import Girth.ForestLocalNeutralTail
import SuccessorTree.FreeAncestralLevelTree
import Mathlib.Tactic

/-!
# Meeting-level guard for simultaneous neutral successor-gap compression

The common-code consistency required by the existing one-gap map is not
an independent assumption for a deleted level outside the marked meet
skeleton. If two selected target histories have the same prefix below
the deleted level but prescribe different successor codes there, their
greatest common prefix is *exactly* that deleted level.

Thus for a finite family of locally neutral histories, excluding all
relevant pairwise meet levels automatically supplies consistency and
produces ONE global free-ancestral shape map deleting that gap.

This verifies the syntactic meet/choice step of guarded diary
normalization. It does not show that actual train support/owner
histories have neutral code tails outside the bounded skeleton.
-/

namespace StructuralRamsey.Girth

open SuccessorTree
open SuccessorTree.FreeAncestral

universe u

/-- The inserted transition is a genuine prefix of the complete
locally checked target history. -/
theorem LocalNeutralGapTail.insertedPrefix
    {Label : Type u} {arity m k : ℕ}
    {stem : History Label arity m}
    {code : Code Label arity m}
    {h : History Label arity (m + k + 1)}
    (ht : LocalNeutralGapTail m stem code k h) :
    Prefix (History.step stem code) h := by
  induction ht with
  | base =>
      exact Prefix.refl _
  | step hprev later hAvoid ih =>
      exact Prefix.step ih later

/-- Two locally checked target histories with a common prefix through
the inserted transition necessarily specify the same insertion code. -/
theorem LocalNeutralGapTail.code_eq_of_commonNextPrefix
    {Label : Type u} {arity m k : ℕ}
    {stem stem' : History Label arity m}
    {code code' : Code Label arity m}
    {h h' : History Label arity (m + k + 1)}
    (ht : LocalNeutralGapTail m stem code k h)
    (ht' : LocalNeutralGapTail m stem' code' k h')
    (hCommon : ∃ p : History Label arity (m + 1),
      Prefix p h ∧ Prefix p h') :
    code = code' := by
  obtain ⟨p, hp, hp'⟩ := hCommon
  have hEq : History.step stem code = p := by
    rcases Prefix.comparable ht.insertedPrefix hp with hle | hge
    · exact eq_of_heq (Prefix.heq_of_level_eq hle rfl)
    · exact (eq_of_heq (Prefix.heq_of_level_eq hge rfl)).symm
  have hEq' : History.step stem' code' = p := by
    rcases Prefix.comparable ht'.insertedPrefix hp' with hle | hge
    · exact eq_of_heq (Prefix.heq_of_level_eq hle rfl)
    · exact (eq_of_heq (Prefix.heq_of_level_eq hge rfl)).symm
  have hSame : History.step stem code = History.step stem' code' :=
    hEq.trans hEq'.symm
  have hc := congrArg (lastCode (n := m)) hSame
  simpa using hc

/-- If two marked histories share a common predecessor above level m,
then the codes inserted at level m coincide. The meet level is measured
in the actual free-ancestral LevelTree, not by an unverified symbolic
dependency graph. -/
theorem LocalNeutralGapTail.code_eq_of_meetAbove
    {Label : Type u} {arity m k : ℕ}
    {stem stem' : History Label arity m}
    {code code' : Code Label arity m}
    {h h' : History Label arity (m + k + 1)}
    (ht : LocalNeutralGapTail m stem code k h)
    (ht' : LocalNeutralGapTail m stem' code' k h')
    (hAbove : m <
      (meetNode
        (⟨m + k + 1, h⟩ : Node Label arity)
        (⟨m + k + 1, h'⟩ : Node Label arity)).level) :
    code = code' := by
  let x : Node Label arity := ⟨m + k + 1, h⟩
  let y : Node Label arity := ⟨m + k + 1, h'⟩
  let z : Node Label arity := meetNode x y
  have hDepth : m + 1 ≤ z.level := by
    change m + 1 ≤ (meetNode x y).level
    exact Nat.succ_le_of_lt hAbove
  obtain ⟨p, hp⟩ :=
    Prefix.exists_at_level z.2 (m + 1) hDepth
  have hpX : Prefix p h :=
    Prefix.trans hp (meetNode_le_left x y)
  have hpY : Prefix p h' :=
    Prefix.trans hp (meetNode_le_right x y)
  exact ht.code_eq_of_commonNextPrefix ht' ⟨p, hpX, hpY⟩

/-- The finite family of locally checked histories needs no
separate code-coherence axiom when level m is excluded from the
pairwise meet skeleton of histories sharing the level-m stem. -/
theorem finiteLocalNeutralGap_preimages_of_unmarkedMeets
    {Label : Type u} {arity : ℕ}
    [Fintype Label] [Nonempty Label]
    (m k q : ℕ)
    (stem : Fin q → History Label arity m)
    (code : Fin q → Code Label arity m)
    (target : Fin q → History Label arity (m + k + 1))
    (hLocal : ∀ i : Fin q,
      LocalNeutralGapTail m (stem i) (code i) k (target i))
    (hUnmarkedMeet : ∀ i j : Fin q, stem i = stem j →
      (meetNode
        (⟨m + k + 1, target i⟩ : Node Label arity)
        (⟨m + k + 1, target j⟩ : Node Label arity)).level ≠ m) :
    ∃ choose : History Label arity m → Code Label arity m,
      ∃ source : Fin q → History Label arity (m + k),
        ∀ i : Fin q,
          gapNode m choose
            (⟨m + k, source i⟩ : Node Label arity) =
            (⟨m + k + 1, target i⟩ : Node Label arity) := by
  have hConsistent (i j : Fin q) (hs : stem i = stem j) :
      code i = code j := by
    let x : Node Label arity := ⟨m + k + 1, target i⟩
    let y : Node Label arity := ⟨m + k + 1, target j⟩
    have hi : (⟨m, stem i⟩ : Node Label arity) ≤ x := by
      change Prefix (stem i) (target i)
      exact Prefix.trans
        (Prefix.step (Prefix.refl _) (code i))
        (hLocal i).insertedPrefix
    have hj0 : Prefix (stem j) (target j) :=
      Prefix.trans
        (Prefix.step (Prefix.refl _) (code j))
        (hLocal j).insertedPrefix
    have hj : (⟨m, stem i⟩ : Node Label arity) ≤ y := by
      change Prefix (stem i) (target j)
      simpa [hs] using hj0
    have hMeetLe : m ≤ (meetNode x y).level :=
      node_level_le (le_meetNode hi hj)
    have hMeetAbove : m < (meetNode x y).level := by
      have hn := hUnmarkedMeet i j hs
      exact lt_of_le_of_ne hMeetLe (Ne.symm hn)
    exact (hLocal i).code_eq_of_meetAbove (hLocal j) hMeetAbove
  exact finiteLocalNeutralGap_preimages
    m k q stem code target hLocal hConsistent

end StructuralRamsey.Girth
