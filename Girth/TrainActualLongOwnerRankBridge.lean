import Girth.TrainPairedFinOwnerTransport
import Girth.TrainOneDoubleOwnerCutBound
import Girth.TrainActualLongDesignatedCountDrop
import Girth.TrainDesignatedLabelLexRank
import Mathlib.Tactic

/-!
# Path A: exact admissible owner word and lexicographic descent for an actual long cycle

An earlier finite owner-transport theorem returned an admissible Fin-indexed
owner assignment, but forgot its exact owner-word projection in its CONCLUSION.
Consequently the checked cyclic cut bound could not be applied to that witness.
We retain the second projection of the same paired-word certificate explicitly,
then compose it with physical source-label/descent and minimum owner selection.

All results are conditional on an ACTUAL one-long BigCycle output and the
real physical geometry. This file does not choose the supreme picture piece,
settle mixed short cases, or prove the complete cycle-transfer theorem.
Circulation only. No appendix.
-/

namespace StructuralRamsey.Girth

universe v w
variable {Label : Type v} {Owner : Type w}

/-- Strengthened paired-word extraction: the owner assignment retains
the exact SECOND projection of the paired certificate, not just per-position
admissibility. -/
theorem finOwnerChoice_of_paired_word_exact
    {m : ℕ} (outLabels : Fin m → Label)
    (paired : List (Label × Owner))
    (Allowed : Label → Owner → Prop)
    (hLength : paired.length = m)
    (hLabels : paired.map Prod.fst = List.ofFn outLabels)
    (hAllowed : ∀ z ∈ paired, Allowed z.1 z.2) :
    ∃ newOwner : Fin m → Owner,
      (∀ k : Fin m, Allowed (outLabels k) (newOwner k)) ∧
      List.ofFn newOwner = paired.map Prod.snd := by
  let pairAt : Fin m → Label × Owner :=
    fun k => paired.get (Fin.cast hLength.symm k)
  have hPaired : List.ofFn pairAt = paired := by
    calc
      List.ofFn pairAt =
          List.ofFn (fun k : Fin m =>
            paired.get (Fin.cast hLength.symm k)) := rfl
      _ = List.ofFn (List.get paired) :=
            (List.ofFn_congr hLength (List.get paired)).symm
      _ = paired := List.ofFn_get paired
  have hLabelList :
      List.ofFn (fun k : Fin m => (pairAt k).1) =
        List.ofFn outLabels := by
    calc
      List.ofFn (fun k : Fin m => (pairAt k).1) =
          (List.ofFn pairAt).map Prod.fst := by
            simp [List.map_ofFn] <;> (funext k; rfl)
      _ = paired.map Prod.fst :=
            congrArg (List.map Prod.fst) hPaired
      _ = List.ofFn outLabels := hLabels
  have hLabelAt :
      ∀ k : Fin m, (pairAt k).1 = outLabels k :=
    fun k => congrFun (List.ofFn_inj.mp hLabelList) k
  refine ⟨fun k => (pairAt k).2, ?_, ?_⟩
  · intro k
    have hkMem : pairAt k ∈ paired := by
      rw [← hPaired]
      exact List.mem_ofFn.mpr ⟨k, rfl⟩
    have h := hAllowed (pairAt k) hkMem
    change Allowed (outLabels k) (pairAt k).2
    rw [← hLabelAt k]
    exact h
  · calc
      List.ofFn (fun k : Fin m => (pairAt k).2) =
          (List.ofFn pairAt).map Prod.snd := by
            simp [List.map_ofFn] <;> (funext k; rfl)
      _ = paired.map Prod.snd :=
            congrArg (List.map Prod.snd) hPaired

/-- The actual expanded Fin owner word is exactly the one-double
source owner word, and all its labels are admissibly owned. -/
theorem oneDoubleWord_fin_owner_exact
    {n m : ℕ} (labels : Fin n → Label)
    (oldOwner : Fin n → Owner)
    (j : Fin n) (first second : Label) (target : Owner)
    (outLabels : Fin m → Label)
    (Allowed : Label → Owner → Prop)
    (hOld : ∀ k : Fin n, Allowed (labels k) (oldOwner k))
    (hFirst : Allowed first target)
    (hSecond : Allowed second target)
    (hWord : List.ofFn outLabels =
      oneDoubleWord labels j first second) :
    ∃ newOwner : Fin m → Owner,
      (∀ k : Fin m, Allowed (outLabels k) (newOwner k)) ∧
      List.ofFn newOwner =
        oneDoubleWord oldOwner j target target := by
  let paired := oneDoublePairedWord
    labels oldOwner j first second target
  have hLabelProjection :
      paired.map Prod.fst = List.ofFn outLabels :=
    (oneDoublePairedWord_label_projection
      labels oldOwner j first second target).trans hWord.symm
  have hLength : paired.length = m := by
    have hP := congrArg List.length hLabelProjection
    simp only [List.length_map, List.length_ofFn] at hP
    exact hP
  have hAdmissible : ∀ z ∈ paired, Allowed z.1 z.2 :=
    oneDoublePairedWord_admissible labels oldOwner j
      first second target Allowed hOld hFirst hSecond
  obtain ⟨newOwner, hNewAllowed, hOwnerProjection⟩ :=
    finOwnerChoice_of_paired_word_exact
      outLabels paired Allowed hLength hLabelProjection hAdmissible
  refine ⟨newOwner, hNewAllowed, ?_⟩
  exact hOwnerProjection.trans
    (oneDoublePairedWord_owner_projection
      labels oldOwner j first second target)

/-- Close the formal gap between per-occurrence owner admissibility and
the exact cyclic Finset cut inequality for an isolated long replacement. -/
theorem oneDoubleWord_fin_owner_cut_bound
    [DecidableEq Owner]
    {n m : ℕ} (hn : 2 ≤ n) (labels : Fin n → Label)
    (oldOwner : Fin n → Owner)
    (j : Fin n) (first second : Label) (target : Owner)
    (outLabels : Fin m → Label)
    (Allowed : Label → Owner → Prop)
    (hOld : ∀ k : Fin n, Allowed (labels k) (oldOwner k))
    (hFirst : Allowed first target)
    (hSecond : Allowed second target)
    (hWord : List.ofFn outLabels =
      oneDoubleWord labels j first second)
    (hPrev : oldOwner (trainCyclicPred j) ≠ oldOwner j)
    (hNext : oldOwner j ≠ oldOwner (cyclicSucc j)) :
    ∃ newOwner : Fin m → Owner,
      (∀ k : Fin m, Allowed (outLabels k) (newOwner k)) ∧
      List.ofFn newOwner =
        oneDoubleWord oldOwner j target target ∧
      cyclicOwnerChanges newOwner ≤ cyclicOwnerChanges oldOwner := by
  obtain ⟨newOwner, hNewAllowed, hOwnerWord⟩ :=
    oneDoubleWord_fin_owner_exact labels oldOwner
      j first second target outLabels Allowed
      hOld hFirst hSecond hWord
  refine ⟨newOwner, hNewAllowed, hOwnerWord, ?_⟩
  exact cyclicOwnerChanges_long_output_le
    hn oldOwner newOwner j target hPrev hNext hOwnerWord

end StructuralRamsey.Girth

namespace StructuralRamsey.Girth.OrderOneData

universe v w
variable {V E I P : Type v} {Owner : Type w}
variable [DecidableEq Owner] (D : OrderOneData V E I P)

/-- For an ACTUAL one-fresh-physical-long output, the finite owner
certificate is simultaneously admissible, cut-nonincreasing, and
strictly lexicographically descending in the genuine designated count.
No assumption that the receiving standard neighbours the source. -/
theorem BigCycle.oneFreshPhysicalLong_owner_rank_of_isolated
    {n m : ℕ} (K : D.BigCycle n) (H : D.BigCycle m)
    (hn : 2 ≤ n) (j : Fin n)
    (first : E) (wagon : P) (second : E)
    (oldOwner : Fin n → Owner) (target : Owner)
    (Allowed : (I ⊕ E) → Owner → Prop)
    (hOld : ∀ k : Fin n, Allowed (K.label k) (oldOwner k))
    (hFirst : Allowed (Sum.inr first) target)
    (hSecond : Allowed (Sum.inr second) target)
    (hPrev : oldOwner (trainCyclicPred j) ≠ oldOwner j)
    (hNext : oldOwner j ≠ oldOwner (cyclicSucc j))
    (hPhysical : K.PhysicalLongGeometry D j first wagon second)
    (hWord : List.ofFn (fun k : Fin m =>
      (H.label k, H.connector k)) =
      K.resultWord D (K.onlyLongPieces D j first wagon second)) :
    ∃ newOwner : Fin m → Owner,
      (∀ k : Fin m, Allowed (H.label k) (newOwner k)) ∧
      List.ofFn newOwner =
        oneDoubleWord oldOwner j target target ∧
      cyclicOwnerChanges newOwner ≤ cyclicOwnerChanges oldOwner ∧
      H.designatedOccurrenceCount D + 1 =
        K.designatedOccurrenceCount D ∧
      Prod.Lex (· < ·) (· < ·)
        (cyclicOwnerChanges newOwner, H.designatedOccurrenceCount D)
        (cyclicOwnerChanges oldOwner, K.designatedOccurrenceCount D) := by
  have hOutLabels : List.ofFn H.label =
      oneDoubleWord K.label j (Sum.inr first) (Sum.inr second) := by
    calc
      List.ofFn H.label =
          (List.ofFn (fun k : Fin m =>
            (H.label k, H.connector k))).map Prod.fst := by
              simp [List.map_ofFn] <;> (funext k; rfl)
      _ = (K.resultWord D
          (K.onlyLongPieces D j first wagon second)).map Prod.fst :=
            congrArg (List.map Prod.fst) hWord
      _ = oneDoubleWord K.label j
          (Sum.inr first) (Sum.inr second) :=
            K.onlyLong_resultWord_label_projection
              D j first wagon second
  obtain ⟨newOwner, hNewAllowed, hOwnerWord, hCuts⟩ :=
    oneDoubleWord_fin_owner_cut_bound
      hn K.label oldOwner j (Sum.inr first) (Sum.inr second)
      target H.label Allowed hOld hFirst hSecond
      hOutLabels hPrev hNext
  have hDrop :
      H.designatedOccurrenceCount D + 1 =
        K.designatedOccurrenceCount D :=
    K.oneFreshPhysicalLong_designatedCount_drop D H
      j first wagon second hPhysical hWord
  have hStrict :
      H.designatedOccurrenceCount D <
        K.designatedOccurrenceCount D := by
    omega
  exact ⟨newOwner, hNewAllowed, hOwnerWord, hCuts, hDrop,
    natCutDesignatedLex_drop hCuts hStrict⟩

/-- Minimize the admissible owner word on the actual output; the
minimum has rank strictly below the displayed source owner word.
If that source owner was minimal, this gives exactly the paper's
isolated-long rank descent (conditionally on an actual long output). -/
theorem BigCycle.oneFreshPhysicalLong_minimal_rank_of_isolated
    {n m : ℕ} (K : D.BigCycle n) (H : D.BigCycle m)
    (hn : 2 ≤ n) (j : Fin n)
    (first : E) (wagon : P) (second : E)
    (oldOwner : Fin n → Owner) (target : Owner)
    (Allowed : (I ⊕ E) → Owner → Prop)
    (hOld : ∀ k : Fin n, Allowed (K.label k) (oldOwner k))
    (hFirst : Allowed (Sum.inr first) target)
    (hSecond : Allowed (Sum.inr second) target)
    (hPrev : oldOwner (trainCyclicPred j) ≠ oldOwner j)
    (hNext : oldOwner j ≠ oldOwner (cyclicSucc j))
    (hPhysical : K.PhysicalLongGeometry D j first wagon second)
    (hWord : List.ofFn (fun k : Fin m =>
      (H.label k, H.connector k)) =
      K.resultWord D (K.onlyLongPieces D j first wagon second)) :
    ∃ minimumOwner : Fin m → Owner,
      (∀ k : Fin m, Allowed (H.label k) (minimumOwner k)) ∧
      (∀ other : Fin m → Owner,
        (∀ k : Fin m, Allowed (H.label k) (other k)) →
        cyclicOwnerChanges minimumOwner ≤ cyclicOwnerChanges other) ∧
      Prod.Lex (· < ·) (· < ·)
        (cyclicOwnerChanges minimumOwner, H.designatedOccurrenceCount D)
        (cyclicOwnerChanges oldOwner, K.designatedOccurrenceCount D) := by
  obtain ⟨outOwner, hOutAllowed, _, hCuts, hDrop, _⟩ :=
    K.oneFreshPhysicalLong_owner_rank_of_isolated D H hn j
      first wagon second oldOwner target Allowed
      hOld hFirst hSecond hPrev hNext hPhysical hWord
  obtain ⟨minimumOwner, hMinAllowed, hMin⟩ :=
    exists_minimal_cyclic_owner
      (fun k owner => Allowed (H.label k) owner)
      (fun k => ⟨outOwner k, hOutAllowed k⟩)
  have hStrict :
      H.designatedOccurrenceCount D <
        K.designatedOccurrenceCount D := by
    omega
  refine ⟨minimumOwner, hMinAllowed, hMin, ?_⟩
  exact natCutDesignatedLex_drop
    ((hMin outOwner hOutAllowed).trans hCuts) hStrict

end StructuralRamsey.Girth.OrderOneData
