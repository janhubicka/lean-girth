import Girth.ForestPreBirthSplit
import SuccessorTree.FreeAncestralGapMap
import Mathlib.Tactic

/-!
# The pre-birth split fixes the old front outside its private cone

The two one-gap maps used to duplicate a moving carrier differ only at
one source history u at level m.  At every node which is *not* above u,
the two global one-gap maps agree.  Combined with the previously proved
private-cone separation, this gives the exact syntactic old-front
agreement required by the corrected two-copy test.

No geometric evaluation of actual A/B carriers is assumed.
-/

namespace StructuralRamsey.Girth

open SuccessorTree
open SuccessorTree.FreeAncestral

universe u
variable {Label : Type u} {arity : ℕ}
variable [Fintype Label] [Nonempty Label]

/-- Dependent child congruence, used when the mapped base changes
but the two ancestral parameter level lists coincide. -/
private theorem child_eq_of_base_and_levels
    (a b : Node Label arity)
    (t : ParamTuple arity a.level)
    (u : ParamTuple arity b.level)
    (label : Label)
    (hab : a = b)
    (ht : levelList t = levelList u) :
    child a t label = child b u label := by
  cases hab
  have htu : t = u := levelList_injective ht
  rw [htu]

theorem preBirthOne_at_other_gap
    (m : ℕ) (h0 h : History Label arity m)
    (c0 c1 : Label) (hne : h ≠ h0) :
    preBirthOne (arity := arity) m h0 c0 c1
        (⟨m, h⟩ : Node Label arity) =
      child (⟨m, h⟩ : Node Label arity)
        (emptyParamTuple arity m) c0 := by
  classical
  simp [preBirthOne, oneGapShapeMap_apply, gapNode_at_level,
    if_neg hne]

/-- Both global one-gap maps agree outside the upward cone of the one
node where their chosen inserted labels differ. -/
theorem preBirth_maps_agree_outside_cone
    (m : ℕ) (hmpos : 0 < m)
    (h0 : History Label arity m) (c0 c1 : Label)
    {x : Node Label arity}
    (hx : ¬ (⟨m, h0⟩ : Node Label arity) ≤ x) :
    preBirthZero (arity := arity) m c0 x =
      preBirthOne (arity := arity) m h0 c0 c1 x := by
  classical
  rcases x with ⟨n, h⟩
  induction n with
  | zero =>
      exact preBirth_maps_agree_below_gap
        m h0 c0 c1 (⟨0, h⟩ : Node Label arity) hmpos
  | succ n ih =>
      by_cases hlt : n + 1 < m
      · exact preBirth_maps_agree_below_gap
          m h0 c0 c1
          (⟨n + 1, h⟩ : Node Label arity) hlt
      · by_cases heq : n + 1 = m
        · subst m
          have hne : h ≠ h0 := by
            intro he
            subst h
            exact hx le_rfl
          rw [preBirthZero_at_gap (arity := arity) (n + 1) h c0,
              preBirthOne_at_other_gap (arity := arity)
                (n + 1) h0 h c0 c1 hne]
        · have hge : m ≤ n := by omega
          cases h with
          | step p code =>
              let a : Node Label arity := ⟨n, p⟩
              have hchild :
                  a ≤
                    (⟨n + 1, History.step p code⟩ :
                      Node Label arity) :=
                base_le_child a code.params code.label
              have hparent :
                  ¬ (⟨m, h0⟩ : Node Label arity) ≤ a := by
                intro hle
                exact hx (hle.trans hchild)
              have heqParent :=
                ih p hparent
              change
                gapNode m
                  (fun _ => ⟨c0, emptyParamTuple arity m⟩)
                    (child a code.params code.label) =
                  gapNode m
                    (fun q : History Label arity m =>
                      if q = h0 then
                        ⟨c1, emptyParamTuple arity m⟩
                      else
                        ⟨c0, emptyParamTuple arity m⟩)
                    (child a code.params code.label)
              rw [gapNode_child_of_ge m
                    (fun _ => ⟨c0, emptyParamTuple arity m⟩)
                    a code.params code.label hge,
                  gapNode_child_of_ge m
                    (fun q : History Label arity m =>
                      if q = h0 then
                        ⟨c1, emptyParamTuple arity m⟩
                      else
                        ⟨c0, emptyParamTuple arity m⟩)
                    a code.params code.label hge]
              change
                child (preBirthZero (arity := arity) m c0 a)
                    (gapShiftParamTuple m
                      (fun _ => ⟨c0, emptyParamTuple arity m⟩)
                      a code.params hge) code.label =
                child (preBirthOne (arity := arity) m h0 c0 c1 a)
                    (gapShiftParamTuple m
                      (fun q : History Label arity m =>
                        if q = h0 then
                          ⟨c1, emptyParamTuple arity m⟩
                        else
                          ⟨c0, emptyParamTuple arity m⟩)
                      a code.params hge) code.label
              apply child_eq_of_base_and_levels
              · exact heqParent
              · rfl

/-- Any finite old front disjoint from the private cone remains
pointwise identical under the two test embeddings. -/
theorem preBirth_maps_agree_on_frozen_front
    (m : ℕ) (hmpos : 0 < m)
    (h0 : History Label arity m) (c0 c1 : Label)
    (K : Set (Node Label arity))
    (hPrivate : ∀ x ∈ K,
       ¬ (⟨m, h0⟩ : Node Label arity) ≤ x) :
    ∀ x ∈ K,
      preBirthZero (arity := arity) m c0 x =
        preBirthOne (arity := arity) m h0 c0 c1 x := by
  intro x hx
  exact preBirth_maps_agree_outside_cone
    m hmpos h0 c0 c1 (hPrivate x hx)

/-- A predecessor-closed old front avoids every private cone whose
origin u is not itself in the front.  Thus the test maps really agree
on the complete old front, not only on the levels below u. -/
theorem preBirth_maps_agree_on_predClosed_front
    (m : ℕ) (hmpos : 0 < m)
    (h0 : History Label arity m) (c0 c1 : Label)
    (K : Set (Node Label arity))
    (hClosed :
      ∀ ⦃x y : Node Label arity⦄,
        x ≤ y → y ∈ K → x ∈ K)
    (hu : (⟨m, h0⟩ : Node Label arity) ∉ K) :
    ∀ x ∈ K,
      preBirthZero (arity := arity) m c0 x =
        preBirthOne (arity := arity) m h0 c0 c1 x := by
  apply preBirth_maps_agree_on_frozen_front
    m hmpos h0 c0 c1 K
  intro x hx hux
  exact hu (hClosed hux hx)

/-- Complete *syntactic* two-copy configuration: the frozen
predecessor-closed front is common after any further shape map, while
the moving carrier's intrinsic birth events remain distinct.
This does not assert that those events evaluate to different
physical A-edges or B-copies. -/
theorem preBirth_twoCopy_syntax
    (m : ℕ) (hmpos : 0 < m)
    (h0 : History Label arity m)
    (c0 c1 : Label) (hne : c0 ≠ c1)
    (K : Set (Node Label arity))
    (hClosed :
      ∀ ⦃x y : Node Label arity⦄,
        x ≤ y → y ∈ K → x ∈ K)
    (hu : (⟨m, h0⟩ : Node Label arity) ∉ K)
    (e : IntrinsicEvent
      (freeSTree (Label := Label) (arity := arity)))
    (he : (⟨m, h0⟩ : Node Label arity) ≤ e.base)
    (W : ShapeMap
      (freeSTree (Label := Label) (arity := arity))) :
    (∀ x ∈ K,
      W (preBirthZero (arity := arity) m c0 x) =
        W (preBirthOne (arity := arity) m h0 c0 c1 x)) ∧
      W.mapEvent
          ((preBirthZero (arity := arity) m c0).mapEvent e) ≠
        W.mapEvent
          ((preBirthOne (arity := arity) m h0 c0 c1).mapEvent e) := by
  constructor
  · intro x hx
    exact congrArg W
      (preBirth_maps_agree_on_predClosed_front
        m hmpos h0 c0 c1 K hClosed hu x hx)
  · exact preBirthSplit_event_ne_after
      m h0 c0 c1 hne e he W

/-- Exact bridge from syntactic two-copy separation to geometric
carrier distinctness: it is enough for the evaluated carrier-origin
map to be injective on intrinsic events. This is a CONDITION on the
geometric model, not a proof that such a model exists. -/
theorem preBirth_twoCopy_of_faithfulOrigins
    (Atom : Type*)
    (origin : IntrinsicEvent
      (freeSTree (Label := Label) (arity := arity)) → Atom)
    (hOrigin : Function.Injective origin)
    (m : ℕ) (hmpos : 0 < m)
    (h0 : History Label arity m)
    (c0 c1 : Label) (hne : c0 ≠ c1)
    (K : Set (Node Label arity))
    (hClosed :
      ∀ ⦃x y : Node Label arity⦄,
        x ≤ y → y ∈ K → x ∈ K)
    (hu : (⟨m, h0⟩ : Node Label arity) ∉ K)
    (e : IntrinsicEvent
      (freeSTree (Label := Label) (arity := arity)))
    (he : (⟨m, h0⟩ : Node Label arity) ≤ e.base)
    (W : ShapeMap
      (freeSTree (Label := Label) (arity := arity))) :
    (∀ x ∈ K,
      W (preBirthZero (arity := arity) m c0 x) =
        W (preBirthOne (arity := arity) m h0 c0 c1 x)) ∧
      origin
        (W.mapEvent
          ((preBirthZero (arity := arity) m c0).mapEvent e)) ≠
      origin
        (W.mapEvent
          ((preBirthOne (arity := arity) m h0 c0 c1).mapEvent e)) := by
  obtain ⟨hFront, hEvents⟩ :=
    preBirth_twoCopy_syntax
      m hmpos h0 c0 c1 hne K hClosed hu e he W
  refine ⟨hFront, ?_⟩
  intro heq
  exact hEvents (hOrigin heq)

end StructuralRamsey.Girth
