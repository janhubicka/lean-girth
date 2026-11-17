import Girth.TrainUniversalTopTwoCycleSupreme
import Girth.TrainShortOnlyPlanGlobal
import Mathlib.Tactic

set_option autoImplicit false
set_option Elab.async false

/-!
# A mixed three-occurrence top cycle is globally supreme

If the original BigCycle has one wagon connector and two vertex
connectors, the middle occurrence between the two vertices must
be designated: A2 prohibits an ambient edge joining those two
vertices in the common universal wagon.

Every vertex of a designated support is in an owned A-edge. At
the universal top those two owned edges meet the same wagon, so
they provide simultaneous SHORT replacements for both other
occurrences. The checked all-short plan theorem supplies a
globally legal resulting cycle.

Only the structure of a top-parent pretrain, selected support
coverage and the actual (A2) axiom of the source are used. No
local full-system-girth or Ramsey bound is assumed.

The separate numerical lemma that every acceptable top cycle
of order <=2 and length 3 has the specified connector pattern
is the remaining finite classification needed to finish a top
FullSystemGirthGT 2 theorem.
-/

namespace StructuralRamsey.Girth.OrderOneData

universe v
variable {V E I P : Type v} (D : OrderOneData V E I P)

/-- Every point of ANY literal label is covered by an edge owned by
that label, provided all designated-copy vertices are A-supported. -/
theorem label_vertex_supported
    (hCover : ∀ i : I, ∀ x ∈ D.copyCarrier i,
      ∃ e : E, e ∈ D.copyEdges i ∧ x ∈ D.edgeCarrier e)
    (a : I ⊕ E) (x : V) (hx : x ∈ D.carrier a) :
    ∃ e : E, e ∈ D.edges a ∧ x ∈ D.edgeCarrier e := by
  cases a with
  | inl i =>
      exact hCover i x hx
  | inr e =>
      exact ⟨e, rfl, hx⟩

/-- A real top wagon contains every vertex of every label incident
with a nonempty physical edge, since all edges have the same parent. -/
theorem wagonVertex_of_constant_parent_of_label_vertex
    (hConst : ∀ e f : E, D.parent e = D.parent f)
    (hCover : ∀ i : I, ∀ x ∈ D.copyCarrier i,
      ∃ e : E, e ∈ D.copyEdges i ∧ x ∈ D.edgeCarrier e)
    (a : I ⊕ E) (x : V) (p : P)
    (hx : x ∈ D.carrier a)
    (hp : D.Meets a p) :
    D.WagonVertex p x := by
  obtain ⟨e, _he, hxe⟩ :=
    D.label_vertex_supported hCover a x hx
  obtain ⟨f, _hf, hfp⟩ := hp
  exact ⟨e, (hConst e f).trans hfp, hxe⟩

/-- A three-cycle whose connector word has a single universal
wagon and the two neighbouring vertex connectors admits a
globally legal supreme ORIGINAL designated label. The target
is precisely the occurrence between those two vertex connectors. -/
theorem BigCycle.three_top_supreme_of_one_wagon
    (Z : D.BigCycle 3) (hAccept : Z.Acceptable)
    (hConst : ∀ e f : E, D.parent e = D.parent f)
    (hCover : ∀ i : I, ∀ x ∈ D.copyCarrier i,
      ∃ e : E, e ∈ D.copyEdges i ∧ x ∈ D.edgeCarrier e)
    (w : Fin 3) (p : P) (x y : V)
    (hW : Z.connector w = Sum.inr p)
    (hPrev : Z.connector (trainCyclicPred w) = Sum.inl x)
    (hNext : Z.connector (cyclicSucc w) = Sum.inl y) :
    Z.HasSimultaneousSupreme := by
  have hPredSucc : trainCyclicPred (cyclicSucc w) = w :=
    trainCyclicPred_cyclicSucc_of_two_le (by decide : 2 ≤ 3) w
  have hSuccSucc : cyclicSucc (cyclicSucc w) =
      trainCyclicPred w := by
    fin_cases w <;> decide
  have hPredNeSucc :
      trainCyclicPred w ≠ cyclicSucc w := by
    fin_cases w <;> decide
  have hTargetX :
      x ∈ D.carrier (Z.label (trainCyclicPred w)) := by
    have h := Z.left_incident (trainCyclicPred w)
    rw [hPrev] at h
    exact h
  have hTargetY :
      y ∈ D.carrier (Z.label (trainCyclicPred w)) := by
    have h := Z.right_incident (cyclicSucc w)
    rw [hSuccSucc, hNext] at h
    exact h
  have hWagonMeet : D.Meets (Z.label w) p := by
    have h := Z.left_incident w
    rw [hW] at h
    exact h
  obtain ⟨f, _hf, hfp⟩ := hWagonMeet
  have hAllParents (e : E) : D.parent e = p :=
    (hConst e f).trans hfp
  have hWagonX : D.WagonVertex p x := by
    obtain ⟨e, _he, hxe⟩ :=
      D.label_vertex_supported hCover
        (Z.label (trainCyclicPred w)) x hTargetX
    exact ⟨e, hAllParents e, hxe⟩
  have hWagonY : D.WagonVertex p y := by
    obtain ⟨e, _he, hye⟩ :=
      D.label_vertex_supported hCover
        (Z.label (trainCyclicPred w)) y hTargetY
    exact ⟨e, hAllParents e, hye⟩
  have hNoPair : ¬ D.PairEdge x y :=
    hAccept.2.1.2 w p x y
      hW hPrev hNext hPredNeSucc hWagonX hWagonY
  have hDesignated :
      D.designated (Z.label (trainCyclicPred w)) := by
    cases hLabel : Z.label (trainCyclicPred w) with
    | inl i =>
        trivial
    | inr edge =>
        have hxe : x ∈ D.edgeCarrier edge := by
          rw [hLabel] at hTargetX
          exact hTargetX
        have hye : y ∈ D.edgeCarrier edge := by
          rw [hLabel] at hTargetY
          exact hTargetY
        exact False.elim (hNoPair ⟨edge, hxe, hye⟩)
  obtain ⟨edgeX, hOwnX, hxe⟩ :=
    D.label_vertex_supported hCover
      (Z.label (trainCyclicPred w)) x hTargetX
  obtain ⟨edgeY, hOwnY, hye⟩ :=
    D.label_vertex_supported hCover
      (Z.label (trainCyclicPred w)) y hTargetY
  have hPositions (j : Fin 3) :
      j = trainCyclicPred w ∨ j = w ∨ j = cyclicSucc w := by
    fin_cases w <;> fin_cases j <;> decide
  apply Z.hasSimultaneousSupreme_of_all_shortValid D
    hAccept (trainCyclicPred w) hDesignated
  intro j hDifferent
  rcases hPositions j with hTarget | hHere | hAfter
  · subst j
    exact (hDifferent rfl).elim
  · subst j
    refine ⟨edgeX, hOwnX, ?_, ?_⟩
    · rw [hPrev]
      exact hxe
    · rw [hW]
      exact ⟨edgeX, rfl, hAllParents edgeX⟩
  · subst j
    refine ⟨edgeY, hOwnY, ?_, ?_⟩
    · rw [hPredSucc, hW]
      exact ⟨edgeY, rfl, hAllParents edgeY⟩
    · rw [hNext]
      exact hye

end StructuralRamsey.Girth.OrderOneData
