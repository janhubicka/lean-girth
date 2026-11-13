import Girth.TrainRecursiveRefinementDoubleStep
import Girth.TrainRecursiveRefinementGlobalCutGirth

set_option autoImplicit false
set_option Elab.async false

/-!
# Track 6: iterated first-wagon refinement and retained first-cut cap

UNCHECKED LEAN CANDIDATE.  The proof follows the already existing
`FirstWagonRefinement.false_of_short_labelledCycle_in_firstWagon`
descent but uses the conditional two-preimage one-step theorem at the
stronger `2*g+1` cutoff.  All physical labels and proper old cuts are
retained.  No external Ramsey witness is constructed by this module.

A nonempty tail contributes its own original first cutoff `h`.
The exact global bound is `min (2*g+1) h`.  With an empty tail, the
original first relation is universal and the bound is `2*g+1`.
-/

namespace StructuralRamsey.Girth

universe u v
variable {E W P : Type v}

namespace FirstWagonRefinement

variable {m : ℕ} {T : EdgeTrainLevels E m} {hm : 0 < m}
variable {edge : E → Set W} {part : W → P}
variable {firstAllowed : Set P} {g : ℕ}

/-- The original first wagon contains no labelled edge cycle of length
at most `2*g+1`. Descend through each actual inserted first cut;
a bottom equality class cannot contain two distinct cycle edge labels. -/
theorem false_of_short_labelledCycle_in_firstWagon_twice
    (R : FirstWagonRefinement T hm edge part firstAllowed g)
    (hg : 2 ≤ g) (hEdgePart : ∀ e : E, Set.InjOn part (edge e))
    (C : LabelledBergeCycle edge) (hLength : C.length ≤ 2 * g + 1)
    (hFirst : ∀ i j : Fin C.length,
      T.rel ⟨1, by omega⟩ (C.label i) (C.label j)) : False := by
  classical
  let zero : Fin C.length := ⟨0, by have := C.hlength; omega⟩
  have hDescend : ∀ (k : ℕ) (hk : k ≤ R.extraCuts + 1),
      (∀ i j : Fin C.length,
        R.train.rel ⟨k, by omega⟩ (C.label i) (C.label j)) → False := by
    intro k
    induction k with
    | zero =>
        intro hk hRel
        let one : Fin C.length := ⟨1, by have := C.hlength; omega⟩
        have hLabel : C.label zero = C.label one :=
          (R.train.bottom _ _).mp (hRel zero one)
        have hIndex := congrArg Fin.val (C.label_injective hLabel)
        change 0 = 1 at hIndex
        omega
    | succ k ih =>
        intro hk hRel
        let step : Fin (R.extraCuts + 1) := ⟨k, by omega⟩
        let μ := firstRefinementChild m R.extraCuts hm step
        let ν := firstRefinementParent m R.extraCuts hm step
        have hμν : μ ≤ ν := by change k ≤ k + 1; omega
        change ∀ i j : Fin C.length,
          R.train.rel ν (C.label i) (C.label j) at hRel
        let p : Quotient (R.train.wagonSetoid ν) :=
          Quotient.mk _ (C.label zero)
        let Child := {a : Quotient (R.train.wagonSetoid μ) //
          R.train.wagonParent μ ν hμν a = p}
        let child : Fin C.length → Child := fun i =>
          ⟨Quotient.mk _ (C.label i), Quotient.sound (hRel i zero)⟩
        let carrier : Child → Set W :=
          fun a => R.train.wagonClassCarrier edge μ a.val
        have hContained : ∀ i, edge (C.label i) ⊆ carrier (child i) := by
          intro i x hx
          exact ⟨C.label i, (R.train.equivalent μ).refl _, hx⟩
        have hIntersection : ∀ a b : Child, a ≠ b →
            (carrier a ∩ carrier b) ⊆ part ⁻¹' R.permitted step := by
          intro a b hne
          exact R.parameters step (fun h => hne (Subtype.ext h))
            (a.property.trans b.property.symm)
        have hGirth : LabelledGirthGT carrier g := R.childGirth step p
        have hChild := C.child_constant_of_singleton_intersections_twice
          child carrier part (R.permitted step) (R.permitted_subsingleton step)
          (fun i => hEdgePart (C.label i)) hContained hIntersection
          g hg hGirth hLength
        apply ih (by omega)
        intro i j
        exact Quotient.exact (congrArg Subtype.val (hChild i j))
  apply hDescend (R.extraCuts + 1) (Nat.le_refl _)
  intro i j
  have h := (R.oldLevels ⟨1, by omega⟩ Nat.zero_lt_one (C.label i) (C.label j)).mpr
    (hFirst i j)
  simpa only [EdgeTrainLevels.firstRefinementShift, Nat.add_comm] using h

theorem labelledGirthGT_firstWagon_twice
    (R : FirstWagonRefinement T hm edge part firstAllowed g)
    (hg : 2 ≤ g) (hEdgePart : ∀ e : E, Set.InjOn part (edge e)) (a : E) :
    LabelledGirthGT
      (fun e : {e : E // T.rel ⟨1, by omega⟩ a e} => edge e.val)
      (2 * g + 1) := by
  rintro ⟨C, hLength⟩
  let lifted : LabelledBergeCycle edge := {
    length := C.length
    hlength := C.hlength
    label := fun i => (C.label i).val
    vertex := C.vertex
    label_injective := by
      intro i j hij
      exact C.label_injective (Subtype.ext hij)
    vertex_injective := C.vertex_injective
    left_mem := C.left_mem
    right_mem := C.right_mem
  }
  apply R.false_of_short_labelledCycle_in_firstWagon_twice
    hg hEdgePart lifted hLength
  intro i j
  exact (T.equivalent ⟨1, by omega⟩).trans
    ((T.equivalent ⟨1, by omega⟩).symm (C.label i).property)
    (C.label j).property

theorem girthGT_firstWagon_twice
    (R : FirstWagonRefinement T hm edge part firstAllowed g)
    (hg : 2 ≤ g) (hEdgePart : ∀ e : E, Set.InjOn part (edge e)) (a : E) :
    GirthGT {s : Set W | ∃ e : E, T.rel ⟨1, by omega⟩ a e ∧ s = edge e}
      (2 * g + 1) := by
  have h := (R.labelledGirthGT_firstWagon_twice hg hEdgePart a).range_girth
  apply girthGT_of_subset ?_ h
  rintro s ⟨e, he, rfl⟩
  exact ⟨⟨e, he⟩, rfl⟩

/-- Full doubled global bound when the original first wagon is universal. -/
theorem labelledGirthGT_of_first_universal_twice
    (R : FirstWagonRefinement T hm edge part firstAllowed g)
    (hg : 2 ≤ g) (hEdgePart : ∀ e : E, Set.InjOn part (edge e))
    (hUniversal : ∀ e f : E, T.rel ⟨1, by omega⟩ e f) :
    LabelledGirthGT edge (2 * g + 1) := by
  rintro ⟨C, hLength⟩
  exact R.false_of_short_labelledCycle_in_firstWagon_twice
    hg hEdgePart C hLength (fun i j => hUniversal (C.label i) (C.label j))

theorem girthGT_of_first_universal_twice
    (R : FirstWagonRefinement T hm edge part firstAllowed g)
    (hg : 2 ≤ g) (hEdgePart : ∀ e : E, Set.InjOn part (edge e))
    (hUniversal : ∀ e f : E, T.rel ⟨1, by omega⟩ e f) :
    GirthGT (Set.range edge) (2 * g + 1) :=
  (R.labelledGirthGT_of_first_universal_twice hg hEdgePart hUniversal).range_girth

/-- Exact nonempty-tail bound, without discarding the real first cutoff.
This wraps the pre-existing full-label retained-cut localization. -/
theorem labelledGirthGT_of_retainedFirstCut_twice
    (R : FirstWagonRefinement T hm edge part firstAllowed g)
    (hg : 2 ≤ g) (hEdgePart : ∀ e : E, Set.InjOn part (edge e))
    (h : ℕ) (hh : 2 ≤ h)
    (hFirstCut : LabelledGirthGT
      (T.wagonClassCarrier edge (⟨1, by omega⟩ : Fin (m + 1))) h) :
    LabelledGirthGT edge (min (2 * g + 1) h) := by
  rintro ⟨C, hLength⟩
  have hShortFirst : C.length ≤ h := le_trans hLength (min_le_right _ _)
  have hShortLocal : C.length ≤ 2 * g + 1 := le_trans hLength (min_le_left _ _)
  have hFirst : ∀ i j : Fin C.length,
      T.rel ⟨1, by omega⟩ (C.label i) (C.label j) :=
    T.labelledCycle_rel_constant_of_cutGirth
      edge ⟨1, by omega⟩ h hh hFirstCut C hShortFirst
  exact R.false_of_short_labelledCycle_in_firstWagon_twice
    hg hEdgePart C hShortLocal hFirst

theorem girthGT_of_retainedFirstCut_twice
    (R : FirstWagonRefinement T hm edge part firstAllowed g)
    (hg : 2 ≤ g) (hEdgePart : ∀ e : E, Set.InjOn part (edge e))
    (h : ℕ) (hh : 2 ≤ h)
    (hFirstCut : LabelledGirthGT
      (T.wagonClassCarrier edge (⟨1, by omega⟩ : Fin (m + 1))) h) :
    GirthGT (Set.range edge) (min (2 * g + 1) h) :=
  (R.labelledGirthGT_of_retainedFirstCut_twice hg hEdgePart h hh hFirstCut).range_girth

end FirstWagonRefinement

section Actual
open StructuralRamsey.RelStructure

variable {L : RelLanguage.{u}} {UA X P : Type v}

/-- Discharge edge transversality using the existing actual irreducible
A-support geometry, but keep the complete physical first-cut hypothesis. -/
theorem FirstWagonRefinement.actualSupport_girthGT_of_retainedFirstCut_twice
    (A : RelStructure L UA) (hA : A.Irreducible)
    (C : StructuralRamsey.Partite.System L P X)
    {m : ℕ} {T : EdgeTrainLevels (OldACarrierEdge A C.toRelStructure) m}
    {hm : 0 < m} {allowed : Set P} {g : ℕ}
    (R : FirstWagonRefinement T hm (fun e => e.val) C.part allowed g)
    (hg : 2 ≤ g) (h : ℕ) (hh : 2 ≤ h)
    (hFirstCut : LabelledGirthGT
      (T.wagonClassCarrier (fun e => e.val)
        (⟨1, by omega⟩ : Fin (m + 1))) h) :
    GirthGT (supportCopies A C.toRelStructure) (min (2 * g + 1) h) := by
  have hRange := R.girthGT_of_retainedFirstCut_twice
    hg (actualASupport_part_injOn A hA C) h hh hFirstCut
  apply girthGT_of_subset ?_ hRange
  intro s hs
  exact ⟨⟨s, hs⟩, rfl⟩

end Actual
end StructuralRamsey.Girth

#print axioms StructuralRamsey.Girth.FirstWagonRefinement.girthGT_firstWagon_twice
#print axioms StructuralRamsey.Girth.FirstWagonRefinement.girthGT_of_retainedFirstCut_twice
#print axioms StructuralRamsey.Girth.FirstWagonRefinement.actualSupport_girthGT_of_retainedFirstCut_twice
