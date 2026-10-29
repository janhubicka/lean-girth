import Girth.TrainRecursiveRefinement
import Girth.TrainRecursiveRefinementStepGirth
import PartiteConstruction.Partite.Induced

/-!
# One-unit girth gain inside an actual refined first wagon

At each inserted refinement step, a short physical edge cycle inside one
parent lies in a single child.  Iterating that proved one-level localization
down the actual finite nested train reaches the bottom equality relation,
contradicting distinct edge labels.  Thus each original first wagon has
girth greater than `g + 1` when its complete labelled child cuts have girth
greater than `g`, its sibling intersections use at most one part, and the
part map is injective on each physical edge.

The local conclusion is stated on one original first class.  A separate
global corollary explicitly requires the original first relation to be
universal.  No higher-cut localization or global containment is inferred
from the refinement alone.  For actual irreducible relational A-support,
edge transversality follows from the partite system's relation transversality.
-/

namespace StructuralRamsey.Girth

universe u v
variable {E W P : Type v}

namespace FirstWagonRefinement

variable {m : ℕ} {T : EdgeTrainLevels E m} {hm : 0 < m}
variable {edge : E → Set W} {part : W → P} {firstAllowed : Set P} {g : ℕ}

/-- Successive genuine refinement cuts localize a short labelled edge cycle
to bottom equality.  The cycle must initially lie in one original first
wagon; no claim is made about a cycle crossing different first wagons.
-/
theorem false_of_short_labelledCycle_in_firstWagon
    (R : FirstWagonRefinement T hm edge part firstAllowed g)
    (hg : 2 ≤ g) (hEdgePart : ∀ e : E, Set.InjOn part (edge e))
    (C : LabelledBergeCycle edge) (hLength : C.length ≤ g + 1)
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
        have hChild := C.child_constant_of_singleton_intersections
          child carrier part (R.permitted step) (R.permitted_subsingleton step)
          (fun i => hEdgePart (C.label i)) hContained hIntersection g hg hGirth hLength
        apply ih (by omega)
        intro i j
        exact Quotient.exact (congrArg Subtype.val (hChild i j))
  apply hDescend (R.extraCuts + 1) (Nat.le_refl _)
  intro i j
  have h := (R.oldLevels ⟨1, by omega⟩ Nat.zero_lt_one (C.label i) (C.label j)).mpr
    (hFirst i j)
  simpa only [EdgeTrainLevels.firstRefinementShift, Nat.add_comm] using h

/-- Every original first wagon has labelled physical-edge girth through the
next cutoff.  All original edge labels in that class are retained. -/
theorem labelledGirthGT_firstWagon
    (R : FirstWagonRefinement T hm edge part firstAllowed g)
    (hg : 2 ≤ g) (hEdgePart : ∀ e : E, Set.InjOn part (edge e)) (a : E) :
    LabelledGirthGT
      (fun e : {e : E // T.rel ⟨1, by omega⟩ a e} => edge e.val) (g + 1) := by
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
  apply R.false_of_short_labelledCycle_in_firstWagon hg hEdgePart lifted hLength
  intro i j
  exact (T.equivalent ⟨1, by omega⟩).trans
    ((T.equivalent ⟨1, by omega⟩).symm (C.label i).property) (C.label j).property

/-- The complete physical edge family of one original first wagon has
ordinary Berge girth greater than `g + 1`. -/
theorem girthGT_firstWagon
    (R : FirstWagonRefinement T hm edge part firstAllowed g)
    (hg : 2 ≤ g) (hEdgePart : ∀ e : E, Set.InjOn part (edge e)) (a : E) :
    GirthGT {s : Set W | ∃ e : E, T.rel ⟨1, by omega⟩ a e ∧ s = edge e}
      (g + 1) := by
  have h := (R.labelledGirthGT_firstWagon hg hEdgePart a).range_girth
  apply girthGT_of_subset ?_ h
  rintro s ⟨e, he, rfl⟩
  exact ⟨⟨e, he⟩, rfl⟩

/-- A global labelled girth gain is valid when the original first relation
is genuinely universal.  This containment hypothesis is explicit. -/
theorem labelledGirthGT_of_first_universal
    (R : FirstWagonRefinement T hm edge part firstAllowed g)
    (hg : 2 ≤ g) (hEdgePart : ∀ e : E, Set.InjOn part (edge e))
    (hFirstUniversal : ∀ e f : E, T.rel ⟨1, by omega⟩ e f) :
    LabelledGirthGT edge (g + 1) := by
  rintro ⟨C, hLength⟩
  exact R.false_of_short_labelledCycle_in_firstWagon hg hEdgePart C hLength
    (fun i j => hFirstUniversal (C.label i) (C.label j))

/-- Global ordinary girth follows from the same explicit universal-first
condition; finiteness and nonempty support are not needed for this implication. -/
theorem girthGT_of_first_universal
    (R : FirstWagonRefinement T hm edge part firstAllowed g)
    (hg : 2 ≤ g) (hEdgePart : ∀ e : E, Set.InjOn part (edge e))
    (hFirstUniversal : ∀ e f : E, T.rel ⟨1, by omega⟩ e f) :
    GirthGT (Set.range edge) (g + 1) :=
  (R.labelledGirthGT_of_first_universal hg hEdgePart hFirstUniversal).range_girth

end FirstWagonRefinement

section Actual

open StructuralRamsey.RelStructure

variable {L : RelLanguage.{u}} {UA X : Type v}

/-- Every actual irreducible A-support edge is transversal to the part map.
The System's relation transversality suffices; no assumed edge-level
injectivity, rigidity, finiteness or base homomorphism-embedding is needed. -/
theorem actualASupport_part_injOn
    (A : RelStructure L UA) (hA : A.Irreducible)
    (C : StructuralRamsey.Partite.System L P X)
    (e : OldACarrierEdge A C.toRelStructure) : Set.InjOn C.part e.val := by
  obtain ⟨a, ha⟩ := e.property
  rw [ha]
  exact C.part_injOn_irreducible (copyCarrier a) (hA.range_embedding a)

/-- The local one-unit gain on the complete actual A-support inside one
original first wagon, with physical transversality discharged. -/
theorem FirstWagonRefinement.actualSupport_girthGT_firstWagon
    (A : RelStructure L UA) (hA : A.Irreducible)
    (C : StructuralRamsey.Partite.System L P X)
    {m : ℕ} {T : EdgeTrainLevels (OldACarrierEdge A C.toRelStructure) m}
    {hm : 0 < m} {allowed : Set P} {g : ℕ}
    (R : FirstWagonRefinement T hm (fun e => e.val) C.part allowed g)
    (hg : 2 ≤ g) (a : OldACarrierEdge A C.toRelStructure) :
    GirthGT {s : Set X | ∃ e : OldACarrierEdge A C.toRelStructure,
      T.rel ⟨1, by omega⟩ a e ∧ s = e.val} (g + 1) :=
  R.girthGT_firstWagon hg (actualASupport_part_injOn A hA C) a

/-- The full actual core support gains one unit only when all of its edges
belong to the original first wagon.  This explicit containment assumption
cannot be inferred from the first-wagon refinement data alone. -/
theorem FirstWagonRefinement.actualSupport_girthGT_of_first_universal
    (A : RelStructure L UA) (hA : A.Irreducible)
    (C : StructuralRamsey.Partite.System L P X)
    {m : ℕ} {T : EdgeTrainLevels (OldACarrierEdge A C.toRelStructure) m}
    {hm : 0 < m} {allowed : Set P} {g : ℕ}
    (R : FirstWagonRefinement T hm (fun e => e.val) C.part allowed g)
    (hg : 2 ≤ g)
    (hFirstUniversal : ∀ e f : OldACarrierEdge A C.toRelStructure,
      T.rel ⟨1, by omega⟩ e f) :
    GirthGT (supportCopies A C.toRelStructure) (g + 1) := by
  have h := R.girthGT_of_first_universal hg (actualASupport_part_injOn A hA C)
    hFirstUniversal
  apply girthGT_of_subset ?_ h
  intro s hs
  exact ⟨⟨s, hs⟩, rfl⟩

end Actual
end StructuralRamsey.Girth
