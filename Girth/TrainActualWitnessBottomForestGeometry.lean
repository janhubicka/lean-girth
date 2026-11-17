import Girth.TrainActiveGluingWitness
import Girth.ForestToSupremeActualGeometry

set_option autoImplicit false
set_option Elab.async false

/-!
# Bottom forest geometry of the GENUINE selected local witness

A local F_t witness uses the complete image of every selected active
copy and ALL ambient A-support edges. The shared-edge witness and
active-gluing witness presentations are exactly equal as OrderOneData,
including designated indices and wagon parents.

At the equality cut, ordinary A-linearity of the local witness yields
the physical BottomForestGeometry. This does not assume any output
system girth or a new local Ramsey construction.
-/

namespace StructuralRamsey.Girth
open StructuralRamsey.RelStructure

universe u v

variable {L : RelLanguage.{u}} {UA P X Y I : Type v}
variable (A : RelStructure L UA)
variable (C : StructuralRamsey.Partite.System L P X)
variable (α : UA → P) (R : RelStructure L Y)
variable (f : I → RelStructure.Embedding
  (C.toRelStructure.induce (activeCarrier A C α)) R)
variable {m : ℕ} (U : EdgeTrainLevels (OldACarrierEdge A R) m)

local notation "μBottom" => (⟨0, Nat.zero_lt_succ m⟩ : Fin (m + 1))
local notation "Local" => activeGluingWitnessOrderOneData
  A C α R f U μBottom
local notation "Shared" => sharedWitnessOrderOneData U μBottom
  (sharedOldACarrierCoreEmbedding A C.toRelStructure
    (activeCarrier A C α) R f)
  (Subtype.val : OldACarrierEdge A R → Set Y)

/-- Actual selected local gluing copies have the physical bottom
forest incidence geometry when the witness support is A-linear.
No copy-image strongness or designated edge coverage is needed. -/
theorem activeGluingWitness_bottomForestGeometry
    [Nontrivial UA] (hLinear : ALinear A R) :
    (Local).BottomForestGeometry where
  edge_subset := by
    intro a edge he
    cases a with
    | inl i => exact he
    | inr edge' =>
        have hEq : edge = edge' := he
        subst edge'
        exact Set.Subset.rfl
  edge_nontrivial := by
    intro edge
    obtain ⟨a, ha⟩ := edge.2
    change edge.1.Nontrivial
    rw [ha]
    obtain ⟨u, v, huv⟩ := exists_pair_ne UA
    exact ⟨a u, ⟨u, rfl⟩, a v, ⟨v, rfl⟩,
      fun h => huv (a.injective h)⟩
  edge_linear := by
    intro edge edge' hne
    obtain ⟨a, ha⟩ := edge.2
    obtain ⟨b, hb⟩ := edge'.2
    have hCopies : ¬ SameCopy a b := by
      intro h
      apply hne
      exact Subtype.ext (ha.trans (h.trans hb.symm))
    change (edge.1 ∩ edge'.1).Subsingleton
    rw [ha, hb]
    exact hLinear a b hCopies
  parent_injective := by
    intro edge edge' hEq
    exact (U.bottom edge edge').mp (Quotient.exact hEq)

/-- The literal shared-witness system (used in the cut-indexed
reduction) is exactly the complete gluing-copy bottom system.
Thus the same bottom geometry transfers without an extra axiom. -/
theorem sharedWitness_bottomForestGeometry_of_aLinear
    [Nontrivial UA] (hLinear : ALinear A R) :
    (Shared).BottomForestGeometry := by
  have h := activeGluingWitness_bottomForestGeometry
    A C α R f U hLinear
  rw [← activeGluingWitnessOrderOneData_eq_shared
    A C α R f U μBottom]
  exact h

end StructuralRamsey.Girth
