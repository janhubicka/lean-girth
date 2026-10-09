import Girth.ActiveCarrierProjectedSupport

/-!
# Exact support hypergraph of an ordered active subsystem

The active carrier consists of vertices in A-copies with one prescribed
base projection. Because the induced active structure contains all those
copies, its transported A-support includes the projected edge family.
The converse is the ordered finite-carrier projection theorem.

Therefore the support of the actual induced active subsystem is
*exactly* the projected support family, not merely a subfamily.
This identifies the two girth invariants without making any assertion
about copies outside the active carrier.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {UA P X : Type v}

/-- Every A-edge with projection β belongs to the induced active
carrier and transports back to the same ambient A-edge. This
direction needs neither linearity nor ordered rigidity. -/
theorem projectedSupportCopies_subset_mapped_activeSupport
    (A : RelStructure L UA)
    (C : StructuralRamsey.Partite.System L P X)
    (β : UA ↪ P) :
    projectedSupportCopies A C β ⊆
      mappedSupportCopies A
        (C.induce (activeCarrier A C β)).toRelStructure
        C.toRelStructure
        (StructuralRamsey.Partite.System.inclusion C
          (activeCarrier A C β)).toEmbedding := by
  intro e he
  obtain ⟨a, rfl⟩ := he
  let aInd := activeInduceProjected A a
    (projected_mem_activeCarrier A C β a)
  refine ⟨aInd.val, ?_⟩
  rfl

/-- Exact identification of all A-support edges in the ordered
induced active carrier with the β-projected family of ambient A-edges.
Unlike active-carrier strongness, this equality does not use base
A-linearity. -/
theorem mapped_activeSupport_eq_projected_ordered
    (A₀ : RelStructure L UA)
    [LinearOrder UA] [Finite UA]
    (D : RelStructure L.withOrder P)
    (C : StructuralRamsey.Partite.System L.withOrder P X)
    (hPartite : C.IsPartiteOver D)
    (β : RelStructure.Embedding A₀.ordered D) :
    mappedSupportCopies A₀.ordered
      (C.induce
        (activeCarrier A₀.ordered C β.toFunctionEmbedding)).toRelStructure
      C.toRelStructure
      (StructuralRamsey.Partite.System.inclusion C
        (activeCarrier A₀.ordered C β.toFunctionEmbedding)).toEmbedding
      =
    projectedSupportCopies A₀.ordered C β.toFunctionEmbedding := by
  apply Set.Subset.antisymm
  · exact mapped_activeSupport_subset_projected_ordered
      A₀ D C hPartite β
  · exact projectedSupportCopies_subset_mapped_activeSupport
      A₀.ordered C β.toFunctionEmbedding

end StructuralRamsey.Girth
