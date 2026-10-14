import Girth.TrainActualPhysicalAEdgePushout
import Girth.TrainActualTopParentQuotientBridge

/-!
# Evaluate canonical physical A-support edges in the actual attachment

The genuine physical core/private edge presentation is bijective to the
actual A-support carrier hypergraph. Its evaluation agrees with each
canonical core edge and with every indexed old edge, including shared
old edges that are represented on the core side.

These identities are equalities of physical vertex *sets*, not of
A-embeddings. No cover by designated B-copies is required.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}} {UA Old Core I : Type v}

/-- The core arm of the physical edge bijection evaluates to the
physical image of that genuine core support edge. -/
theorem actualAPictureEdgeEquiv_core_carrier
    (A : RelStructure L UA)
    (hA : A.Irreducible)
    (B : RelStructure L Old)
    (S : Set Old)
    (D : RelStructure L Core)
    (f : I → RelStructure.Embedding (B.induce S) D)
    (e : OldACarrierEdge A D) :
    (actualAPictureEdgeEquiv A hA B S D f
      (physicalCoreEdge (sharedOldACarrierInclusion A B S) I e)).1 =
    attachedCoreAEdgeCarrier A B S D f e := by
  rfl

/-- Every old genuine support edge, shared or private, evaluates
to its actual carrier in its indexed standard copy. -/
theorem actualAPictureEdgeEquiv_standard_carrier
    (A : RelStructure L UA)
    (hA : A.Irreducible)
    (B : RelStructure L Old)
    (S : Set Old)
    (D : RelStructure L Core)
    (f : I → RelStructure.Embedding (B.induce S) D)
    (i : I) (e : OldACarrierEdge A B) :
    (actualAPictureEdgeEquiv A hA B S D f
      (physicalStandardEdge
        (sharedOldACarrierInclusion A B S)
        (sharedOldACarrierCoreEmbedding A B S D f) i e)).1 =
      attachedOldAEdgeCarrier A B S D f i e := by
  classical
  by_cases h : e ∈ Set.range (sharedOldACarrierInclusion A B S)
  · obtain ⟨s, hs⟩ := h
    subst e
    rw [physicalStandardEdge_shared]
    exact (actualAPictureEdgeEquiv_core_carrier A hA B S D f
      (sharedOldACarrierCoreEmbedding A B S D f i s)).trans
      (attachedSharedAEdgeCarrier_eq A B S D f i s).symm
  · rw [physicalStandardEdge_private
      (sharedOldACarrierInclusion A B S)
      (sharedOldACarrierCoreEmbedding A B S D f) i e h]
    rfl

end StructuralRamsey.Girth
