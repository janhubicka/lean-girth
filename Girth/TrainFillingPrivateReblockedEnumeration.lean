import Girth.TrainFillingPrivateReblockedContractedM
import Mathlib.Data.Fintype.Sort

set_option Elab.async false

/-!
# Remove the arbitrary ordered-X enumeration from the shortened M

The actual contracted-M support theorem was formulated using
  enumerateX : Fin k ≃ X
with a separate StrictMono enumeration certificate.

After sorting X by predicate colours, the finite linear order
canonically has an increasing enumeration by
  Fintype.orderIsoFinOfCardEq X rfl.

Hence there is no new enumeration hypothesis at cutoff two.
The other two former inputs hXBlocks and hCoordinate after
reblocking were already derived in the preceding module.
We now produce the ACTUAL full support equality of the ordered
colour-block contracted M, retaining the original old-carrier
linearity as the true separate geometric input to the
physical-train and Ramsey constructions.

Source candidate until exact-head Lean compilation; no
new Ramsey arrow, actual selected OrderStage or final
T embedding is assumed in this module.
-/

namespace StructuralRamsey.Girth.IndexedPrivateChoice

universe v
variable {C V P X I : Type v}
variable (U : C → PrivateWagonInput V P X)
variable [LinearOrder C] [LinearOrder V] [Fintype V]
variable [LinearOrder P] [LinearOrder X] [LinearOrder I]
variable [Fintype X]

/-- The actual finite X sorted by predicate blocks has a
canonical increasing enumeration. The order is reblocked
ONLY for constructing this enumeration; the underlying
vertex type X and all template edges remain unchanged. -/
noncomputable def reblockedXEnumeration
    (templateColour : X → I) :
    Fin (Fintype.card X) ≃ X := by
  letI : LinearOrder X := colourBlockOrder templateColour
  exact (Fintype.orderIsoFinOfCardEq X rfl).toEquiv

/-- The constructed enumeration is increasing for the
predicate-block order, not necessarily the original
EHN auxiliary order. -/
theorem reblockedXEnumeration_strictMono
    (templateColour : X → I) :
    letI : LinearOrder X := colourBlockOrder templateColour
    StrictMono (reblockedXEnumeration (X := X) templateColour) := by
  letI : LinearOrder X := colourBlockOrder templateColour
  change StrictMono ((Fintype.orderIsoFinOfCardEq X rfl).toEquiv)
  exact (Fintype.orderIsoFinOfCardEq X rfl).strictMono

/-- Actual full heterogeneous M-support with all three order
bookkeeping inputs discharged:
1) the order-compatible X enumeration is CONSTRUCTED;
2) hCoordinate for the reblocked X is DERIVED from original
   coordinate monotonicity, colour preservation and block
   ordering of original V;
3) hXBlocks is DERIVED from colourBlockOrder.

The distinct first-wagon carrier hypotheses are not bundled
into this identity; they are used by the subsequent checked
contractedPhysicalEdgeEquiv and cut-girth theorems. -/
theorem actualIndexedContractedM_support_without_enumeration
    [Nontrivial X]
    (oldColour : V → I) (templateColour : X → I)
    (hColour : ∀ c : C, ∀ p : P,
      ∀ z : {v : V // v ∈ (U c).oldCarrier p},
        oldColour z.1 = templateColour ((U c).coordinate p z))
    (hCoordinate : ∀ c : C, ∀ p : P,
      StrictMono ((U c).coordinate p))
    (hOldBlocks : ∀ x y : V,
      oldColour x ≠ oldColour y →
      x < y → oldColour x < oldColour y) :
    letI : LinearOrder X := colourBlockOrder templateColour
    supportCopies
        (colouredOrderedEdgeSource (Fintype.card X)
          (fun i => templateColour (reblockedXEnumeration
            (X := X) templateColour i)))
        (actualIndexedContractedM U oldColour templateColour) =
      Set.range (contractedCarrier U) := by
  exact actualIndexedContractedM_support_of_reblockedX
    U oldColour templateColour
      (reblockedXEnumeration (X := X) templateColour)
      (reblockedXEnumeration_strictMono
        (X := X) templateColour)
      hColour hCoordinate hOldBlocks

end StructuralRamsey.Girth.IndexedPrivateChoice
