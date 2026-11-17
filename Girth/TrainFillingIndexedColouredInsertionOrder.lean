import Girth.TrainFillingIndexedColourOrder
import Girth.TrainFillingActualContractedColouredM

set_option Elab.async false

/-! # The contracted target with its constructed colour order -/

namespace StructuralRamsey.Girth.IndexedPrivateChoice

universe v
variable {C V P X I : Type v}
variable (U : C → PrivateWagonInput V P X)
variable [LinearOrder C] [LinearOrder V] [Fintype V]
variable [LinearOrder P] [LinearOrder X] [LinearOrder I]

/-- The actual contracted M with a CONSTRUCTED colour-first order on
all tagged heterogeneous G0 vertices, not an assumed global order. -/
noncomputable def actualIndexedContractedM
    {k : ℕ}
    (oldColour : V → I) (templateColour : X → I) :
    RelStructure (colouredOrderedEdgeLanguage I k) (Vertex U) :=
  letI : LinearOrder (Vertex U) :=
    colouredChoiceInsertionOrder U oldColour templateColour
  actualContractedColouredM U oldColour templateColour

/-- Exact physical support of the actual contracted M, WITHOUT a
separately postulated global order or full-edge support equality.

The old coordinates and template X really must respect the common
colour order. Under those actual input conditions the constructed
colour-first order provides all ordered enumerations, and the checked
support theorem #897 proves the conclusion. -/
theorem actualIndexedContractedM_support_eq
    {k : ℕ}
    (enumerateX : Fin k ≃ X) (hEnumerate : StrictMono enumerateX)
    (oldColour : V → I) (templateColour : X → I)
    (hColour : ∀ c : C, ∀ p : P,
      ∀ z : {v : V // v ∈ (U c).oldCarrier p},
        oldColour z.1 = templateColour ((U c).coordinate p z))
    (hCoordinate : ∀ c : C, ∀ p : P,
      StrictMono ((U c).coordinate p))
    (hXBlocks : ∀ x y : X,
      templateColour x ≠ templateColour y →
      x < y → templateColour x < templateColour y) :
    supportCopies
        (colouredOrderedEdgeSource k
          (fun i => templateColour (enumerateX i)))
        (actualIndexedContractedM U oldColour templateColour) =
      Set.range (contractedCarrier U) := by
  letI : LinearOrder (Vertex U) :=
    colouredChoiceInsertionOrder U oldColour templateColour
  change supportCopies
      (colouredOrderedEdgeSource k
        (fun i => templateColour (enumerateX i)))
      (actualContractedColouredM U oldColour templateColour) =
    Set.range (contractedCarrier U)
  apply actualContractedColouredM_support_eq
    U enumerateX oldColour templateColour hColour
  intro cp i j _
  exact colouredChoiceEnumerate_lt_iff U oldColour templateColour
    enumerateX hEnumerate hColour hCoordinate hXBlocks cp i j

end StructuralRamsey.Girth.IndexedPrivateChoice
