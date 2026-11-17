import Girth.TrainFillingPrivateColourCompatibility
import Girth.TrainFillingPrivateColourBlockOrder
import Girth.TrainFillingIndexedColouredInsertionOrder

set_option Elab.async false

/-!
# The actual coloured shortened M after reordering X by predicates

The EHN template X has an auxiliary total order. For the actual
coloured contracted M we need a global X order listing predicate
blocks consecutively. Replacing X's order by colourBlockOrder
preserves the order within each predicate, and an old
colour-preserving coordinate map F_p -> X remains increasing
provided the OLD vertex order already lists predicate blocks.

Thus two former independent assumptions of the checked actual
contracted M support theorem are now derived:
  hCoordinate : every full first-wagon coordinate is increasing
  hXBlocks    : different X predicate blocks are in colour order.
The hColour condition follows from the two original unary-colour
embeddings (see TrainFillingPrivateColourCompatibility).

Only an actual increasing enumeration of finite REBLOCKED X and
the original ordered, covered EHN witness remain as inputs.

This is an interface theorem, not the missing existence of the
full RR_h selected OrderStage or the final original T embedding.
Source candidate, not kernel checked.
-/

namespace StructuralRamsey.Girth.IndexedPrivateChoice

universe v
variable {C V P X I : Type v}
variable (U : C → PrivateWagonInput V P X)
variable [LinearOrder C] [LinearOrder V] [Fintype V]
variable [LinearOrder P] [LinearOrder X] [LinearOrder I]

/-- The first-wagon coordinate maps remain globally increasing
after X is sorted by predicate colour, with no need to assume
they are separately increasing in the new order. -/
theorem selectedCoordinates_mono_after_colourBlockSort
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
    ∀ c : C, ∀ p : P,
      StrictMono ((U c).coordinate p) := by
  have hMonoAt (c : C) (p : P) :
      letI : LinearOrder X := colourBlockOrder templateColour
      StrictMono ((U c).coordinate p) := by
    exact strictMono_into_colourBlockOrder
      (fun z : {v : V // v ∈ (U c).oldCarrier p} => oldColour z.1)
      templateColour ((U c).coordinate p)
      (fun z => (hColour c p z).symm)
      (hCoordinate c p)
      (by
        intro x y hDifferent hxy
        exact hOldBlocks x.1 y.1 hDifferent hxy)
  intro c p
  exact hMonoAt c p

/-- Instantiate the CHECKED actual ordered coloured M support
theorem after reblocking the EHN template by predicate colours.
The hXBlocks parameter is PROVED by the constructed order; the
hCoordinate parameter is PROVED from original monotonicity and
actual unary-colour compatibility. The output support is the
complete physically distinct (choice,first-wagon) carrier family. -/
theorem actualIndexedContractedM_support_of_reblockedX
    [Finite X] [Nontrivial X]
    {k : ℕ}
    (oldColour : V → I) (templateColour : X → I)
    (enumerateX : Fin k ≃ X)
    (hEnumerate :
      letI : LinearOrder X := colourBlockOrder templateColour
      StrictMono enumerateX)
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
        (colouredOrderedEdgeSource k
          (fun i => templateColour (enumerateX i)))
        (actualIndexedContractedM U oldColour templateColour) =
      Set.range (contractedCarrier U) := by
  let hNewMono :
      letI : LinearOrder X := colourBlockOrder templateColour
      ∀ c : C, ∀ p : P, StrictMono ((U c).coordinate p) :=
    selectedCoordinates_mono_after_colourBlockSort
      U oldColour templateColour hColour hCoordinate hOldBlocks
  have hNewBlocks :
      letI : LinearOrder X := colourBlockOrder templateColour
      ∀ x y : X, templateColour x ≠ templateColour y →
        x < y → templateColour x < templateColour y := by
    intro x y hDifferent hxy
    exact colourBlockOrder_blocks templateColour x y hDifferent hxy
  letI : LinearOrder X := colourBlockOrder templateColour
  exact actualIndexedContractedM_support_eq U enumerateX
    hEnumerate oldColour templateColour hColour hNewMono hNewBlocks

end StructuralRamsey.Girth.IndexedPrivateChoice
