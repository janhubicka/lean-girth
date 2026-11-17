import Girth.TrainFillingPrivateColouredInsertionOrder
import Girth.TrainFillingIndexedCarrierGeometry
import Girth.TrainFillingColouredOrderedEdgePresentation

set_option Elab.async false

/-! # Colour order on the heterogeneous contracted target -/

namespace StructuralRamsey.Girth.IndexedPrivateChoice

open StructuralRamsey.RelStructure

universe u v
variable {C V P X : Type v} {I : Type u}
variable (U : C → PrivateWagonInput V P X)

/-- Coloured ordered M defined LITERALLY on the complete tagged G0
vertex set, with precisely all whole first-wagon carriers as edges. -/
def actualContractedColouredM
    {k : ℕ}
    (oldColour : V → I) (templateColour : X → I)
    [LinearOrder (Vertex U)] :
    RelStructure (colouredOrderedEdgeLanguage I k) (Vertex U) :=
  colouredOrderedEdgeTarget k
    (Set.range (contractedCarrier U))
    (contractedVertexColour U oldColour templateColour)

end StructuralRamsey.Girth.IndexedPrivateChoice

namespace StructuralRamsey.Girth.IndexedPrivateChoice

universe v
variable {C V P X I : Type v}
variable (U : C → PrivateWagonInput V P X)
variable [LinearOrder C] [LinearOrder V] [Fintype V]
variable [LinearOrder P] [LinearOrder X] [LinearOrder I]

/-- One ordered key on the actual complete Sigma vertex set. -/
noncomputable def colouredChoiceInsertionKey
    (oldColour : V → I) (templateColour : X → I) :
    Vertex U → I ×ₗ (C ×ₗ (WithTop V ×ₗ WithTop (P ×ₗ X))) :=
  fun z => toLex
    (contractedVertexColour U oldColour templateColour z,
      toLex (z.1, PrivateWagonInput.insertionKey (U z.1) z.2))

/-- Choice tags distinguish vertices from different choices; within
one choice, the old/private insertion key is injective. -/
theorem colouredChoiceInsertionKey_injective
    (oldColour : V → I) (templateColour : X → I) :
    Function.Injective
      (colouredChoiceInsertionKey U oldColour templateColour) := by
  rintro ⟨c, z⟩ ⟨d, w⟩ h
  have hChoice : c = d :=
    congrArg
      (fun q : I ×ₗ (C ×ₗ (WithTop V ×ₗ WithTop (P ×ₗ X))) =>
        (ofLex (ofLex q).2).1) h
  subst d
  have hKey :
      PrivateWagonInput.insertionKey (U c) z =
        PrivateWagonInput.insertionKey (U c) w :=
    congrArg
      (fun q : I ×ₗ (C ×ₗ (WithTop V ×ₗ WithTop (P ×ₗ X))) =>
        (ofLex (ofLex q).2).2) h
  exact congrArg (Sigma.mk c)
    ((PrivateWagonInput.insertionKey_injective (U c)) hKey)

/-- A single order on the whole heterogeneous union, with predicate
blocks in the common order, then choices, then private insertion. -/
noncomputable def colouredChoiceInsertionOrder
    (oldColour : V → I) (templateColour : X → I) :
    LinearOrder (Vertex U) :=
  LinearOrder.lift'
    (colouredChoiceInsertionKey U oldColour templateColour)
    (colouredChoiceInsertionKey_injective U oldColour templateColour)

/-- Every whole first-wagon coordinate preserves the order of X in
the ONE global heterogeneous union order. -/
theorem colouredChoicePlace_lt
    (oldColour : V → I) (templateColour : X → I)
    (hColour : ∀ c : C, ∀ p : P,
      ∀ z : {v : V // v ∈ (U c).oldCarrier p},
        oldColour z.1 = templateColour ((U c).coordinate p z))
    (hCoordinate : ∀ c : C, ∀ p : P,
      StrictMono ((U c).coordinate p))
    (hXBlocks : ∀ x y : X,
      templateColour x ≠ templateColour y →
      x < y → templateColour x < templateColour y)
    (cp : C × P) {x y : X} (hxy : x < y) :
    @LT.lt (Vertex U)
      (colouredChoiceInsertionOrder U oldColour templateColour).toLT
      (tagVertex U cp.1 ((U cp.1).place cp.2 x))
      (tagVertex U cp.1 ((U cp.1).place cp.2 y)) := by
  change colouredChoiceInsertionKey U oldColour templateColour
      (tagVertex U cp.1 ((U cp.1).place cp.2 x)) <
    colouredChoiceInsertionKey U oldColour templateColour
      (tagVertex U cp.1 ((U cp.1).place cp.2 y))
  have hCx : contractedVertexColour U oldColour templateColour
      (tagVertex U cp.1 ((U cp.1).place cp.2 x)) =
      templateColour x :=
    contractedVertexColour_place U oldColour templateColour hColour
      cp.1 cp.2 x
  have hCy : contractedVertexColour U oldColour templateColour
      (tagVertex U cp.1 ((U cp.1).place cp.2 y)) =
      templateColour y :=
    contractedVertexColour_place U oldColour templateColour hColour
      cp.1 cp.2 y
  by_cases hs : templateColour x = templateColour y
  · have hk : PrivateWagonInput.insertionKey (U cp.1)
        ((U cp.1).place cp.2 x) <
        PrivateWagonInput.insertionKey (U cp.1)
          ((U cp.1).place cp.2 y) :=
      PrivateWagonInput.insertionOrder_place_lt
        (U cp.1) (hCoordinate cp.1) cp.2 hxy
    have hInside :
        (toLex (cp.1, PrivateWagonInput.insertionKey (U cp.1)
              ((U cp.1).place cp.2 x)) :
          C ×ₗ (WithTop V ×ₗ WithTop (P ×ₗ X))) <
        toLex (cp.1, PrivateWagonInput.insertionKey (U cp.1)
              ((U cp.1).place cp.2 y)) :=
      Prod.Lex.toLex_lt_toLex.mpr (Or.inr ⟨rfl, hk⟩)
    exact Prod.Lex.toLex_lt_toLex.mpr
      (Or.inr ⟨by simpa only [hCx, hCy] using hs, hInside⟩)
  · exact Prod.Lex.toLex_lt_toLex.mpr
      (Or.inl (by simpa only [hCx, hCy] using
        (hXBlocks x y hs hxy)))

/-- A globally increasing enumeration of the common ordered X is
increasing on every actual contracted first wagon, including all
private vertices, not only the chosen W* support edge positions. -/
theorem colouredChoiceEnumerate_lt_iff
    {k : ℕ}
    (oldColour : V → I) (templateColour : X → I)
    (enumerateX : Fin k ≃ X) (hEnumerate : StrictMono enumerateX)
    (hColour : ∀ c : C, ∀ p : P,
      ∀ z : {v : V // v ∈ (U c).oldCarrier p},
        oldColour z.1 = templateColour ((U c).coordinate p z))
    (hCoordinate : ∀ c : C, ∀ p : P,
      StrictMono ((U c).coordinate p))
    (hXBlocks : ∀ x y : X,
      templateColour x ≠ templateColour y →
      x < y → templateColour x < templateColour y)
    (cp : C × P) (i j : Fin k) :
    (i < j ↔
      @LT.lt (Vertex U)
        (colouredChoiceInsertionOrder U oldColour templateColour).toLT
        (contractedEnumerationOfEquiv U enumerateX cp i)
        (contractedEnumerationOfEquiv U enumerateX cp j)) := by
  have hComposed :
      StrictMono
        (fun i : Fin k => (toLex
          (contractedVertexColour U oldColour templateColour
            (contractedEnumerationOfEquiv U enumerateX cp i),
           toLex (cp.1,
             PrivateWagonInput.insertionKey (U cp.1)
               ((U cp.1).place cp.2 (enumerateX i)))) :
          I ×ₗ (C ×ₗ (WithTop V ×ₗ WithTop (P ×ₗ X))))) := by
    intro a b hab
    exact colouredChoicePlace_lt U oldColour templateColour
      hColour hCoordinate hXBlocks cp (hEnumerate hab)
  -- Reduce the chosen order to the injective lexicographic key.
  change i < j ↔
    colouredChoiceInsertionKey U oldColour templateColour
      (contractedEnumerationOfEquiv U enumerateX cp i) <
    colouredChoiceInsertionKey U oldColour templateColour
      (contractedEnumerationOfEquiv U enumerateX cp j)
  exact (hComposed.lt_iff_lt).symm

end StructuralRamsey.Girth.IndexedPrivateChoice
