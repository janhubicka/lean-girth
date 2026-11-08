import Girth.TrainFillingIndexedMonotoneCarrierBridge
import Girth.TrainFillingActualContractedColouredM
import Girth.TrainFillingIndexedColouredInsertionOrder
import Girth.TrainFillingColouredBlockMonotone

set_option Elab.async false

/-!
# Exact physical filled G0 carriers from one genuinely selected M-copy

The checked contracted-coloured M support theorem supplies every full
first-wagon carrier.  The checked source-to-selected-old-edge embedding
takes a GENUINE induced relational embedding b : M ↪ N, rather than a
separately invented physical old-edge map.

Compose it with the checked indexed filled edge map, then recover
its precise vertex carrier from:
* exact full-image equality of the selected old physical edge;
* source and canonical full-wagon monotonicity;
* finite uniqueness of increasing parametrisations (merged #913,
  instantiated by the strictly monotone interface in draft #934).

No hypothesis identifies individual X-coordinates or postulates the
output filled-edge carrier equality.  The actual selected b, its
monotonicity and the genuine canonical ordered placements remain
explicit applications of the shortened-train Ramsey witness.
This is not the global selected-family Ramsey arrow or full
system-girth theorem.
-/

namespace StructuralRamsey.Girth.IndexedPrivateChoice

open StructuralRamsey.RelStructure

universe v
variable {C V P X Y I : Type v}
variable (U : C → PrivateWagonInput V P X)
variable (H : UniformFillingData Y X)
variable (hTemplate : ∀ c : C, (U c).templateEdges = H.templateEdges)
variable [LinearOrder X] [Finite X] [Nontrivial X]
variable [LinearOrder (Vertex U)] [PartialOrder Y]

/-- A genuinely selected relational M-copy supplies all *old* carrier
images, and the actual complete filling then supplies every physical
G0 edge.  The resulting exact vertex-carrier equation holds for
unselected template edges as well as the distinguished W*-subedges. -/
theorem selectedIndexedFilledEdgeEmbedding_carrier_of_actualM
    {k : ℕ}
    (enumerateX : Fin k ≃ X)
    (oldColour : V → I) (templateColour : X → I)
    (hColour : ∀ c : C, ∀ p : P,
      ∀ z : {v : V // v ∈ (U c).oldCarrier p},
        oldColour z.1 = templateColour ((U c).coordinate p z))
    (hOrdered : ∀ e : C × P, ∀ i j : Fin k,
      templateColour (enumerateX i) = templateColour (enumerateX j) →
      (i < j ↔
        contractedEnumerationOfEquiv U enumerateX e i <
          contractedEnumerationOfEquiv U enumerateX e j))
    (hLinear : ∀ c : C, ∀ p q : P, p ≠ q →
      ((U c).oldCarrier p ∩ (U c).oldCarrier q).Subsingleton)
    (N : RelStructure (colouredOrderedEdgeLanguage I k) Y)
    (b : Embedding (actualContractedColouredM U oldColour templateColour) N)
    (hOldSupport : H.oldEdges =
      supportCopies
        (colouredOrderedEdgeSource k
          (fun i => templateColour (enumerateX i))) N)
    (hSourceMono : ∀ cp : C × P,
      StrictMono (fun x : X =>
        tagVertex U cp.1 ((U cp.1).place cp.2 x)))
    (hSelectedMono : StrictMono (fun z : Vertex U => b z))
    (hCanonicalMono : ∀ f : H.OldEdge,
      StrictMono (H.place f))
    (a : Edge U) :
    (selectedIndexedFilledEdgeEmbedding U H hTemplate
      (actualContractedSelectedOldEdgeEmbedding U enumerateX
        oldColour templateColour hColour hOrdered hLinear
        N b H hOldSupport) a).1 =
      (fun z : Vertex U => b z) '' edgeCarrier U a := by
  let β : (C × P) ↪ H.OldEdge :=
    actualContractedSelectedOldEdgeEmbedding U enumerateX
      oldColour templateColour hColour hOrdered hLinear
      N b H hOldSupport
  let vertex : Vertex U ↪o Y :=
    OrderEmbedding.ofStrictMono (fun z : Vertex U => b z) hSelectedMono
  have hFullCarrier (cp : C × P) :
      Set.range (fun x : X =>
        vertex (tagVertex U cp.1 ((U cp.1).place cp.2 x))) =
      Set.range (H.place (β cp)) := by
    calc
      Set.range (fun x : X =>
          vertex (tagVertex U cp.1 ((U cp.1).place cp.2 x))) =
        (fun z : Vertex U => b z) '' contractedCarrier U cp := by
          ext y
          constructor
          · rintro ⟨x, rfl⟩
            exact ⟨tagVertex U cp.1 ((U cp.1).place cp.2 x),
              ⟨(U cp.1).place cp.2 x, ⟨x, rfl⟩, rfl⟩, rfl⟩
          · rintro ⟨z, ⟨w, ⟨x, rfl⟩, rfl⟩, rfl⟩
            exact ⟨x, rfl⟩
      _ = (β cp).1 := by
        exact (actualContractedSelectedOldEdgeEmbedding_carrier U
          enumerateX oldColour templateColour hColour hOrdered hLinear
          N b H hOldSupport cp).symm
      _ = Set.range (H.place (β cp)) := (H.range_place (β cp)).symm
  exact selectedIndexedFilledEdgeEmbedding_carrier_of_strictMono
    U H hTemplate β vertex hSourceMono
    (fun cp => hCanonicalMono (β cp)) hFullCarrier a


/-- The genuine selected old-edge map on an ACTUAL heterogeneous
colour-block-ordered M.  This is derived from the relational selected
copy and the global source order, not supplied as independent physical
input. The noncomputable definition chooses no target edge beyond
the image determined by b. -/
noncomputable def selectedActualIndexedOldEdgeEmbedding
    [LinearOrder C] [LinearOrder V] [Fintype V]
    [LinearOrder P] [LinearOrder I]
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
      x < y → templateColour x < templateColour y)
    (hLinear : ∀ c : C, ∀ p q : P, p ≠ q →
      ((U c).oldCarrier p ∩ (U c).oldCarrier q).Subsingleton)
    (targetColour : Y → I)
    (b : Embedding
      (actualIndexedContractedM U oldColour templateColour)
      (colouredOrderedEdgeTarget k H.oldEdges targetColour))
    (hOldSupport : H.oldEdges =
      supportCopies
        (colouredOrderedEdgeSource k
          (fun i => templateColour (enumerateX i)))
        (colouredOrderedEdgeTarget k H.oldEdges targetColour)) :
    (C × P) ↪ H.OldEdge := by
  letI : LinearOrder (Vertex U) :=
    colouredChoiceInsertionOrder U oldColour templateColour
  have hOrdered : ∀ e : C × P, ∀ i j : Fin k,
      templateColour (enumerateX i) = templateColour (enumerateX j) →
      (i < j ↔
        contractedEnumerationOfEquiv U enumerateX e i <
          contractedEnumerationOfEquiv U enumerateX e j) := by
    intro cp i j _
    exact colouredChoiceEnumerate_lt_iff U oldColour templateColour
      enumerateX hEnumerate hColour hCoordinate hXBlocks cp i j
  exact actualContractedSelectedOldEdgeEmbedding U enumerateX
    oldColour templateColour hColour hOrdered hLinear
    (colouredOrderedEdgeTarget k H.oldEdges targetColour)
    b H hOldSupport

/-- With the checked global colour-block order, a genuine induced
M-copy in an equally block-ordered N has a strictly increasing
vertex map. All source full-X placements are increasing too.
Consequently the filled H physical edge carrier identity is
a theorem of the selected b plus its canonical target placements,
with no independently postulated whole-carrier or pointwise equality. -/
theorem selectedIndexedFilledEdgeEmbedding_carrier_of_actualIndexedM
    [LinearOrder C] [LinearOrder V] [Fintype V]
    [LinearOrder P] [LinearOrder I] [LinearOrder Y]
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
      x < y → templateColour x < templateColour y)
    (hLinear : ∀ c : C, ∀ p q : P, p ≠ q →
      ((U c).oldCarrier p ∩ (U c).oldCarrier q).Subsingleton)
    (targetColour : Y → I)
    (b : Embedding
      (actualIndexedContractedM U oldColour templateColour)
      (colouredOrderedEdgeTarget k H.oldEdges targetColour))
    (hTargetBlocks : ∀ x y : Y,
      targetColour x < targetColour y → x < y)
    (hOldSupport : H.oldEdges =
      supportCopies
        (colouredOrderedEdgeSource k
          (fun i => templateColour (enumerateX i)))
        (colouredOrderedEdgeTarget k H.oldEdges targetColour))
    (hCanonicalMono : ∀ f : H.OldEdge, StrictMono (H.place f))
    (a : Edge U) :
    (selectedIndexedFilledEdgeEmbedding U H hTemplate
      (selectedActualIndexedOldEdgeEmbedding U H
        enumerateX hEnumerate oldColour templateColour
        hColour hCoordinate hXBlocks hLinear targetColour b hOldSupport) a).1 =
      (fun z : Vertex U => b z) '' edgeCarrier U a := by
  letI : LinearOrder (Vertex U) :=
    colouredChoiceInsertionOrder U oldColour templateColour
  have hOrdered : ∀ e : C × P, ∀ i j : Fin k,
      templateColour (enumerateX i) = templateColour (enumerateX j) →
      (i < j ↔
        contractedEnumerationOfEquiv U enumerateX e i <
          contractedEnumerationOfEquiv U enumerateX e j) := by
    intro cp i j _
    exact colouredChoiceEnumerate_lt_iff U oldColour templateColour
      enumerateX hEnumerate hColour hCoordinate hXBlocks cp i j
  have hSourceMono : ∀ cp : C × P,
      StrictMono (fun x : X =>
        tagVertex U cp.1 ((U cp.1).place cp.2 x)) := by
    intro cp x y hxy
    exact colouredChoicePlace_lt U oldColour templateColour
      hColour hCoordinate hXBlocks cp hxy
  have hSourceBlocks : ∀ x y : Vertex U,
      contractedVertexColour U oldColour templateColour x ≠
        contractedVertexColour U oldColour templateColour y →
      x < y →
      contractedVertexColour U oldColour templateColour x <
        contractedVertexColour U oldColour templateColour y := by
    intro x y hNe hxy
    change colouredChoiceInsertionKey U oldColour templateColour x <
      colouredChoiceInsertionKey U oldColour templateColour y at hxy
    rcases Prod.Lex.toLex_lt_toLex.mp hxy with hColourLt | ⟨hEq, _⟩
    · exact hColourLt
    · exact False.elim (hNe hEq)
  have hSelectedMono : StrictMono (fun z : Vertex U => b z) := by
    exact colouredOrderedEmbedding_strictMono
      k (Set.range (contractedCarrier U)) H.oldEdges
      (contractedVertexColour U oldColour templateColour)
      targetColour b hSourceBlocks hTargetBlocks
  exact selectedIndexedFilledEdgeEmbedding_carrier_of_actualM
    U H hTemplate enumerateX oldColour templateColour
    hColour hOrdered hLinear
    (colouredOrderedEdgeTarget k H.oldEdges targetColour)
    b hOldSupport hSourceMono hSelectedMono hCanonicalMono a

end StructuralRamsey.Girth.IndexedPrivateChoice
