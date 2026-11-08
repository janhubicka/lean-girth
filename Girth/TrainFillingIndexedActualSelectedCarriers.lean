import Girth.TrainFillingIndexedMonotoneCarrierBridge
import Girth.TrainFillingActualContractedColouredM

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

end StructuralRamsey.Girth.IndexedPrivateChoice
