import Girth.TrainFillingIndexedOrderedPlacementCarrier

set_option Elab.async false

/-!
# Actual indexed physical carrier transport from strict monotonicity

The already checked ordered-carrier lemma was formulated using a pair
of supplied families of bundled order embeddings: source placements
and canonical target placements. In the cutoff-two application those
bundles are not extra data: the source placement is the actual
choice-tagged full first-wagon map, and the canonical placement is
literally H.place of the chosen old target edge.

Build both order embeddings from their real StrictMono hypotheses.
The resulting exact G0-to-H filled physical edge-carrier equation
requires only full carrier equality for the genuinely selected map
and the two ordering conditions. In particular it does not assume
pointwise placement compatibility or an output physical edge map.

This is a conditional selected-copy adapter, not the construction
of the selected relational M-copy, its order, or its Ramsey arrow.
No appendix or new train-system-girth assertion is involved.
-/

namespace StructuralRamsey.Girth.IndexedPrivateChoice

universe v
variable {C V P X Y : Type v}
variable (U : C → PrivateWagonInput V P X)
variable (H : UniformFillingData Y X)
variable (hTemplate : ∀ c : C, (U c).templateEdges = H.templateEdges)
variable [LinearOrder X] [Finite X]
variable [LinearOrder (Vertex U)] [PartialOrder Y]

/-- The exact selected physical image of EACH heterogeneous first-wagon
or template edge follows from genuine monotonicity and equality of
the full selected first-wagon carriers. Ordered coordinate maps are
constructed rather than independently supplied. -/
theorem selectedIndexedFilledEdgeEmbedding_carrier_of_strictMono
    (β : (C × P) ↪ H.OldEdge)
    (selectedVertex : Vertex U ↪o Y)
    (hSourceMono : ∀ cp : C × P,
      StrictMono (fun x : X =>
        tagVertex U cp.1 ((U cp.1).place cp.2 x)))
    (hCanonicalMono : ∀ cp : C × P,
      StrictMono (H.place (β cp)))
    (hCarrier : ∀ cp : C × P,
      Set.range (fun x : X =>
        selectedVertex (tagVertex U cp.1 ((U cp.1).place cp.2 x))) =
      Set.range (H.place (β cp)))
    (a : Edge U) :
    (selectedIndexedFilledEdgeEmbedding U H hTemplate β a).1 =
      (fun z : Vertex U => selectedVertex z) '' edgeCarrier U a := by
  let sourcePlacement : (C × P) → X ↪o Vertex U :=
    fun cp => OrderEmbedding.ofStrictMono
      (fun x : X => tagVertex U cp.1 ((U cp.1).place cp.2 x))
      (hSourceMono cp)
  let canonicalPlacement : (C × P) → X ↪o Y :=
    fun cp => OrderEmbedding.ofStrictMono
      (H.place (β cp)) (hCanonicalMono cp)
  exact selectedIndexedFilledEdgeEmbedding_carrier_of_ordered
    U H hTemplate β sourcePlacement selectedVertex canonicalPlacement
    (by intro cp x; rfl)
    (by intro cp x; rfl)
    (by intro cp; exact hCarrier cp)
    a

end StructuralRamsey.Girth.IndexedPrivateChoice
