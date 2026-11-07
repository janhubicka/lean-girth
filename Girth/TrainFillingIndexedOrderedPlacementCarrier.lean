import Girth.TrainFillingIndexedSelectedPhysicalMap
import Girth.TrainFillingOrderedPlacementUnique

set_option Elab.async false

/-!
# Literal indexed filled-edge carriers from genuine ordered placements

The checked heterogeneous physical G0→H map (#894) supplies exact
new-edge carriers given a pointwise equation between every selected
source X-coordinate and the canonical filled X_f-coordinate in N.

The pointwise equation is NOT an independent mathematical hypothesis.
When both placements are increasing and the actual selected vertex
map transports each full first-wagon carrier ONTO the corresponding
full old N-edge carrier, finite order-embedding uniqueness forces
the coordinates to coincide at every x in X.

These identities imply the indexed edge-carrier equation of the
actual selected G0→H physical map. No arbitrary new edge map, new
girth, or pruning of ambient H physical edges is used. Constructing
the source global colour-block order and genuine selected M-copy
remain the application obligations.
-/

namespace StructuralRamsey.Girth.IndexedPrivateChoice

universe v
variable {C V P X Y : Type v}
variable (U : C → PrivateWagonInput V P X)
variable (H : UniformFillingData Y X)
variable (hTemplate : ∀ c : C, (U c).templateEdges = H.templateEdges)
variable [LinearOrder X] [Finite X]
variable [PartialOrder (Vertex U)] [PartialOrder Y]

/-- Equality of complete ordered carriers forces the literal
selected-vs-canonical placement equation in every first wagon.

The source/canonical ordered coordinate structures are genuine
order embeddings. The selected map and its image carrier are genuine
data of the shorter-train witness, not an assumed pointwise
identification of the eventual H vertex lift. -/
theorem selectedIndexedPlacement_eq_of_ordered_carriers
    (β : (C × P) ↪ H.OldEdge)
    (sourcePlacement : (C × P) → X ↪o Vertex U)
    (selectedVertex : Vertex U ↪o Y)
    (canonicalPlacement : (C × P) → X ↪o Y)
    (hSource : ∀ cp : C × P, ∀ x : X,
      sourcePlacement cp x =
        tagVertex U cp.1 ((U cp.1).place cp.2 x))
    (hCanonical : ∀ cp : C × P, ∀ x : X,
      canonicalPlacement cp x = H.place (β cp) x)
    (hCarrier : ∀ cp : C × P,
      Set.range (fun x : X => selectedVertex (sourcePlacement cp x)) =
        Set.range (canonicalPlacement cp : X → Y))
    (cp : C × P) (x : X) :
    H.place (β cp) x =
      selectedVertex (tagVertex U cp.1 ((U cp.1).place cp.2 x)) := by
  have hCoordinate :=
    finite_ordered_selected_coordinates_commute
      sourcePlacement selectedVertex canonicalPlacement hCarrier cp x
  calc
    H.place (β cp) x = canonicalPlacement cp x :=
      (hCanonical cp x).symm
    _ = selectedVertex (sourcePlacement cp x) := hCoordinate.symm
    _ = selectedVertex (tagVertex U cp.1
          ((U cp.1).place cp.2 x)) :=
      congrArg selectedVertex (hSource cp x)

/-- The exact selected G0 physical H-edge carrier equality follows
from ordered complete first-wagon image equality, with no extra
pointwise placement-compatibility premise. -/
theorem selectedIndexedFilledEdgeEmbedding_carrier_of_ordered
    (β : (C × P) ↪ H.OldEdge)
    (sourcePlacement : (C × P) → X ↪o Vertex U)
    (selectedVertex : Vertex U ↪o Y)
    (canonicalPlacement : (C × P) → X ↪o Y)
    (hSource : ∀ cp : C × P, ∀ x : X,
      sourcePlacement cp x =
        tagVertex U cp.1 ((U cp.1).place cp.2 x))
    (hCanonical : ∀ cp : C × P, ∀ x : X,
      canonicalPlacement cp x = H.place (β cp) x)
    (hCarrier : ∀ cp : C × P,
      Set.range (fun x : X => selectedVertex (sourcePlacement cp x)) =
        Set.range (canonicalPlacement cp : X → Y))
    (a : Edge U) :
    (selectedIndexedFilledEdgeEmbedding U H hTemplate β a).1 =
      (fun z : Vertex U => selectedVertex z) '' edgeCarrier U a := by
  let vertex : Vertex U ↪ Y :=
    ⟨(fun z : Vertex U => selectedVertex z), selectedVertex.injective⟩
  change (selectedIndexedFilledEdgeEmbedding U H hTemplate β a).1 =
    vertex '' edgeCarrier U a
  apply selectedIndexedFilledEdgeEmbedding_carrier
    U H hTemplate β vertex
  intro c p x
  exact selectedIndexedPlacement_eq_of_ordered_carriers
    U H β sourcePlacement selectedVertex canonicalPlacement
    hSource hCanonical hCarrier (c, p) x

end StructuralRamsey.Girth.IndexedPrivateChoice
