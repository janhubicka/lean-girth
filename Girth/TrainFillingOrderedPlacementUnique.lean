import Mathlib.Order.Preorder.Finite

set_option Elab.async false

/-!
# Canonical finite ordered edge placements are unique

A coloured one-edge template X has fixed within-predicate linear orders.
On each prescribed finite ordered edge type (or after concatenating its
predicate blocks), an order-preserving coordinate map onto a given
physical edge carrier is UNIQUE.

Consequently an order-preserving selected M-copy embedding automatically
commutes with canonical local X placements once it is known to send the
whole contracted edge carrier onto the required old N-edge carrier.
The pointwise compatibility required for the physical filled-edge map
is therefore not an independent input.

This module isolates the finite-order argument; extending its result
to the actual relational coloured predicates and constructing the real
selected M-copy maps remain separate application work.
-/

namespace StructuralRamsey.Girth

universe v

/-- A finite ordered source cannot have two different increasing
parametrizations of the SAME target carrier. No finiteness or
well-foundedness assumption on the ambient target order is needed. -/
theorem finite_orderEmbedding_eq_of_range_eq
    {X Y : Type v} [LinearOrder X] [PartialOrder Y] [Finite X]
    (f g : X ↪o Y)
    (hRange : Set.range (f : X → Y) = Set.range (g : X → Y)) :
    f = g :=
  (OrderEmbedding.range_eq_iff).mp hRange

/-- If the selected old M-copy preserves the template order and maps
one entire source first-wagon carrier to the canonical N-edge carrier,
its local coordinates literally agree with the canonical X_f placement.
This is a conclusion, not a separately chosen coordinate identification. -/
theorem finite_ordered_selected_coordinate_commutes
    {X W V : Type v}
    [LinearOrder X] [PartialOrder W] [PartialOrder V] [Finite X]
    (sourceCoordinate : X ↪o W)
    (selectedVertex : W ↪o V)
    (canonicalPlacement : X ↪o V)
    (hCarrier :
      Set.range (fun x : X => selectedVertex (sourceCoordinate x)) =
      Set.range (canonicalPlacement : X → V)) :
    ∀ x : X,
      selectedVertex (sourceCoordinate x) = canonicalPlacement x := by
  let composed : X ↪o V := sourceCoordinate.comp selectedVertex
  have hRange :
      Set.range (composed : X → V) =
      Set.range (canonicalPlacement : X → V) := hCarrier
  have hEq : composed = canonicalPlacement :=
    finite_orderEmbedding_eq_of_range_eq composed canonicalPlacement hRange
  intro x
  exact congrArg (fun e : X ↪o V => e x) hEq

/-- The same uniqueness and compatibility hold simultaneously for all
first-wagon edges in a selected contracted M-copy. The local index
type can be empty, and distinct source first wagons may overlap. -/
theorem finite_ordered_selected_coordinates_commute
    {S X W V : Type v}
    [LinearOrder X] [PartialOrder W] [PartialOrder V] [Finite X]
    (sourceCoordinate : S → X ↪o W)
    (selectedVertex : W ↪o V)
    (canonicalPlacement : S → X ↪o V)
    (hCarrier : ∀ s : S,
      Set.range (fun x : X => selectedVertex (sourceCoordinate s x)) =
        Set.range (canonicalPlacement s : X → V)) :
    ∀ s : S, ∀ x : X,
      selectedVertex (sourceCoordinate s x) = canonicalPlacement s x := by
  intro s x
  exact finite_ordered_selected_coordinate_commutes
    (sourceCoordinate s) selectedVertex (canonicalPlacement s)
    (hCarrier s) x

end StructuralRamsey.Girth
