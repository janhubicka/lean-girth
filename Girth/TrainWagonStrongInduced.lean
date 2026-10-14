import Girth.TrainSimultaneousSupreme

/-!
# Circulation: wagon strong inducedness from pretrain linearity

A linear pretrain has a linear family of ambient physical edges and
a linear family of wagon vertex carriers. Hence an ambient edge that
meets one wagon in two distinct vertices cannot belong to a different
wagon: its own wagon would then have a two-vertex intersection.

This is the direct one-line geometric argument used in the circulation
cycle invariant, with no system-girth or appendix input.
-/

namespace StructuralRamsey.Girth.OrderOneData

universe v
variable {V E I P : Type v} (D : OrderOneData V E I P)

/-- Two vertices of an ambient edge in one wagon force the entire
ambient edge to belong to that wagon. -/
theorem parent_eq_of_two_vertices_in_wagon
    (hLinear : D.LinearPretrain)
    (e : E) (w : P) (x y : V)
    (hxe : x ∈ D.edgeCarrier e)
    (hye : y ∈ D.edgeCarrier e)
    (hxw : D.WagonVertex w x)
    (hyw : D.WagonVertex w y)
    (hxy : x ≠ y) :
    D.parent e = w := by
  by_contra hne
  have hInter :=
    hLinear.2 (D.parent e) w hne
  have hxOwn : D.WagonVertex (D.parent e) x :=
    ⟨e, rfl, hxe⟩
  have hyOwn : D.WagonVertex (D.parent e) y :=
    ⟨e, rfl, hye⟩
  exact hxy (hInter ⟨hxOwn, hxw⟩ ⟨hyOwn, hyw⟩)

/-- In particular an edge not belonging to a wagon can meet its
complete vertex carrier in at most one vertex. -/
theorem outside_edge_intersection_subsingleton
    (hLinear : D.LinearPretrain)
    (e : E) (w : P) (hne : D.parent e ≠ w) :
    (D.edgeCarrier e ∩ {x : V | D.WagonVertex w x}).Subsingleton := by
  intro x hx y hy
  by_contra hxy
  exact hne (D.parent_eq_of_two_vertices_in_wagon
    hLinear e w x y hx.1 hy.1 hx.2 hy.2 hxy)

end StructuralRamsey.Girth.OrderOneData
