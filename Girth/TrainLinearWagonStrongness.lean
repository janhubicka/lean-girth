import Girth.TrainSimultaneousSupreme

/-!
# Circulation: linear pretrains have strongly induced wagons

A wagon carrier is the union of all physical edge carriers labelled
by that wagon. If an outside edge meets a wagon in two distinct
vertices, those vertices belong to two distinct wagon carriers,
contradicting the linear intersection parameter.

This is the elementary observation at the start of the circulation
cycle section and is useful when projecting acceptable cycles into
a strongly induced old/core wagon.

No appendix theorem or higher-order system-girth argument is used.
-/

namespace StructuralRamsey.Girth.OrderOneData

universe v
variable {V E I P : Type v}

/-- Distinct wagon carriers cannot share the two vertices of an
actual edge. Consequently any edge meeting a wagon twice belongs
to that same wagon. -/
theorem edge_parent_eq_of_two_wagon_vertices
    (D : OrderOneData V E I P)
    (hLinear : D.LinearPretrain)
    (e : E) (p : P) (x y : V)
    (hxy : x ≠ y)
    (hxe : x ∈ D.edgeCarrier e)
    (hye : y ∈ D.edgeCarrier e)
    (hxp : D.WagonVertex p x)
    (hyp : D.WagonVertex p y) :
    D.parent e = p := by
  by_contra hne
  have hSub :
      ({z : V | D.WagonVertex (D.parent e) z} ∩
        {z : V | D.WagonVertex p z}).Subsingleton :=
    hLinear.2 (D.parent e) p hne
  have hx :
      x ∈ ({z : V | D.WagonVertex (D.parent e) z} ∩
        {z : V | D.WagonVertex p z}) :=
    ⟨⟨e, rfl, hxe⟩, hxp⟩
  have hy :
      y ∈ ({z : V | D.WagonVertex (D.parent e) z} ∩
        {z : V | D.WagonVertex p z}) :=
    ⟨⟨e, rfl, hye⟩, hyp⟩
  exact hxy (hSub hx hy)

end StructuralRamsey.Girth.OrderOneData
