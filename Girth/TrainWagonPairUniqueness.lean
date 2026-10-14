import Girth.TrainWagonStrongInduced

/-!
# Circulation: a vertex pair determines its wagon

The four-occurrence detour in the two-standard-copy lemma can be
replaced by the old wagon linearity: two different wagons cannot BOTH
contain two different vertices x,y. In particular, the wagon in any
long supreme piece between x and y must equal any already known old
wagon through that pair.

This certifies only the INTRINSIC old-wagon geometry. Transport to
generated output quotient wagons belongs to the separate actual
picture-step construction. No appendix is used.
-/

namespace StructuralRamsey.Girth.OrderOneData

universe v
variable {V E I P : Type v} (D : OrderOneData V E I P)

/-- Two different vertices cannot lie together in two distinct
wagons of a linear pretrain. In particular, an old wagon passing
through an ordered pair is unique. -/
theorem wagon_eq_of_common_vertex_pair
    (hLinear : D.LinearPretrain)
    (p q : P) (x y : V)
    (hpx : D.WagonVertex p x) (hpy : D.WagonVertex p y)
    (hqx : D.WagonVertex q x) (hqy : D.WagonVertex q y)
    (hxy : x ≠ y) : p = q := by
  by_contra hpq
  have hInter := hLinear.2 p q hpq
  exact hxy (hInter ⟨hpx, hqx⟩ ⟨hpy, hqy⟩)

/-- If x,y already lie in an old wagon p, any long piece of an
arbitrary label between them MUST use two distinct source edges
whose parent wagon is exactly p. This is a direct replacement for
the unnecessary four-occurrence cycle in the intrinsic step. -/
theorem longPiece_edges_in_given_wagon
    (hLinear : D.LinearPretrain)
    (a : I ⊕ E) (p : P) (x y : V)
    (hpx : D.WagonVertex p x) (hpy : D.WagonVertex p y)
    (hxy : x ≠ y)
    (hLong : D.LongPiece a (.inl x) (.inl y)) :
    ∃ e f : E,
      e ∈ D.edges a ∧ f ∈ D.edges a ∧ e ≠ f ∧
      D.parent e = p ∧ D.parent f = p ∧
      x ∈ D.edgeCarrier e ∧ y ∈ D.edgeCarrier f ∧
      ¬ D.PairEdge x y := by
  rcases hLong with ⟨xx, yy, w, e, f, hxx, hyy, he, hf,
    hef, hew, hfw, hxe, hyf, hNonedge⟩
  have hxx' : xx = x := (Sum.inl.inj hxx).symm
  have hyy' : yy = y := (Sum.inl.inj hyy).symm
  subst xx
  subst yy
  have hwx : D.WagonVertex w x := ⟨e, hew, hxe⟩
  have hwy : D.WagonVertex w y := ⟨f, hfw, hyf⟩
  have hwp : w = p :=
    D.wagon_eq_of_common_vertex_pair hLinear
      w p x y hwx hwy hpx hpy hxy
  exact ⟨e, f, he, hf, hef, hew.trans hwp,
    hfw.trans hwp, hxe, hyf, hNonedge⟩

end StructuralRamsey.Girth.OrderOneData
