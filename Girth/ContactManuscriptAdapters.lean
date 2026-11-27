import Girth.ContactLocalForestPartite
import Girth.ContactBergeWindows

/-! Exact endpoint statements for two elementary manuscript consequences.

The linear ordered seed is the cutoff-two specialization of the checked
local-forest theorem. It includes the restriction to designated copies,
restoration of isolated source vertices, and the compatible part orders.
The wagon consequence uses only the two linearity clauses of a pretrain.
-/

namespace StructuralRamsey.Girth
universe v
variable {V E I P : Type v}

/-- The covered ordered linear seed, including sources with isolated vertices.
The witness carries finite vertices, edges and designated copies; strongly
induced train embeddings preserving order and parts; both vertex and edge
coverage; distinct copy images; and the all-edge Ramsey arrow. Its edges are
explicitly linear. The common edge profile is the usual ordered f-partite
formulation, with arbitrary repetitions of part labels allowed. -/
theorem contactCoveredLinearSeed
    (D : ContactHypergraphData V E I) [Finite V] [Finite E] [Nonempty E]
    [LinearOrder V] [LinearOrder P] [Finite P]
    (part : V → P) (hmono : Monotone part) {a : ℕ} (ha : 2 ≤ a)
    (word : Fin a → P) (enumeration : E → Fin a ↪o V)
    (he : ∀ e, D.edgeCarrier e = Set.range (enumeration e))
    (hw : ∀ e i, part (enumeration e i) = word i)
    (hlin : ∀ e f : E, e ≠ f → (D.edgeCarrier e ∩ D.edgeCarrier f).Subsingleton)
    (Color : Type v) [Finite Color] [Nonempty Color] :
    ∃ W : ContactLocalForestWitness D P part 2 Color,
      ∀ e f : W.Edge, e ≠ f →
        (W.graph.edgeCarrier e ∩ W.graph.edgeCarrier f).Subsingleton := by
  obtain ⟨W⟩ := contactLocalForestPartite D part hmono ha word enumeration he hw
    2 (le_refl 2) (contactLabelledGirthGT_two_of_pairwiseSubsingleton D.edgeCarrier hlin)
    Color
  exact ⟨W,contact_pairwise_of_labelledGirth W.graph.edgeCarrier (le_refl 2) W.girth⟩

namespace OrderOneData
variable (D : OrderOneData V E I P)

/-- Every complete wagon of a linear pretrain is strongly induced: an
ambient edge meeting it at two distinct vertices belongs to that wagon. -/
theorem contact_wagon_strong (hlin : D.ContactLinear) (p : P) (e : E)
    (h : (D.edgeCarrier e ∩ D.contactWagonCarrier p).Nontrivial) :
    D.parent e = p := by
  by_contra hne
  obtain ⟨x,hx,y,hy,hxy⟩ := h
  exact hxy (hlin.2 (D.parent e) p hne
    ⟨⟨e,rfl,hx.1⟩,hx.2⟩ ⟨⟨e,rfl,hy.1⟩,hy.2⟩)

/-- An edge outside a wagon has at most one vertex in the complete wagon
carrier. This is the equivalent intersection formulation of strongness. -/
theorem contact_outside_wagon_intersection_subsingleton
    (hlin : D.ContactLinear) (p : P) (e : E) (hne : D.parent e ≠ p) :
    (D.edgeCarrier e ∩ D.contactWagonCarrier p).Subsingleton := by
  intro x hx y hy
  by_contra hxy
  exact hne (D.contact_wagon_strong hlin p e ⟨x,hx,y,hy,hxy⟩)

end OrderOneData
end StructuralRamsey.Girth
