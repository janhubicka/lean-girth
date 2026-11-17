import Girth.TrainCoverageFreeACopyGeometry
import PartiteConstruction.Relational.Order
import PartiteConstruction.Partite.Operations
import Mathlib.Tactic

set_option autoImplicit false
set_option Elab.async false

/-!
# Canonical order BETWEEN fine parts, with within-part orders auxiliary

This is a precise type-level repair of the q=2 ordered
IsPartiteOver mismatch: an unordered A-partite hypergraph can
be expanded by an order relation ONLY between vertices whose
fine parts are strictly increasing. This keeps the same physical
hyperedges and part map; it is *not* the total order within each
fine part, which remains auxiliary until the final finite pass.

The order-expanded structure can have new order-irreducible sets
not contained in a physical A-edge, so full IsPartiteOver is not
claimed. Nevertheless selected partite embeddings automatically
preserve/reflect the canonical cross-part order. Every unordered
physical A-copy whose fine parts agree with its source vertices
extends to an actual ordered A-copy.

This is SOURCE-ONLY and has not been Lean elaborated.
-/

namespace StructuralRamsey.Partite

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}} {P X Y : Type v}

/-- Canonical forward order between fine parts of the SAME
underlying unordered partite structure. No within-part comparisons
are introduced. All old L-relations and physical hyperedges
remain unchanged. -/
def System.crossPartOrder (H : System L P X) [LT P] :
    System L.withOrder P X where
  toRelStructure := {
    rel R := by
      cases R with
      | inl r => exact H.rel r
      | inr _ => exact fun z => H.part (z 0) < H.part (z 1)
  }
  part := H.part
  transversal := by
    intro R z hz i j hPart
    cases R with
    | inl r =>
        change H.rel r z at hz
        exact H.transversal r z hz i j hPart
    | inr _ =>
        change H.part (z 0) < H.part (z 1) at hz
        fin_cases i <;> fin_cases j
        · rfl
        · exact False.elim ((ne_of_lt hz) hPart)
        · exact False.elim ((ne_of_lt hz) hPart.symm)
        · rfl

/-- The canonical cross-part order is forward-compatible by
definition; it requires no order-irreducible coverage. -/
theorem System.crossPartOrder_forwardCompatible
    (H : System L P X) [LT P] :
    StructuralRamsey.Girth.PartiteOrderCompatible H.crossPartOrder := by
  intro z hz
  change H.part (z 0) < H.part (z 1) at hz
  exact hz

/-- A selected partite embedding of the UNORDERED reduct induces
an exact partite embedding of the canonical cross-part order
expansions, preserving AND reflecting that order. -/
def Embedding.crossPartOrder
    (H : System L P X) (K : System L P Y) [LT P]
    (f : Embedding H K) :
    Embedding H.crossPartOrder K.crossPartOrder where
  toEmbedding := {
    toFun := f.toEmbedding.toFun
    injective := f.toEmbedding.injective
    map_rel_iff := by
      intro R z
      cases R with
      | inl r =>
          exact f.toEmbedding.map_rel_iff r z
      | inr _ =>
          change K.part (f (z 0)) < K.part (f (z 1)) ↔
            H.part (z 0) < H.part (z 1)
          simp only [f.map_part]
  }
  map_part := f.map_part

/-- A genuine unordered physical A-edge on its prescribed fine
parts is also an ordered A-edge in the canonical expansion.
No global ordered IsPartiteOver is used. -/
def physicalEdge_to_ordered
    {UA : Type v}
    (A₀ : RelStructure L UA) [LinearOrder UA]
    (H : System L UA X)
    (a : RelStructure.Embedding A₀ H.toRelStructure)
    (hFine : ∀ x : UA, H.part (a x) = x) :
    RelStructure.Embedding A₀.ordered H.crossPartOrder.toRelStructure where
  toFun := a.toFun
  injective := a.injective
  map_rel_iff := by
    intro R z
    cases R with
    | inl r =>
        exact a.map_rel_iff r z
    | inr _ =>
        change H.part (a (z 0)) < H.part (a (z 1)) ↔
          z 0 < z 1
        simp only [hFine]


/-- Forget only the canonical cross-part order, retaining the
literal unordered physical A-embedding and its vertex image. -/
def physicalEdge_to_unordered
    {UA : Type v}
    (A₀ : RelStructure L UA) [LinearOrder UA]
    (H : System L UA X)
    (a : RelStructure.Embedding A₀.ordered
      H.crossPartOrder.toRelStructure) :
    RelStructure.Embedding A₀ H.toRelStructure where
  toFun := a.toFun
  injective := a.injective
  map_rel_iff := by
    intro r z
    exact a.map_rel_iff (.inl r) z

/-- If every unordered A-copy has its prescribed fine colours,
canonical cross-part ordering changes NO physical A-copy.
The inverse literally forgets the new order relation. -/
def physicalEdge_orderedEquiv
    {UA : Type v}
    (A₀ : RelStructure L UA) [LinearOrder UA]
    (H : System L UA X)
    (hFine : ∀ a : RelStructure.Embedding A₀ H.toRelStructure,
      ∀ x : UA, H.part (a x) = x) :
    RelStructure.Embedding A₀ H.toRelStructure ≃
      RelStructure.Embedding A₀.ordered
        H.crossPartOrder.toRelStructure where
  toFun := fun a => physicalEdge_to_ordered A₀ H a (hFine a)
  invFun := fun a => physicalEdge_to_unordered A₀ H a
  left_inv := by
    intro a
    apply RelStructure.Embedding.ext
    intro x
    rfl
  right_inv := by
    intro a
    apply RelStructure.Embedding.ext
    intro x
    rfl

end StructuralRamsey.Partite

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}} {UA P Y : Type v}

/-- A fine cross-part order relabelled along an increasing processed
base A-copy remains compatible with the OLD base part order.
This combines literal cross-part construction with the independently
proved order-relabel theorem, avoiding full IsPartiteOver. -/
theorem canonicalCrossPartOrder_relabel_compatible
    [LT UA] [LT P]
    (H : StructuralRamsey.Partite.System L UA Y)
    (β : UA ↪ P)
    (hβ : ∀ a b : UA, a < b → β a < β b) :
    PartiteOrderCompatible ((H.crossPartOrder).relabel β) :=
  partiteOrderCompatible_of_fineRelabelling
    H.crossPartOrder β hβ H.crossPartOrder_forwardCompatible


/-- The canonical cross-fine-part order does not create or remove
any genuine physical A-support edge. This is stronger than just
preserving selected embeddings and essential for the girth invariants. -/
theorem supportCopies_canonicalCrossPartOrder_eq
    (A₀ : RelStructure L UA) [LinearOrder UA]
    (H : StructuralRamsey.Partite.System L UA Y)
    (hFine : ∀ a : Embedding A₀ H.toRelStructure,
      ∀ x : UA, H.part (a x) = x) :
    supportCopies A₀.ordered (H.crossPartOrder).toRelStructure =
      supportCopies A₀ H.toRelStructure := by
  apply Set.Subset.antisymm
  · rintro E ⟨a, rfl⟩
    exact ⟨StructuralRamsey.Partite.physicalEdge_to_unordered A₀ H a, rfl⟩
  · rintro E ⟨a, rfl⟩
    exact ⟨StructuralRamsey.Partite.physicalEdge_to_ordered A₀ H a (hFine a), rfl⟩

end StructuralRamsey.Girth
