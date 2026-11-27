import Girth.ContactRelationalUnion
import Girth.ContactRawSeed
import Girth.ContactIsolatedPadding
import Girth.ContactGluedOrder

/-! Actual relational input and private restoration. The one-point
label type is a finite quotient of the target, not an assumed finite
language of artificially added unary predicates. -/

namespace StructuralRamsey.Girth
open StructuralRamsey.RelStructure
universe u v
variable {L : RelLanguage.{u}} {U V W F J : Type v}

abbrev ContactDiagonalType (B : RelStructure L V) := Quotient (contactDiagonalSetoid B)

def contactDiagonalLabel (B : RelStructure L V) (x : V) : ContactDiagonalType B :=
  Quotient.mk _ x

theorem contactDiagonalLabel_eq_iff (B : RelStructure L V) (x y : V) :
    contactDiagonalLabel B x = contactDiagonalLabel B y ↔ ContactDiagonalEq B x y :=
  ⟨fun h => @Quotient.exact V (contactDiagonalSetoid B) x y h,
    fun h => @Quotient.sound V (contactDiagonalSetoid B) x y h⟩

theorem contactDiagonalType_finite (B : RelStructure L V) [Finite V] :
    Finite (ContactDiagonalType B) :=
  Finite.of_surjective (contactDiagonalLabel B) (by
    intro q
    induction q using Quotient.inductionOn with
    | h x => exact ⟨x,rfl⟩)

noncomputable def contactDiagonalType_order (B : RelStructure L V) [Finite V] :
    LinearOrder (ContactDiagonalType B) := by
  letI : Finite (ContactDiagonalType B) := contactDiagonalType_finite B
  letI : Fintype (ContactDiagonalType B) := Fintype.ofFinite _
  let e := Fintype.equivFin (ContactDiagonalType B)
  exact LinearOrder.lift' e e.injective

/-- The literal support of the relational target, with isolated
vertices omitted, is a uniform ordered edge-word input. No monotonicity
of the diagonal labels is asserted or used. -/
noncomputable def contactRelationalTrimWord
    (A : RelStructure L U) (B : RelStructure L V)
    [Fintype U] [LinearOrder U] [LinearOrder V]
    (α : Embedding A.ordered B.ordered) :
    ContactOrderedEdgeWord
      (contactRelationalTarget A.ordered B.ordered).trimIsolated
      (ContactDiagonalType B.ordered) (Fintype.card U) := by
  classical
  let D := contactRelationalTarget A.ordered B.ordered
  let k := Fintype.orderIsoFinOfCardEq U rfl
  let f (e : Embedding A.ordered B.ordered) (i : Fin (Fintype.card U)) : D.EdgeVertex :=
    ⟨e (k i),⟨e,⟨k i,rfl⟩⟩⟩
  refine {
    part := fun x => contactDiagonalLabel B.ordered x.val
    word := fun i => contactDiagonalLabel B.ordered (α (k i))
    enumeration := fun e => OrderEmbedding.ofStrictMono (f e)
      (fun i j hij => (Embedding.strictMono e) (k.strictMono hij))
    carrier_eq := ?_
    part_eq := ?_ }
  · intro e
    ext x
    change x.val ∈ Set.range e ↔ x ∈ Set.range (f e)
    constructor
    · rintro ⟨y,hy⟩
      refine ⟨k.symm y,Subtype.ext ?_⟩
      change e (k (k.symm y)) = x.val
      rw [k.apply_symm_apply]
      exact hy
    · rintro ⟨i,rfl⟩
      exact ⟨k i,rfl⟩
  · intro e i
    apply (contactDiagonalLabel_eq_iff B.ordered _ _).mpr
    intro R
    exact (e.map_rel_iff R (fun _ => k i)).trans
      (α.map_rel_iff R (fun _ => k i)).symm

end StructuralRamsey.Girth
