import PartiteConstruction.Partite.Operations
import PartiteConstruction.Relational.Homomorphism

set_option autoImplicit false

namespace StructuralRamsey.Partite

open StructuralRamsey.RelStructure

universe u v w p
variable {L : RelLanguage.{u}} {P : Type p} {X : Type v} {U : Type w}

/-- If each relation tuple with two distinct entries is a transversal
edge meeting all fine parts, every nonsingleton irreducible induced
substructure is the carrier of one such tuple. This applies to the
hypergraph reduct with unary predicates and with the within-part
orders kept separately. -/
theorem System.irreducible_eq_range_of_spanning_edge_tuples
    (C : System L P X)
    (hSpans : ∀ (R : L.Symbol) (z : Fin (L.arity R) → X),
      C.rel R z → (∃ i j, z i ≠ z j) → Function.Surjective (C.part ∘ z))
    (S : Set X) (hS : (C.toRelStructure.induce S).Irreducible)
    (hPair : ∃ x y : S, x ≠ y) :
    ∃ (R : L.Symbol) (z : Fin (L.arity R) → X),
      C.rel R z ∧ (∃ i j, z i ≠ z j) ∧ Set.range z = S := by
  have hInjective : Set.InjOn C.part S := by
    intro x hx y hy hpart
    by_contra hxy
    have hSub : (⟨x, hx⟩ : S) ≠ ⟨y, hy⟩ :=
      fun h => hxy (congrArg Subtype.val h)
    obtain ⟨R, z, i, j, hz, hi, hj⟩ := hS hSub
    let w : Fin (L.arity R) → X := Subtype.val ∘ z
    have hi' : w i = x := congrArg Subtype.val hi
    have hj' : w j = y := congrArg Subtype.val hj
    exact hxy (hi'.symm.trans ((C.transversal R w hz i j (by rw [hi', hj', hpart])).trans hj'))
  obtain ⟨x, y, hxy⟩ := hPair
  obtain ⟨R, z, i, j, hz, hi, hj⟩ := hS hxy
  let w : Fin (L.arity R) → X := Subtype.val ∘ z
  have hne : w i ≠ w j := by
    intro h
    exact hxy (hi.symm.trans ((Subtype.ext h).trans hj))
  refine ⟨R, w, hz, ⟨i, j, hne⟩, Set.Subset.antisymm ?_ ?_⟩
  · rintro _ ⟨i, rfl⟩
    exact (z i).property
  · intro x hx
    obtain ⟨i, hi⟩ := hSpans R w hz ⟨i, j, hne⟩ (C.part x)
    exact ⟨i, hInjective (z i).property hx hi⟩

/-- In a vertex-covered fine-partite edge reduct, every irreducible
induced substructure is covered by an actual edge embedding. The empty
induced substructure uses any one edge. No girth bound is needed. -/
theorem System.irreduciblesExtendTo_of_spanning_edge_tuples
    (A : RelStructure L U) (C : System L P X)
    (hSpans : ∀ (R : L.Symbol) (z : Fin (L.arity R) → X),
      C.rel R z → (∃ i j, z i ≠ z j) → Function.Surjective (C.part ∘ z))
    (hTuples : ∀ (R : L.Symbol) (z : Fin (L.arity R) → X),
      C.rel R z → (∃ i j, z i ≠ z j) →
      ∃ e : RelStructure.Embedding A C.toRelStructure,
        Set.range z ⊆ Set.range e)
    (hVertices : ∀ x : X, ∃ e : RelStructure.Embedding A C.toRelStructure,
      x ∈ Set.range e)
    (hNonempty : Nonempty (RelStructure.Embedding A C.toRelStructure)) :
    ∀ S : Set X, (C.toRelStructure.induce S).Irreducible →
      ∃ e : RelStructure.Embedding A C.toRelStructure, S ⊆ Set.range e := by
  intro S hS
  by_cases hPair : ∃ x y : S, x ≠ y
  · obtain ⟨R, z, hz, hne, rfl⟩ := C.irreducible_eq_range_of_spanning_edge_tuples hSpans S hS hPair
    exact hTuples R z hz hne
  · by_cases hS' : S.Nonempty
    · obtain ⟨x, hx⟩ := hS'
      obtain ⟨e, he⟩ := hVertices x
      refine ⟨e, fun y hy => ?_⟩
      have hxy : (⟨x, hx⟩ : S) = ⟨y, hy⟩ :=
        Classical.byContradiction (fun h => hPair ⟨_, _, h⟩)
      have hEq : x = y := congrArg Subtype.val hxy
      exact hEq ▸ he
    · obtain ⟨e⟩ := hNonempty
      exact ⟨e, fun x hx => (hS' ⟨x, hx⟩).elim⟩

/-- The projection of an edge reduct is a homomorphism-embedding when each
edge embedding recovers its source coordinates. The spanning hypothesis
is used only for tuples with two distinct entries. -/
theorem System.edgeReduct_isHomomorphismEmbedding
    (A : RelStructure L P) (C : System L P X)
    (hSpans : ∀ (R : L.Symbol) (z : Fin (L.arity R) → X),
      C.rel R z → (∃ i j, z i ≠ z j) → Function.Surjective (C.part ∘ z))
    (hTuples : ∀ (R : L.Symbol) (z : Fin (L.arity R) → X),
      C.rel R z → (∃ i j, z i ≠ z j) →
      ∃ e : RelStructure.Embedding A C.toRelStructure, Set.range z ⊆ Set.range e)
    (hVertices : ∀ x : X, ∃ e : RelStructure.Embedding A C.toRelStructure,
      x ∈ Set.range e)
    (hNonempty : Nonempty (RelStructure.Embedding A C.toRelStructure))
    (hCoords : ∀ (e : RelStructure.Embedding A C.toRelStructure) (u : P),
      C.part (e u) = u) :
    C.toRelStructure.IsHomomorphismEmbedding A C.part := by
  have cover_tuple (R : L.Symbol) (z : Fin (L.arity R) → X) (hz : C.rel R z) :
      ∃ e : RelStructure.Embedding A C.toRelStructure, Set.range z ⊆ Set.range e := by
    by_cases hDistinct : ∃ i j, z i ≠ z j
    · exact hTuples R z hz hDistinct
    by_cases hIndices : Nonempty (Fin (L.arity R))
    · obtain ⟨i⟩ := hIndices
      obtain ⟨e, he⟩ := hVertices (z i)
      refine ⟨e, ?_⟩
      rintro _ ⟨j, rfl⟩
      have hEq : z j = z i := Classical.byContradiction (fun h => hDistinct ⟨j, i, h⟩)
      rwa [hEq]
    · obtain ⟨e⟩ := hNonempty
      exact ⟨e, fun _ ⟨i, _⟩ => (hIndices ⟨i⟩).elim⟩
  have recover (e : RelStructure.Embedding A C.toRelStructure) {x : X}
      (hx : x ∈ Set.range e) : e (C.part x) = x := by
    obtain ⟨u, rfl⟩ := hx
    rw [hCoords e u]
  constructor
  · intro R z hz
    obtain ⟨e, he⟩ := cover_tuple R z hz
    have hMap : e ∘ (C.part ∘ z) = z := funext (fun i => recover e (he ⟨i, rfl⟩))
    exact (e.map_rel_iff R (C.part ∘ z)).mp (hMap.symm ▸ hz)
  · intro S hS
    obtain ⟨e, he⟩ := C.irreduciblesExtendTo_of_spanning_edge_tuples
      A hSpans hTuples hVertices hNonempty S hS
    refine ⟨{
      toFun := fun x => C.part x.1
      injective := ?_
      map_rel_iff := ?_ }, fun _ => rfl⟩
    · intro x y hxy
      apply Subtype.ext
      exact (recover e (he x.2)).symm.trans ((congrArg e hxy).trans (recover e (he y.2)))
    · intro R z
      have hMap : e ∘ (fun i => C.part (z i).1) = Subtype.val ∘ z :=
        funext (fun i => recover e (he (z i).2))
      change A.rel R (fun i => C.part (z i).1) ↔ C.rel R (Subtype.val ∘ z)
      rw [← hMap]
      exact (e.map_rel_iff R _).symm

end StructuralRamsey.Partite
