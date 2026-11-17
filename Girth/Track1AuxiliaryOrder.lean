import Girth.TrainRecursiveCutoffTwoTokens
import Girth.DesignatedPicture
import Mathlib.Order.Prod.Lex.Basic

set_option autoImplicit false

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}} {U V W I : Type v}

/-- A common auxiliary order on the old selected copies lifts to the
actual core. The token order breaks ties between different lifts of an
old point, so it has no effect within any one selected copy. -/
theorem CutoffTwoLiftData.exists_auxiliaryOrder_of_original
    {A : RelStructure L U} {B : RelStructure L V} {D : RelStructure L W}
    (C : CutoffTwoLiftData A B D I) [LinearOrder V] [LinearOrder W]
    [Finite C.Vertex] (hOriginal : ∀ i, StrictMono (C.original i)) :
    ∃ o : LinearOrder C.Vertex, ∀ i (x y : V), x < y →
      @LT.lt C.Vertex o.toLT (C.lift i x) (C.lift i y) := by
  classical
  letI : Fintype C.Vertex := Fintype.ofFinite C.Vertex
  let index := Fintype.equivFin C.Vertex
  let key (z : C.Vertex) : W ×ₗ Fin (Fintype.card C.Vertex) :=
    toLex (C.project z, index z)
  let order : LinearOrder C.Vertex :=
    LinearOrder.lift' key (fun _ _ h => index.injective (congrArg (fun p => (ofLex p).2) h))
  refine ⟨order, ?_⟩
  intro i x y hLt
  change key (C.lift i x) < key (C.lift i y)
  exact Prod.Lex.toLex_lt_toLex.mpr (Or.inl (hOriginal i hLt))

/-- Lexicographic ordering by the fine base preserves the full target order
on every selected transversal copy, once its chosen base embedding is
monotone. The tie-breaker is never used within such a copy. -/
theorem exists_auxiliaryOrder_of_monotone_designated_base
    {B : RelStructure L V} {D : RelStructure L W}
    [LinearOrder V] [LinearOrder W] [Finite U]
    (C : StructuralRamsey.Partite.System L W U)
    (family : Set (Embedding B D))
    (hFamily : ∀ b, b ∈ family → StrictMono b) :
    ∃ o : LinearOrder U,
      (∀ x y, C.part x < C.part y → @LT.lt U o.toLT x y) ∧
      (∀ (q : DesignatedCopy B D C family) (x y : V), x < y →
        @LT.lt U o.toLT (q.embedding x) (q.embedding y)) := by
  classical
  letI : Fintype U := Fintype.ofFinite U
  let index := Fintype.equivFin U
  let key (z : U) : W ×ₗ Fin (Fintype.card U) :=
    toLex (C.part z, index z)
  let order : LinearOrder U :=
    LinearOrder.lift' key (fun _ _ h => index.injective (congrArg (fun p => (ofLex p).2) h))
  refine ⟨order, ?_, ?_⟩
  · intro x y h
    change key x < key y
    exact Prod.Lex.toLex_lt_toLex.mpr (Or.inl h)
  · intro q x y h
    change key (q.embedding x) < key (q.embedding y)
    apply Prod.Lex.toLex_lt_toLex.mpr
    left
    change C.part (q.embedding x) < C.part (q.embedding y)
    rw [q.projects x, q.projects y]
    exact hFamily q.base q.base_mem h

#print axioms StructuralRamsey.Girth.CutoffTwoLiftData.exists_auxiliaryOrder_of_original
#print axioms StructuralRamsey.Girth.exists_auxiliaryOrder_of_monotone_designated_base

end StructuralRamsey.Girth
