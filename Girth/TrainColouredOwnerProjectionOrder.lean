import Girth.TrainColouredOwnerSelectedLift
import Mathlib.Order.Prod.Lex.Basic

set_option Elab.async false

/-!
# A single projection-first order for every owner-split selected copy

The physical owner split labels each forbidden-predicate incidence
by its original vertex and actual old physical edge. The projection
to original vertices is already checked, including on the isolated
bottom tag of a forbidden source vertex.

On finite split vertex types, order by the old vertex first and an
arbitrary distinct tie-breaker second. This is a genuine linear
order on ALL split vertices, not a separately selected ordering
for each source copy. Whenever old vertices x<y, every split
vertex over x precedes every split vertex over y.

Hence the already checked lift of any originally ordered selected
source copy is strictly monotone for this common order, since
projection composed with that lift equals its old embedding.
Unary predicate preservation is literal under projection. No
output ordered embedding or order-compatibility premise is assumed.

This settles the order component of the owner-incidence splitting
lemma. Full induced relational selected-copy construction and
its coloured Ramsey arrow still require packaging with the
exact physical-edge and strongness lemmas.
-/

namespace StructuralRamsey.Girth

universe v

namespace ColouredEdgeOwnerSplit

variable {V I : Type v} (H : ColouredEdgeOwnerSplit V I)

/-- The original unary predicate survives every owner token and
the actual lift of any genuinely selected source vertex. -/
theorem selectedLift_preserves_predicate {W : Type v}
    (S : ColouredOwnerSelectedCopy (W := W) H) (w : W) :
    H.newPredicate (S.lift w) = H.predicate (S.embedding w) := by
  simp only [ColouredEdgeOwnerSplit.newPredicate, S.project_lift]

/-- One global finite projection-first linear order exists on ALL
split vertices. The second key is only a tie-breaker; the order
strictly refines the original order of distinct projections. -/
theorem exists_projectionFirstLinearOrder
    [LinearOrder V] [Finite H.Vertex] :
    ∃ o : LinearOrder H.Vertex,
      ∀ x y : H.Vertex,
        H.project x < H.project y →
          @LT.lt H.Vertex o.toLT x y := by
  classical
  letI : Fintype H.Vertex := Fintype.ofFinite _
  let key : H.Vertex → V ×ₗ Fin (Fintype.card H.Vertex) :=
    fun x => toLex (H.project x, Fintype.equivFin H.Vertex x)
  have hInjective : Function.Injective key := by
    intro x y h
    exact (Fintype.equivFin H.Vertex).injective
      (congrArg (fun p => (ofLex p).2) h)
  let o : LinearOrder H.Vertex := LinearOrder.lift' key hInjective
  refine ⟨o, ?_⟩
  intro x y hProj
  change key x < key y
  exact Prod.Lex.toLex_lt_toLex.mpr (Or.inl hProj)

/-- For any of the genuinely selected source embeddings, the same
projection-first order makes the actual lifted vertex map strictly
monotone. This preserves the global old order, hence all within-
predicate orders, simultaneously for every selected copy. -/
theorem selectedLift_strictMono_of_projectionFirst
    [LinearOrder V] {W : Type v} [LinearOrder W]
    (S : ColouredOwnerSelectedCopy (W := W) H)
    (o : LinearOrder H.Vertex)
    (hProj : ∀ x y : H.Vertex,
      H.project x < H.project y →
        @LT.lt H.Vertex o.toLT x y)
    (hOldMono : StrictMono S.embedding)
    (x y : W) (hxy : x < y) :
    @LT.lt H.Vertex o.toLT (S.lift x) (S.lift y) := by
  apply hProj
  simpa only [S.project_lift] using hOldMono hxy

end ColouredEdgeOwnerSplit
end StructuralRamsey.Girth
