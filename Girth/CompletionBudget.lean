import Girth.Forest
import Mathlib.Combinatorics.SimpleGraph.Finite

/-! # Cardinal bookkeeping for local forest completion

At one owner of a join tree, the circulation proof adds one local member for
each incident tree edge.  If every owner is represented by at least one
selected object, those connector members fit inside the original global
cardinality budget.  The statement below isolates exactly that counting step.
-/

namespace StructuralRamsey.Girth

universe v
variable {N Q : Type v}

/-- If `owner : N → Q` is onto, then at any owner `q` the objects already
owned by `q`, together with one connector for every graph neighbour of `q`,
are no more numerous than all objects in `N`.

The graph need not be a tree; looplessness is enough.  In the manuscript the
graph is the join tree on the chosen local copies. -/
theorem ownerFiber_card_add_degree_le
    [Fintype N] [Fintype Q] [DecidableEq Q]
    (owner : N → Q)
    (hSurj : Function.Surjective owner)
    (G : SimpleGraph Q)
    [DecidableRel G.Adj]
    (q : Q) :
    Fintype.card {x : N // owner x = q} + G.degree q ≤
      Fintype.card N := by
  classical
  let rep : Q → N := fun r => Classical.choose (hSurj r)
  have hrep (r : Q) : owner (rep r) = r := by
    exact Classical.choose_spec (hSurj r)
  let f :
      ({x : N // owner x = q} ⊕ G.neighborSet q) → N
    | .inl x => x.1
    | .inr r => rep r.1
  have hf : Function.Injective f := by
    intro a b hab
    cases a with
    | inl x =>
        cases b with
        | inl y =>
            have hxy : x.1 = y.1 := by
              simpa [f] using hab
            exact congrArg Sum.inl (Subtype.ext hxy)
        | inr r =>
            exfalso
            have hxr : x.1 = rep r.1 := by
              simpa [f] using hab
            have hqr : q = r.1 := by
              calc
                q = owner x.1 := x.2.symm
                _ = owner (rep r.1) := congrArg owner hxr
                _ = r.1 := hrep r.1
            exact (G.ne_of_adj r.2) hqr
    | inr r =>
        cases b with
        | inl x =>
            exfalso
            have hrx : rep r.1 = x.1 := by
              simpa [f] using hab
            have hqr : q = r.1 := by
              calc
                q = owner x.1 := x.2.symm
                _ = owner (rep r.1) := (congrArg owner hrx).symm
                _ = r.1 := hrep r.1
            exact (G.ne_of_adj r.2) hqr
        | inr s =>
            have hrs : rep r.1 = rep s.1 := by
              simpa [f] using hab
            have hval : r.1 = s.1 := by
              calc
                r.1 = owner (rep r.1) := (hrep r.1).symm
                _ = owner (rep s.1) := congrArg owner hrs
                _ = s.1 := hrep s.1
            exact congrArg Sum.inr (Subtype.ext hval)
  have hcard := Fintype.card_le_of_injective f hf
  simpa [SimpleGraph.card_neighborSet_eq_degree] using hcard

end StructuralRamsey.Girth
