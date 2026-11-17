import Girth.TypedInterfaceForest

/-!
# Running intersection under a coherent shared-index gluing

This is the *incidence* half of gluing two join trees over a common
connected family of interface members. It is more general than the
single connector of JoinTree.sumBridge:

* left and right families are indexed by overlapping subsets L, R of
  a common global family Q;
* the local join-tree edges are embedded in a specified global tree;
* every ambient vertex appearing on both sides occurs in a member of
  the common index family L ∩ R.

These assumptions imply running intersection for the global family.
The separate graph-theoretic obligation that the union/quotient of the
two trees is a tree is kept EXPLICIT, rather than smuggled into the
incidence argument. No Ramsey or closure conclusion is asserted.
-/

namespace StructuralRamsey.Girth
namespace CoherentPort

universe v
variable {W Q : Type v}

/-- The shared labels contain an occurrence of every physical vertex
that is present on both sides. For a coherent interface this follows
from the marked interface subtree, but not from port-set closedness
alone. -/
def SharedOccurrenceCoverage
    (F : Q → HypergraphPiece W) (L R : Set Q) : Prop :=
  ∀ (x : W),
    (∃ i : L, x ∈ (F i.1).carrier) →
    (∃ j : R, x ∈ (F j.1).carrier) →
    ∃ k : {q : Q // q ∈ L ∩ R}, x ∈ (F k.1).carrier

/-- Transport the local occurrence path from one induced join tree
to any global graph containing all of that tree's labelled edges. -/
theorem reachable_of_embedded_local_joinTree
    (F : Q → HypergraphPiece W)
    (G : SimpleGraph Q)
    (S : Set Q)
    (J : JoinTree (fun i : S => F i.1))
    (hEdges : ∀ (i j : S), J.tree.Adj i j → G.Adj i.1 j.1)
    (x : W) (i j : S)
    (hi : x ∈ (F i.1).carrier)
    (hj : x ∈ (F j.1).carrier) :
    (G.induce {q : Q | x ∈ (F q).carrier}).Reachable
      ⟨i.1, hi⟩ ⟨j.1, hj⟩ := by
  let phi :
      (J.tree.induce {k : S | x ∈ (F k.1).carrier}) →g
        (G.induce {q : Q | x ∈ (F q).carrier}) := {
    toFun := fun k => ⟨k.1.1, k.2⟩
    map_rel' := by
      intro a b hab
      exact hEdges a.1 b.1 hab
  }
  have hPath := (J.running x ⟨i, hi⟩ ⟨j, hj⟩).map phi
  convert hPath using 1 <;> apply Subtype.ext <;> rfl

/-- Coherent shared-index gluing preserves the running-intersection
property. This is the main incidence statement for arbitrary marked
interface subtrees. It remains conditional on the underlying global
graph being a tree; constructing that tree from a quotient is the
separate next lemma. -/
theorem joinTree_of_coherent_shared_indices
    (F : Q → HypergraphPiece W)
    (L R : Set Q)
    (hCover : L ∪ R = Set.univ)
    (JL : JoinTree (fun i : L => F i.1))
    (JR : JoinTree (fun i : R => F i.1))
    (G : SimpleGraph Q)
    (hTree : G.IsTree)
    (hEdgesL : ∀ (i j : L), JL.tree.Adj i j → G.Adj i.1 j.1)
    (hEdgesR : ∀ (i j : R), JR.tree.Adj i j → G.Adj i.1 j.1)
    (hShared : SharedOccurrenceCoverage F L R) :
    JoinTree F := by
  refine ⟨G, hTree, ?_⟩
  intro x a b
  have hA : a.1 ∈ L ∨ a.1 ∈ R := by
    have h : a.1 ∈ L ∪ R := by rw [hCover]; exact Set.mem_univ _
    exact h
  have hB : b.1 ∈ L ∨ b.1 ∈ R := by
    have h : b.1 ∈ L ∪ R := by rw [hCover]; exact Set.mem_univ _
    exact h
  have hLeft (p q : {i : Q // x ∈ (F i).carrier})
      (hp : p.1 ∈ L) (hq : q.1 ∈ L) :
      (G.induce {i : Q | x ∈ (F i).carrier}).Reachable p q := by
    have h := reachable_of_embedded_local_joinTree
      F G L JL hEdgesL x
      ⟨p.1, hp⟩ ⟨q.1, hq⟩ p.2 q.2
    convert h using 1 <;> apply Subtype.ext <;> rfl
  have hRight (p q : {i : Q // x ∈ (F i).carrier})
      (hp : p.1 ∈ R) (hq : q.1 ∈ R) :
      (G.induce {i : Q | x ∈ (F i).carrier}).Reachable p q := by
    have h := reachable_of_embedded_local_joinTree
      F G R JR hEdgesR x
      ⟨p.1, hp⟩ ⟨q.1, hq⟩ p.2 q.2
    convert h using 1 <;> apply Subtype.ext <;> rfl
  have hLeftRight (p q : {i : Q // x ∈ (F i).carrier})
      (hp : p.1 ∈ L) (hq : q.1 ∈ R) :
      (G.induce {i : Q | x ∈ (F i).carrier}).Reachable p q := by
    obtain ⟨k, hk⟩ := hShared x
      ⟨⟨p.1, hp⟩, p.2⟩ ⟨⟨q.1, hq⟩, q.2⟩
    let z : {i : Q // x ∈ (F i).carrier} := ⟨k.1, hk⟩
    exact (hLeft p z hp k.2.1).trans (hRight z q k.2.2 hq)
  rcases hA with haL | haR
  · rcases hB with hbL | hbR
    · exact hLeft a b haL hbL
    · exact hLeftRight a b haL hbR
  · rcases hB with hbL | hbR
    · exact (hLeftRight b a hbL haR).symm
    · exact hRight a b haR hbR

/-- The incidence part of the same theorem automatically respects
a typed interface compatibility policy, once full intersections are
certified separately. -/
theorem typedInterfaceForest_of_coherent_shared_indices
    (F : Q → HypergraphPiece W)
    (compatible : HypergraphPiece W → HypergraphPiece W → Prop)
    (hCompatible : ∀ ⦃i j : Q⦄, i ≠ j → compatible (F i) (F j))
    (L R : Set Q) (hCover : L ∪ R = Set.univ)
    (JL : JoinTree (fun i : L => F i.1))
    (JR : JoinTree (fun i : R => F i.1))
    (G : SimpleGraph Q) (hTree : G.IsTree)
    (hEdgesL : ∀ (i j : L), JL.tree.Adj i j → G.Adj i.1 j.1)
    (hEdgesR : ∀ (i j : R), JR.tree.Adj i j → G.Adj i.1 j.1)
    (hShared : SharedOccurrenceCoverage F L R) :
    TypedInterfaceForest compatible F :=
  ⟨hCompatible,
    joinTree_of_coherent_shared_indices F L R hCover
      JL JR G hTree hEdgesL hEdgesR hShared⟩

end CoherentPort
end StructuralRamsey.Girth
