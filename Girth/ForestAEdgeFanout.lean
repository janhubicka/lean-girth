import Girth.ForestOnePortFanout
import Girth.ForestReplayObstruction
import Mathlib.Tactic

/-!
# Safe private B-copy fanout over one complete A-edge

The singleton-port fanout already gives a new private B-copy over a
vertex without any additional intersection hypotheses.

For a complete old A-edge S, the same conclusion follows from the
pairwise allowed intersections of the old designated forest together
with linearity of its selected owner P's intrinsic A-support.

Indeed, if another old B-piece meets S in two vertices, then its
allowed intersection with P must be one of P's support edges; by
linearity that edge is S itself. Thus the new private B-clone meets
every old member either at most in one vertex or in exactly the same
complete supported A-edge. The old join tree is extended by attaching
the clone as a leaf to its owner.

No global free-successor history evaluation is asserted here.
-/

namespace StructuralRamsey.Girth

universe v
variable {W I : Type v}

/-- For a linear B-owner in an existing forest, a chosen complete
A-edge of that owner is either almost disjoint from another old
member, or is itself an intrinsic A-edge of that member. -/
theorem forest_Aedge_old_member_portClean
    {Y : I → HypergraphPiece W}
    (hY : ForestOfCopies Y) (p i : I)
    (S : Set W)
    (hS : S ∈ (Y p).edges)
    (hLinear : LinearEdgeSet (Y p).edges) :
    (S ∩ (Y i).carrier).Subsingleton ∨ S ∈ (Y i).edges := by
  by_cases hip : i = p
  · subst i
    exact Or.inr hS
  · have hAllowed : AllowedIntersection (Y i) (Y p) :=
      hY.pairwiseAllowed hip
    rcases hAllowed with hSmall | ⟨f, hfOld, hfOwner, hCap⟩
    · left
      intro x hx y hy
      have hxOwner : x ∈ (Y p).carrier :=
        (Y p).edge_subset hS hx.1
      have hyOwner : y ∈ (Y p).carrier :=
        (Y p).edge_subset hS hy.1
      exact hSmall ⟨hx.2, hxOwner⟩ ⟨hy.2, hyOwner⟩
    · by_cases hEq : S = f
      · right
        simpa only [hEq] using hfOld
      · left
        have hSmall : (S ∩ f).Subsingleton :=
          hLinear hS hfOwner hEq
        intro x hx y hy
        have hxOwner : x ∈ (Y p).carrier :=
          (Y p).edge_subset hS hx.1
        have hyOwner : y ∈ (Y p).carrier :=
          (Y p).edge_subset hS hy.1
        have hxF : x ∈ f := by
          rw [← hCap]
          exact ⟨hx.2, hxOwner⟩
        have hyF : y ∈ f := by
          rw [← hCap]
          exact ⟨hy.2, hyOwner⟩
        exact hSmall ⟨hx.1, hxF⟩ ⟨hy.1, hyF⟩

/-- Exact physical old-left/new-right contact for possibly different
old B-carriers, not merely two copies of the same carrier. -/
theorem twoCopyPort_images_inter_general
    (S A B : Set W) :
    (twoCopyPortLeft S) '' A ∩
      (twoCopyPortRight S) '' B =
      (twoCopyPortLeft S) '' (A ∩ B ∩ S) := by
  apply Set.Subset.antisymm
  · rintro z ⟨⟨x, hxA, hxz⟩, ⟨y, hyB, hyz⟩⟩
    have hCross : twoCopyPortLeft S x = twoCopyPortRight S y :=
      hxz.trans hyz.symm
    obtain ⟨hxy, hxS⟩ :=
      (twoCopyPort_cross_eq_iff S x y).mp hCross
    have hxB : x ∈ B := by simpa only [hxy] using hyB
    exact ⟨x, ⟨⟨hxA, hxB⟩, hxS⟩, hxz⟩
  · rintro z ⟨x, ⟨⟨hxA, hxB⟩, hxS⟩, hxz⟩
    refine ⟨⟨x, hxA, hxz⟩, ⟨x, hxB, ?_⟩⟩
    exact (twoCopyPort_agree_on_separator S hxS).symm.trans hxz

/-- A new private copy over one complete owner A-edge has an allowed
intersection with any old member that either meets the edge in at
most one vertex or contains that same complete supported edge. -/
theorem twoCopyPort_Aedge_cross_allowed
    (Old P : HypergraphPiece W) (S : Set W)
    (hP : S ∈ P.edges)
    (hOld :
      (S ∩ Old.carrier).Subsingleton ∨ S ∈ Old.edges) :
    AllowedIntersection
      (Old.map (twoCopyPortLeft S))
      (P.map (twoCopyPortRight S)) := by
  have hCap :
      (Old.map (twoCopyPortLeft S)).carrier ∩
        (P.map (twoCopyPortRight S)).carrier =
        (twoCopyPortLeft S) '' (Old.carrier ∩ P.carrier ∩ S) := by
    exact twoCopyPort_images_inter_general S Old.carrier P.carrier
  rcases hOld with hSmall | hEdge
  · left
    rw [hCap]
    intro z hz t ht
    obtain ⟨x, hx, hxz⟩ := hz
    obtain ⟨y, hy, hyt⟩ := ht
    have hSmallX : x ∈ S ∩ Old.carrier :=
      ⟨hx.2, hx.1.1⟩
    have hSmallY : y ∈ S ∩ Old.carrier :=
      ⟨hy.2, hy.1.1⟩
    calc
      z = twoCopyPortLeft S x := hxz.symm
      _ = twoCopyPortLeft S y :=
        congrArg (twoCopyPortLeft S) (hSmall hSmallX hSmallY)
      _ = t := hyt
  · right
    have hCapEq :
        Old.carrier ∩ P.carrier ∩ S = S := by
      apply Set.Subset.antisymm
      · exact Set.inter_subset_right
      · intro x hx
        exact ⟨⟨Old.edge_subset hEdge hx, P.edge_subset hP hx⟩, hx⟩
    refine ⟨(twoCopyPortLeft S) '' S, ?_, ?_, ?_⟩
    · exact ⟨S, hEdge, rfl⟩
    · exact ⟨S, hP, twoCopyPort_image_separator S⟩
    · calc
        (Old.map (twoCopyPortLeft S)).carrier ∩
            (P.map (twoCopyPortRight S)).carrier =
          (twoCopyPortLeft S) '' (Old.carrier ∩ P.carrier ∩ S) :=
          hCap
        _ = (twoCopyPortLeft S) '' S := by rw [hCapEq]

/-- Unconditional safe fan-out over any complete owner A-edge of
a linear B-support forest. The right B-copy is new and private off
that edge, and the old forest join tree gains one leaf. -/
theorem twoCopyPort_Aedge_fanout
    [Fintype I] [Nonempty I]
    {Y : I → HypergraphPiece W}
    (hY : ForestOfCopies Y) (p : I)
    (S : Set W)
    (hS : S ∈ (Y p).edges)
    (hLinear : LinearEdgeSet (Y p).edges) :
    ForestOfCopies
      (sumPieces
        (fun i : I => (Y i).map (twoCopyPortLeft S))
        (fun _ : PUnit.{v+1} =>
          (Y p).map (twoCopyPortRight S))) := by
  apply twoCopyPort_fanout_of_allowed hY p S
    ((Y p).edge_subset hS)
  intro i
  exact twoCopyPort_Aedge_cross_allowed (Y i) (Y p) S hS
    (forest_Aedge_old_member_portClean hY p i S hS hLinear)

end StructuralRamsey.Girth
