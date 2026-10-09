import Girth.ForestAEdgeFanout
import Girth.ForestTwoCopyGirthFanout

/-!
# Safe picture fanout preserves BOTH forest and Berge-girth invariants

The local free-attachment step of the circulation and successor-tree
programmes needs two independent facts simultaneously:

* the family of intended B-copies, including the fresh private clone,
  still admits a supported running-intersection join tree; and
* the complete ambient A-support edge family retains girth > g.

Both now follow for a prescribed singleton port, and also for one
complete old A-edge provided the old owner has linear intrinsic
support. No ambient vertex finiteness is required.

These are local geometric invariant-preservation statements, not
the global Ramsey arrow or the missing free-ancestral cofinal
history-evaluation theorem.
-/

namespace StructuralRamsey.Girth

universe v
variable {W I : Type v}

/-- A free B-copy clone over one old vertex preserves both the
designated-copy forest and the girth of the full old/new support
union, at every prescribed finite cutoff. -/
theorem twoCopyPort_singleton_fanout_invariants
    [Fintype I] [Nonempty I]
    {Y : I → HypergraphPiece W}
    (hForest : ForestOfCopies Y)
    (p : I) (S : Set W)
    (hPort : S ⊆ (Y p).carrier) (hSmall : S.Subsingleton)
    (H : Set (Set W)) (g : ℕ)
    (hOwnerSupport : (Y p).edges ⊆ H)
    (hGirth : GirthGT H g) :
    ForestOfCopies
      (sumPieces
        (fun i : I => (Y i).map (twoCopyPortLeft S))
        (fun _ : PUnit.{v+1} =>
          (Y p).map (twoCopyPortRight S))) ∧
    GirthGT
      (injectedEdgeFamily (twoCopyPortLeft S) H ∪
        injectedEdgeFamily (twoCopyPortRight S) (Y p).edges) g := by
  constructor
  · exact twoCopyPort_singleton_fanout
      hForest p S hPort hSmall
  · exact twoCopyPort_girth_singleton_fanout
      H (Y p).edges S g hSmall hGirth
      (girthGT_of_subset hOwnerSupport hGirth)

/-- A fresh B-clone over one COMPLETE intrinsic A-edge preserves
both the B-copy forest and ambient A-support girth, provided the
old owner A-support is linear. The chosen A-edge is physically
one and the same edge in both standard pictures. -/
theorem twoCopyPort_Aedge_fanout_invariants
    [Fintype I] [Nonempty I]
    {Y : I → HypergraphPiece W}
    (hForest : ForestOfCopies Y)
    (p : I) (S : Set W)
    (hS : S ∈ (Y p).edges)
    (hLinear : LinearEdgeSet (Y p).edges)
    (H : Set (Set W)) (g : ℕ)
    (hOwnerSupport : (Y p).edges ⊆ H)
    (hGirth : GirthGT H g) :
    ForestOfCopies
      (sumPieces
        (fun i : I => (Y i).map (twoCopyPortLeft S))
        (fun _ : PUnit.{v+1} =>
          (Y p).map (twoCopyPortRight S))) ∧
    GirthGT
      (injectedEdgeFamily (twoCopyPortLeft S) H ∪
        injectedEdgeFamily (twoCopyPortRight S) (Y p).edges) g := by
  constructor
  · exact twoCopyPort_Aedge_fanout
      hForest p S hS hLinear
  · exact twoCopyPort_girth_Aedge_fanout
      H (Y p).edges S g (hOwnerSupport hS) hS
      hGirth (girthGT_of_subset hOwnerSupport hGirth)

end StructuralRamsey.Girth
