import Girth.ForestArbitraryPortPushout
import Girth.ForestAEdgeFanout
import Girth.ForestTwoCopyGirthFanout
import Mathlib.Tactic

/-!
# Safe one-port attachment of a DIFFERENT B-piece to an old B-forest

The explicit clone fanout glues the same source vertex positions.
A general B-forest leaf may use a different vertex (or A-edge) of
its source B-piece from the vertex/edge in the chosen old owner.

Using PortGluing, the new piece is injected over ANY isomorphism
of the chosen old/new port sets. The old forest is transported
as a whole. Its pairwise supported intersections and linearity
force any old member to meet an old owner A-edge either at one
vertex or at that complete edge. The new right piece therefore
has allowed contacts with every old member and is attached as
a dominated join-tree leaf.

The same physical gluing preserves ambient support girth via
the verified singleton/whole-edge Berge gluing lemmas.
This is a local safe construction, not a global successor-history
Ramsey/evaluation theorem.
-/

namespace StructuralRamsey.Girth

universe v
variable {Old New I : Type v}

namespace PortGluing

/-- The image of the new port is exactly the image of the old port,
not merely included in it. -/
theorem newPort_image_eq_oldPort_image
    (G : PortGluing Old New) :
    G.newEmbedding '' G.newPort =
      G.oldEmbedding '' G.oldPort := by
  apply Set.Subset.antisymm
  · rintro z ⟨y, hy, hyz⟩
    exact ⟨(G.identify ⟨y, hy⟩).1,
      (G.identify ⟨y, hy⟩).2,
      (G.agree_on_port hy).trans hyz⟩
  · exact G.oldPort_image_subset_newPort_image

/-- Cross intersections with any old member lie in the image of
the old part of the prescribed port. -/
theorem old_new_inter_subset_member_port
    (G : PortGluing Old New)
    (A : Set Old) (B : Set New) :
    G.oldEmbedding '' A ∩ G.newEmbedding '' B ⊆
      G.oldEmbedding '' (G.oldPort ∩ A) := by
  intro z hz
  obtain ⟨x, hx, hxz⟩ := hz.1
  have hPort :
      z ∈ G.oldEmbedding '' G.oldPort :=
    G.old_new_image_inter_subset_port A B hz
  obtain ⟨y, hyPort, hyz⟩ := hPort
  have hxy : x = y :=
    G.oldEmbedding.injective (hxz.trans hyz.symm)
  have hxPort : x ∈ G.oldPort := by
    rw [hxy]
    exact hyPort
  exact ⟨x, ⟨hxPort, hx⟩, hxz⟩

/-- If the ENTIRE port occurs in both old and new pieces, their
physical carrier intersection is exactly the common port image. -/
theorem old_new_inter_eq_full_port
    (G : PortGluing Old New)
    (A : Set Old) (B : Set New)
    (hOld : G.oldPort ⊆ A)
    (hNew : G.newPort ⊆ B) :
    G.oldEmbedding '' A ∩ G.newEmbedding '' B =
      G.oldEmbedding '' G.oldPort := by
  apply Set.Subset.antisymm
  · exact G.old_new_image_inter_subset_port A B
  · rintro z ⟨x, hx, hxz⟩
    refine ⟨⟨x, hOld hx, hxz⟩, ?_⟩
    have hzNew :
        z ∈ G.newEmbedding '' G.newPort :=
      G.oldPort_image_subset_newPort_image ⟨x, hx, hxz⟩
    obtain ⟨y, hy, hyz⟩ := hzNew
    exact ⟨y, hNew hy, hyz⟩

/-- When the old port meets an old member in at most one vertex,
the corresponding physical old/new pair meets in at most one. -/
theorem allowedIntersection_of_small_port_member
    (G : PortGluing Old New)
    (P : HypergraphPiece Old)
    (N : HypergraphPiece New)
    (hSmall : (G.oldPort ∩ P.carrier).Subsingleton) :
    AllowedIntersection
      (P.map G.oldEmbedding) (N.map G.newEmbedding) := by
  left
  intro z hz t ht
  have hzp : z ∈ G.oldEmbedding '' (G.oldPort ∩ P.carrier) :=
    G.old_new_inter_subset_member_port
      P.carrier N.carrier hz
  have htp : t ∈ G.oldEmbedding '' (G.oldPort ∩ P.carrier) :=
    G.old_new_inter_subset_member_port
      P.carrier N.carrier ht
  obtain ⟨x, hx, hxz⟩ := hzp
  obtain ⟨y, hy, hyt⟩ := htp
  calc
    z = G.oldEmbedding x := hxz.symm
    _ = G.oldEmbedding y := congrArg G.oldEmbedding (hSmall hx hy)
    _ = t := hyt

/-- If an old member contains the WHOLE old A-edge port and the new
piece contains the corresponding complete new A-edge, their
intersection is exactly this single common physical support edge. -/
theorem allowedIntersection_of_shared_full_port
    (G : PortGluing Old New)
    (P : HypergraphPiece Old)
    (N : HypergraphPiece New)
    (hOldEdge : G.oldPort ∈ P.edges)
    (hNewEdge : G.newPort ∈ N.edges) :
    AllowedIntersection
      (P.map G.oldEmbedding) (N.map G.newEmbedding) := by
  right
  let S : Set G.Vertex := G.oldEmbedding '' G.oldPort
  have hCap :
      (P.map G.oldEmbedding).carrier ∩
        (N.map G.newEmbedding).carrier = S :=
    G.old_new_inter_eq_full_port P.carrier N.carrier
      (P.edge_subset hOldEdge) (N.edge_subset hNewEdge)
  refine ⟨S, ?_, ?_, hCap⟩
  · exact ⟨G.oldPort, hOldEdge, rfl⟩
  · exact ⟨G.newPort, hNewEdge,
      (G.newPort_image_eq_oldPort_image).symm⟩

/-- Exact physical dominance of all contacts of one new B-piece
by its chosen old owner. This works for ANY bijection of ports. -/
theorem new_piece_contacts_dominated
    (G : PortGluing Old New)
    (Y : I → HypergraphPiece Old)
    (N : HypergraphPiece New)
    (p i : I)
    (hOwner : G.oldPort ⊆ (Y p).carrier) :
    (N.map G.newEmbedding).carrier ∩
      ((Y i).map G.oldEmbedding).carrier ⊆
    (N.map G.newEmbedding).carrier ∩
      ((Y p).map G.oldEmbedding).carrier := by
  intro z hz
  have hPort : z ∈ G.oldEmbedding '' G.oldPort :=
    G.old_new_image_inter_subset_port
      (Y i).carrier N.carrier ⟨hz.2, hz.1⟩
  obtain ⟨x, hx, hxz⟩ := hPort
  exact ⟨hz.1, ⟨x, hOwner hx, hxz⟩⟩

/-- With an old join-tree forest and a linear chosen owner, any new
B-piece glued by an arbitrary bijection of one permitted vertex or
A-edge port has allowed intersections with EVERY old member. -/
theorem safe_cross_allowed
    [Fintype I] [Nonempty I]
    (G : PortGluing Old New)
    {Y : I → HypergraphPiece Old}
    (hForest : ForestOfCopies Y)
    (p : I) (N : HypergraphPiece New)
    (hOwner : G.oldPort ⊆ (Y p).carrier)
    (hPort :
      G.oldPort.Subsingleton ∨
        (G.oldPort ∈ (Y p).edges ∧ G.newPort ∈ N.edges))
    (hOwnerLinear : LinearEdgeSet (Y p).edges) :
    ∀ i : I, AllowedIntersection
      ((Y i).map G.oldEmbedding) (N.map G.newEmbedding) := by
  intro i
  rcases hPort with hSmall | ⟨hOldEdge, hNewEdge⟩
  · apply G.allowedIntersection_of_small_port_member (Y i) N
    intro x hx y hy
    exact hSmall hx.1 hy.1
  · rcases forest_Aedge_old_member_portClean
        hForest p i G.oldPort hOldEdge hOwnerLinear with hSmall | hWhole
    · exact G.allowedIntersection_of_small_port_member
        (Y i) N hSmall
    · exact G.allowedIntersection_of_shared_full_port
        (Y i) N hWhole hNewEdge

/-- A fresh B-piece, not necessarily isomorphic to the chosen owner
by a port-fixing automorphism, can always be attached over a
permitted singleton or complete-A-edge port to a finite old forest. -/
theorem safe_port_fanout
    [Fintype I] [Nonempty I]
    (G : PortGluing Old New)
    {Y : I → HypergraphPiece Old}
    (hForest : ForestOfCopies Y)
    (p : I) (N : HypergraphPiece New)
    (hOwner : G.oldPort ⊆ (Y p).carrier)
    (hPort :
      G.oldPort.Subsingleton ∨
        (G.oldPort ∈ (Y p).edges ∧ G.newPort ∈ N.edges))
    (hOwnerLinear : LinearEdgeSet (Y p).edges) :
    ForestOfCopies
      (sumPieces
        (fun i : I => (Y i).map G.oldEmbedding)
        (fun _ : PUnit.{v+1} => N.map G.newEmbedding)) := by
  have hOld : ForestOfCopies
      (fun i : I => (Y i).map G.oldEmbedding) :=
    hForest.map G.oldEmbedding
  apply forestOfCopies_attach_dominated
    hOld (N.map G.newEmbedding)
    (G.safe_cross_allowed hForest p N hOwner hPort hOwnerLinear)
    p
  intro i
  exact G.new_piece_contacts_dominated Y N p i hOwner

end PortGluing

end StructuralRamsey.Girth
