import Girth.ForestGeneralPortFanout
import Girth.ForestAEdgeFanoutFromGirth
import Girth.BergeGlue
import Mathlib.Tactic

/-!
# Simultaneous forest and girth preservation for arbitrary port isomorphisms

A new B-piece need not use the same intrinsic A-edge or vertex position
as its old parent. An arbitrary isomorphism of selected old/new port
sets is sufficient for the canonical injective pushout.

For a singleton port, every old/new A-edge intersection is contained
in one physical vertex. For a complete A-support edge on both sides,
all cross-edge intersections lie in that one common physical edge.
The verified Berge-gluing lemmas preserve girth in either case.

Combining these with the general safe-port forest fanout theorem
gives a ONE-STEP preservation result for both local invariants.
Linearity of the old owner follows from ambient girth > g for g >= 2.

The additional assumption that the new piece's support itself has
girth > g is necessary when the new piece is not a clone of the old.
Nothing in this module asserts cofinal Ramsey histories, shape-map
naturality or ownership of unintended ambient decorated A-copies.
-/

namespace StructuralRamsey.Girth

universe v
variable {Old New I : Type v}

namespace PortGluing

/-- The canonical old-port image remains subsingleton whenever the
actual old port contains at most one vertex. -/
theorem old_port_image_subsingleton
    (G : PortGluing Old New)
    (hSmall : G.oldPort.Subsingleton) :
    (G.oldEmbedding '' G.oldPort).Subsingleton := by
  intro x hx y hy
  obtain ⟨a, ha, rfl⟩ := hx
  obtain ⟨b, hb, rfl⟩ := hy
  exact congrArg G.oldEmbedding (hSmall ha hb)

/-- The physical intersection of EVERY old A-edge and EVERY new
A-edge lies in the specified old-port image. -/
theorem injected_edges_cross_subset
    (G : PortGluing Old New)
    (HL : Set (Set Old)) (HR : Set (Set New)) :
    ∀ ⦃eL eR : Set G.Vertex⦄,
      eL ∈ injectedEdgeFamily G.oldEmbedding HL →
      eR ∈ injectedEdgeFamily G.newEmbedding HR →
      eL ∩ eR ⊆ G.oldEmbedding '' G.oldPort := by
  intro eL eR heL heR
  obtain ⟨a, _, rfl⟩ := heL
  obtain ⟨b, _, rfl⟩ := heR
  exact G.old_new_image_inter_subset_port a b

/-- An old/new support union is high-girth after gluing over one
empty or singleton port, for arbitrary old and new vertex types. -/
theorem girth_singleton_port
    (G : PortGluing Old New)
    (HL : Set (Set Old)) (HR : Set (Set New)) (g : ℕ)
    (hSmall : G.oldPort.Subsingleton)
    (hOld : GirthGT HL g)
    (hNew : GirthGT HR g) :
    GirthGT
      (injectedEdgeFamily G.oldEmbedding HL ∪
       injectedEdgeFamily G.newEmbedding HR) g := by
  apply girthGT_union_of_subsingleton_glue
    (S := G.oldEmbedding '' G.oldPort)
    (G.old_port_image_subsingleton hSmall)
    (G.injected_edges_cross_subset HL HR)
    (girthGT_injectedEdgeFamily G.oldEmbedding HL g hOld)
    (girthGT_injectedEdgeFamily G.newEmbedding HR g hNew)

/-- The same girth conclusion holds for an old/new port isomorphism
between COMPLETE A-support edges. The two port edge images
are literally equal in the canonical pushout. -/
theorem girth_Aedge_port
    (G : PortGluing Old New)
    (HL : Set (Set Old)) (HR : Set (Set New)) (g : ℕ)
    (hOldPortEdge : G.oldPort ∈ HL)
    (hNewPortEdge : G.newPort ∈ HR)
    (hOld : GirthGT HL g)
    (hNew : GirthGT HR g) :
    GirthGT
      (injectedEdgeFamily G.oldEmbedding HL ∪
       injectedEdgeFamily G.newEmbedding HR) g := by
  apply girthGT_union_of_edge_glue
    (separator := G.oldEmbedding '' G.oldPort)
  · exact ⟨G.oldPort, hOldPortEdge, rfl⟩
  · exact ⟨G.newPort, hNewPortEdge,
      (G.newPort_image_eq_oldPort_image).symm⟩
  · exact G.injected_edges_cross_subset HL HR
  · exact girthGT_injectedEdgeFamily G.oldEmbedding HL g hOld
  · exact girthGT_injectedEdgeFamily G.newEmbedding HR g hNew

/-- One new B-piece attached over an arbitrary permitted port
isomorphism preserves BOTH the entire intended B-copy forest
and ambient old/new support girth. -/
theorem safe_port_fanout_invariants
    [Fintype I] [Nonempty I]
    (G : PortGluing Old New)
    {Y : I → HypergraphPiece Old}
    (hForest : ForestOfCopies Y)
    (p : I) (N : HypergraphPiece New)
    (hOwner : G.oldPort ⊆ (Y p).carrier)
    (hPort : G.oldPort.Subsingleton ∨
      (G.oldPort ∈ (Y p).edges ∧ G.newPort ∈ N.edges))
    (hLinear : LinearEdgeSet (Y p).edges)
    (H : Set (Set Old)) (g : ℕ)
    (hOwnerSupport : (Y p).edges ⊆ H)
    (hOldGirth : GirthGT H g)
    (hNewGirth : GirthGT N.edges g) :
    ForestOfCopies
      (sumPieces
        (fun i : I => (Y i).map G.oldEmbedding)
        (fun _ : PUnit.{v+1} => N.map G.newEmbedding)) ∧
    GirthGT
      (injectedEdgeFamily G.oldEmbedding H ∪
       injectedEdgeFamily G.newEmbedding N.edges) g := by
  constructor
  · exact G.safe_port_fanout hForest p N hOwner hPort hLinear
  · rcases hPort with hSmall | ⟨hOwnerEdge, hNewEdge⟩
    · exact G.girth_singleton_port H N.edges g
        hSmall hOldGirth hNewGirth
    · exact G.girth_Aedge_port H N.edges g
        (hOwnerSupport hOwnerEdge) hNewEdge
        hOldGirth hNewGirth

/-- In the actual girth-g construction with g >= 2, the old
owner's support is automatically linear. Hence one arbitrary
permitted B-piece birth has a direct two-invariant theorem with
no independent old-owner linearity hypothesis. -/
theorem safe_port_fanout_invariants_of_ambientGirth
    [Fintype I] [Nonempty I]
    (G : PortGluing Old New)
    {Y : I → HypergraphPiece Old}
    (hForest : ForestOfCopies Y)
    (p : I) (N : HypergraphPiece New)
    (hOwner : G.oldPort ⊆ (Y p).carrier)
    (hPort : G.oldPort.Subsingleton ∨
      (G.oldPort ∈ (Y p).edges ∧ G.newPort ∈ N.edges))
    (H : Set (Set Old)) (g : ℕ)
    (hg : 2 ≤ g)
    (hOwnerSupport : (Y p).edges ⊆ H)
    (hOldGirth : GirthGT H g)
    (hNewGirth : GirthGT N.edges g) :
    ForestOfCopies
      (sumPieces
        (fun i : I => (Y i).map G.oldEmbedding)
        (fun _ : PUnit.{v+1} => N.map G.newEmbedding)) ∧
    GirthGT
      (injectedEdgeFamily G.oldEmbedding H ∪
       injectedEdgeFamily G.newEmbedding N.edges) g := by
  have hLinear : LinearEdgeSet (Y p).edges :=
    ownerLinear_of_ambientGirthTwo H (Y p) hOwnerSupport
      (girthGT_mono hOldGirth hg)
  exact G.safe_port_fanout_invariants hForest p N hOwner
    hPort hLinear H g hOwnerSupport hOldGirth hNewGirth

end PortGluing

end StructuralRamsey.Girth
