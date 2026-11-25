import Girth.Forest

/-!
# The bipartite incidence graph of a physical hypergraph piece

A Berge cycle of m edges becomes a simple 2m-cycle in the
bipartite incidence graph. This representation is the natural
common geometric language for gluing over a port with BOTH
physical vertices and shared hyperedge occurrences.

This file supplies the intrinsic incidence graph, with one
edge-node for each *actual support-edge carrier* (not one node per
enumeration occurrence). The exact cycle/BergeCycle correspondence
will be proved separately; the current definitions and incidence
lemmas do not claim it without proof.

In particular, a shared physical support edge is represented
by ONE common edge node in the gluing port, not two differently
coloured private copies. This is essential for avoiding spurious
Berge two-cycles in the boundary-signature scheme.
-/

namespace StructuralRamsey.Girth
namespace BergeIncidence

universe v
variable {W : Type v}

/-- The physical incidence vertex type consists of one tagged
vertex for each actual member of the carrier, and one tagged
edge node for each distinct actual support-edge carrier. -/
abbrev IncidenceNode (P : HypergraphPiece W) :=
  P.carrier ⊕ {e : Set W // e ∈ P.edges}

/-- Bipartite incidence graph. Unlike the coloured occurrence arena,
it remembers only the E-support hypergraph geometry. -/
def graph (P : HypergraphPiece W) : SimpleGraph (IncidenceNode P) where
  Adj a b :=
    match a, b with
    | .inl x, .inr e => x.1 ∈ e.1
    | .inr e, .inl x => x.1 ∈ e.1
    | _, _ => False
  symm := by
    intro a b h
    cases a <;> cases b <;> simpa using h
  loopless := by
    intro a
    cases a <;> simp

/-- Actual incidence is exactly the adjacency of a physical
carrier vertex and a physical support-edge node. -/
@[simp] theorem graph_adj_vertex_edge
    (P : HypergraphPiece W)
    (x : P.carrier) (e : {s : Set W // s ∈ P.edges}) :
    (graph P).Adj (.inl x) (.inr e) ↔ x.1 ∈ e.1 := Iff.rfl

@[simp] theorem graph_adj_edge_vertex
    (P : HypergraphPiece W)
    (x : P.carrier) (e : {s : Set W // s ∈ P.edges}) :
    (graph P).Adj (.inr e) (.inl x) ↔ x.1 ∈ e.1 := Iff.rfl

/-- The two vertex sorts are independent in the bipartite graph. -/
@[simp] theorem graph_no_vertex_vertex
    (P : HypergraphPiece W) (x y : P.carrier) :
    ¬ (graph P).Adj (.inl x) (.inl y) := by
  simp [graph]

/-- Two support-edge nodes are never adjacent without a physical
connector vertex in between. -/
@[simp] theorem graph_no_edge_edge
    (P : HypergraphPiece W)
    (e f : {s : Set W // s ∈ P.edges}) :
    ¬ (graph P).Adj (.inr e) (.inr f) := by
  simp [graph]

/-- Every tagged support-edge node has its actual vertices in the
piece carrier; the piece's incidence structure has no dangling
incidences to outside vertices. -/
theorem edge_node_subset_carrier
    (P : HypergraphPiece W)
    (e : {s : Set W // s ∈ P.edges}) :
    e.1 ⊆ P.carrier :=
  P.edge_subset e.2

end BergeIncidence
end StructuralRamsey.Girth
