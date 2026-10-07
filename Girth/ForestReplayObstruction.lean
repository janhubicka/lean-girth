import Girth.ForestCarrierCorner

/-!
# Geometric obstruction to duplicated multi-contact replay

The standalone successor-tree forest draft originally asked for arbitrarily
many private realisations of *every* admissible attachment record.  This is
false for linear hypergraphs: two different support edges cannot contain the
same pair of vertices.  More generally, two pairwise-clean strip copies with
exactly the same old boundary can be repeated privately only when that whole
boundary is subsingleton or is one common support edge.

These are unconditional finite lemmas.  They do not assert a replacement
successor-tree evaluation or the forest partite theorem.
-/

namespace StructuralRamsey.Girth

universe v
variable {W : Type v}

/-- Any two edges of a linear support with two distinct common vertices
must coincide.  This is the basic obstruction to replaying a two-contact
support-edge attachment privately. -/
theorem linearEdge_eq_of_two_shared_vertices
    (E : Set (Set W))
    (hLinear : LinearEdgeSet E)
    {e f : Set W} (he : e ∈ E) (hf : f ∈ E)
    {x y : W} (hxy : x ≠ y)
    (hxe : x ∈ e) (hxf : x ∈ f)
    (hye : y ∈ e) (hyf : y ∈ f) :
    e = f := by
  by_contra hef
  have hSmall : (e ∩ f).Subsingleton :=
    hLinear he hf hef
  exact hxy (hSmall ⟨hxe, hxf⟩ ⟨hye, hyf⟩)

/-- If one replay contains a private vertex not belonging to another,
they cannot both be distinct support edges through the same old vertex
pair in a linear ambient support. -/
theorem no_private_edge_replay_through_two_vertices
    (E : Set (Set W))
    (hLinear : LinearEdgeSet E)
    {e f : Set W} (he : e ∈ E) (hf : f ∈ E)
    {x y z : W} (hxy : x ≠ y)
    (hxe : x ∈ e) (hxf : x ∈ f)
    (hye : y ∈ e) (hyf : y ∈ f)
    (hze : z ∈ e) (hzf : z ∉ f) :
    False := by
  have hef :=
    linearEdge_eq_of_two_shared_vertices E hLinear
      he hf hxy hxe hxf hye hyf
  exact hzf (by simpa [hef] using hze)

/-- Necessary condition for two private copies of one strip whose overlap
is precisely the old boundary κ.  This statement uses the exact
Reiher--Rödl pairwise-clean intersection condition. -/
theorem private_replay_overlap_classification
    (F G : HypergraphPiece W)
    (κ : Set W)
    (hBoundary : F.carrier ∩ G.carrier = κ)
    (hAllowed : AllowedIntersection F G) :
    κ.Subsingleton ∨
      ∃ e : Set W, e ∈ F.edges ∧ e ∈ G.edges ∧ e = κ := by
  rcases hAllowed with hSmall | ⟨e, heF, heG, heEq⟩
  · left
    rw [hBoundary] at hSmall
    exact hSmall
  · right
    exact ⟨e, heF, heG, heEq.symm.trans hBoundary⟩

/-- In particular, if the shared boundary has two distinct vertices but
is not a whole common support edge, a second private replay is impossible. -/
theorem no_private_replay_of_nonedge_boundary
    (F G : HypergraphPiece W)
    (κ : Set W)
    (hBoundary : F.carrier ∩ G.carrier = κ)
    {x y : W} (hx : x ∈ κ) (hy : y ∈ κ) (hxy : x ≠ y)
    (hNotEdge :
      ∀ e : Set W, e ∈ F.edges → e ∈ G.edges → e ≠ κ) :
    ¬ AllowedIntersection F G := by
  intro hAllowed
  rcases private_replay_overlap_classification
      F G κ hBoundary hAllowed with hSmall | ⟨e, heF, heG, heEq⟩
  · exact hxy (hSmall hx hy)
  · exact hNotEdge e heF heG heEq

/-- An incompatibility of *different* two-contact extensions, not just
two repetitions of one record. In one extension the two old vertex pairs
have a common third vertex z; in another their completing edges are
disjoint. Each extension can separately be linear, but no linear support
can contain both over the same old vertices. -/
theorem no_linear_amalgam_of_incompatible_pair_owners
    (E : Set (Set W))
    (hLinear : LinearEdgeSet E)
    {p₁ p₂ q₁ q₂ : Set W}
    (hp₁ : p₁ ∈ E) (hp₂ : p₂ ∈ E)
    (hq₁ : q₁ ∈ E) (hq₂ : q₂ ∈ E)
    {a b c d z : W}
    (hab : a ≠ b) (hcd : c ≠ d)
    (hap₁ : a ∈ p₁) (hbp₁ : b ∈ p₁)
    (haq₁ : a ∈ q₁) (hbq₁ : b ∈ q₁)
    (hcp₂ : c ∈ p₂) (hdp₂ : d ∈ p₂)
    (hcq₂ : c ∈ q₂) (hdq₂ : d ∈ q₂)
    (hzp₁ : z ∈ p₁) (hzp₂ : z ∈ p₂)
    (hQDisjoint : Disjoint q₁ q₂) :
    False := by
  have hPairOne : p₁ = q₁ :=
    linearEdge_eq_of_two_shared_vertices
      E hLinear hp₁ hq₁ hab hap₁ haq₁ hbp₁ hbq₁
  have hPairTwo : p₂ = q₂ :=
    linearEdge_eq_of_two_shared_vertices
      E hLinear hp₂ hq₂ hcd hcp₂ hcq₂ hdp₂ hdq₂
  have hzq₁ : z ∈ q₁ := by
    simpa [hPairOne] using hzp₁
  have hzq₂ : z ∈ q₂ := by
    simpa [hPairTwo] using hzp₂
  exact Set.disjoint_left.mp hQDisjoint hzq₁ hzq₂

end StructuralRamsey.Girth
