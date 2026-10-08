import Girth.ForestMarkedAllowedIntersections
import Girth.LocalForestPieces
import Mathlib.Tactic

/-!
# Actual strong support copies have finite B-carrier contact certificates

A strong support embedding reflects every ambient edge meeting its image
in at least two vertices. If all ambient edges have at least two
vertices, its induced hypergraph piece is edge-saturated.

Consequently the finite marked carrier-mask criterion applies directly
to a proposed strong support copy and an arbitrary old family of strong
support copies. This discharges the abstract inducedness condition
from the pairwise AllowedIntersection certificate.

It does not settle the global join-tree or history-shape interfaces.
-/

namespace StructuralRamsey.Girth

universe v

/-- Actual strong support embeddings give the edge-saturated pieces
needed for exact allowed-overlap tests. -/
theorem StrongSupportEmbedding.supportPiece_edgesSaturated
    {X Y : Type v} {H : Set (Set X)} {K : Set (Set Y)}
    (f : StrongSupportEmbedding H K)
    (hBig : ∀ e ∈ K, ¬ e.Subsingleton) :
    f.supportPiece.EdgesSaturated K := by
  intro e heK heSubset
  have hRange : e ⊆ Set.range f := heSubset
  have hNotSmall : ¬ (e ∩ Set.range f).Subsingleton := by
    intro hSmall
    apply hBig e heK
    intro x hx y hy
    exact hSmall ⟨hx, hRange hx⟩ ⟨hy, hRange hy⟩
  obtain ⟨e0, he0, hEq⟩ :=
    f.reflect_edge e heK hNotSmall
  exact ⟨e0, he0, hEq⟩

/-- Designated hypergraph pieces arising from an old family of
strong support embeddings. -/
def strongSupportPieces
    {X Y : Type v} {H : Set (Set X)} {K : Set (Set Y)}
    (family : Set (StrongSupportEmbedding H K)) :
    Set (HypergraphPiece Y) :=
  {D | ∃ f ∈ family, D = f.supportPiece}

/-- For a genuinely strong support copy, every vertex is already
a named marked port (labelled by its preimage in the source B-copy).
Under the usual non-singleton support-edge hypothesis, only finitely
many old carrier masks are necessary to check ALL pairwise allowed
intersections against old strong support copies. -/
theorem strongSupport_allAllowed_iff_markedRepresentatives
    {X Y : Type v} [Fintype X]
    {H : Set (Set X)} {K : Set (Set Y)}
    (family : Set (StrongSupportEmbedding H K))
    (f : StrongSupportEmbedding H K)
    (hBig : ∀ e ∈ K, ¬ e.Subsingleton) :
    (∀ g ∈ family, AllowedIntersection f.supportPiece g.supportPiece) ↔
      (∀ R ∈ markedCarrierRepresentatives
          (oldPieceCarriers (strongSupportPieces family))
          (fun x : X => f x),
        NewPieceOverlapAllowed f.supportPiece
          (f.supportPiece.carrier ∩ R)) := by
  have hPorts : f.supportPiece.carrier =
      (fun x : X => f x) '' (Set.univ : Set X) := by
    change Set.range (fun x : X => f x) =
      (fun x : X => f x) '' (Set.univ : Set X)
    simp
  have hNewEdges : f.supportPiece.edges ⊆ K := by
    intro e he
    exact f.supportPiece_edges_in_target he
  have hOldSat :
      ∀ D ∈ strongSupportPieces family,
        D.EdgesSaturated K := by
    intro D hD
    obtain ⟨g, hg, rfl⟩ := hD
    exact g.supportPiece_edgesSaturated hBig
  have hPieces :
      (∀ g ∈ family, AllowedIntersection f.supportPiece g.supportPiece) ↔
        (∀ D ∈ strongSupportPieces family,
          AllowedIntersection f.supportPiece D) := by
    constructor
    · intro hAll D hD
      obtain ⟨g, hg, rfl⟩ := hD
      exact hAll g hg
    · intro hAll g hg
      exact hAll g.supportPiece ⟨g, hg, rfl⟩
  exact hPieces.trans
    (allAllowedIntersections_iff_markedRepresentatives
      K f.supportPiece (strongSupportPieces family)
      (fun x : X => f x) (Set.univ : Set X)
      hPorts hNewEdges hOldSat)

/-- Independent of the number of old strong support copies, at most
one carrier per subset of the source vertex positions is needed. -/
theorem strongSupport_markedRepresentatives_card_le
    {X Y : Type v} [Fintype X]
    {H : Set (Set X)} {K : Set (Set Y)}
    (family : Set (StrongSupportEmbedding H K))
    (f : StrongSupportEmbedding H K) :
    (markedCarrierRepresentatives
       (oldPieceCarriers (strongSupportPieces family))
       (fun x : X => f x)).card ≤ Fintype.card (Finset X) :=
  allowedIntersectionRepresentative_card_le
    (strongSupportPieces family) (fun x : X => f x)

end StructuralRamsey.Girth
