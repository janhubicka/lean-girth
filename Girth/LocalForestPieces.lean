import Girth.LocalForestBridge
import Girth.RestrictedForestGirth

/-! # Local forest pieces and partite strong support copies

The hypergraph pieces used to state the local forest theorem are the supports
of its designated strong support embeddings.  Their carriers are exactly the
carriers of the corresponding decorated partite copies.  Transversality then
says that their support edges meet each individual part in at most one vertex.

These identities discharge the carrier and fine-part hypotheses in the
untouched-subsystem girth preservation step.  The forest property itself is
the genuinely combinatorial part of the structural local-forest lemma.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {UA X Y ι : Type v}

/-- Regard one strong support embedding as a hypergraph piece, recording its
entire image carrier and the images of its source support edges. -/
def StrongSupportEmbedding.supportPiece
    {H : Set (Set X)} {K : Set (Set Y)}
    (f : StrongSupportEmbedding H K) : HypergraphPiece Y where
  carrier := Set.range f
  edges := {e | ∃ e₀ : Set X, e₀ ∈ H ∧ e = f '' e₀}
  edge_subset_carrier := by
    intro e he y hy
    rcases he with ⟨e₀, he₀, rfl⟩
    rcases hy with ⟨x, hx, rfl⟩
    exact ⟨x, rfl⟩

@[simp]
theorem StrongSupportEmbedding.supportPiece_carrier
    {H : Set (Set X)} {K : Set (Set Y)}
    (f : StrongSupportEmbedding H K) :
    f.supportPiece.carrier = Set.range f := rfl

/-- Each edge of a strong-support piece is an actual edge of the target
support hypergraph. -/
theorem StrongSupportEmbedding.supportPiece_edges_in_target
    {H : Set (Set X)} {K : Set (Set Y)}
    (f : StrongSupportEmbedding H K)
    {e : Set Y}
    (he : e ∈ f.supportPiece.edges) :
    e ∈ K := by
  rcases he with ⟨e₀, he₀, hEq⟩
  rcases f.map_edge e₀ he₀ with ⟨eK, heK, hMap⟩
  have : e = eK := hEq.trans hMap.symm
  rw [this]
  exact heK

/-- The piece carrier of a designated strong support embedding is the
relational carrier of its decorated partite copy. -/
theorem localForestSupportPiece_carrier_eq_copy
    (A : RelStructure L UA)
    {H : Set (Set X)} {K : Set (Set Y)}
    {partX : X → UA} {partY : Y → UA}
    (hTransH : EdgeTransversal H partX)
    (hTransK : EdgeTransversal K partY)
    (hH : H.Nonempty)
    (hCoverX : ∀ x : X, ∃ e : Set X, e ∈ H ∧ x ∈ e)
    (family : Set (StrongSupportEmbedding H K))
    (hParts :
      ∀ f : StrongSupportEmbedding H K, f ∈ family →
        ∀ x : X, partY (f x) = partX x)
    (q : {f : StrongSupportEmbedding H K // f ∈ family}) :
    q.1.supportPiece.carrier =
      copyCarrier
        ((localForestPartiteCopy A hTransH hTransK hH hCoverX
          family hParts q).toEmbedding) := by
  rfl

/-- A transversal target support hypergraph supplies the precise
one-fine-part condition for any family of its strong-support pieces. -/
theorem strongSupportPieces_meetPartAtMostOne
    {H : Set (Set X)} {K : Set (Set Y)}
    {partY : Y → UA}
    (family : ι → StrongSupportEmbedding H K)
    (hTransK : EdgeTransversal K partY)
    (p : UA) :
    EdgesMeetPartAtMostOne
      (fun i : ι => (family i).supportPiece)
      {y : Y | partY y = p} := by
  intro i e he
  have heK : e ∈ K :=
    (family i).supportPiece_edges_in_target he
  intro x hx y hy
  obtain ⟨w, hw, huniq⟩ := hTransK e heK p
  exact (huniq x ⟨hx.1, hx.2⟩).trans
    (huniq y ⟨hy.1, hy.2⟩).symm

end StructuralRamsey.Girth
