import Girth.LocalForestPieces
import Girth.ForestImage

/-!
# Small gluing copies lie inside full standard-picture support pieces

The circulation forest-completion induction uses two *different*
hypergraph pieces for each local owner: the small gluing support
image of the active subsystem, and the full standard-picture image
of the entire old picture. The former embeds into the latter, but
they cannot be identified because full pictures have private vertices.

If a small strong-support map factors through the embedding of its
full standard picture, the carrier inclusion and support-edge
inclusion follow from the corresponding source incidences. We keep
the latter explicit, since a source support edge must actually be
an edge of the full old picture.

The exact equality of intersections of DIFFERENT full standard
pictures is a separate free-amalgamation fact; it is not claimed here.
-/

namespace StructuralRamsey.Girth

universe v
variable {Src Old W : Type v}

/-- The image of any source subset under a factored gluing map agrees
with its two-stage image through the active subsystem and the full
standard picture. -/
theorem factorized_support_image
    (outer : Src → W) (active : Src → Old) (standard : Old → W)
    (hFactor : ∀ x : Src, outer x = standard (active x))
    (S : Set Src) :
    outer '' S = standard '' (active '' S) := by
  apply Set.ext
  intro z
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨active x, ⟨x, hx, rfl⟩, (hFactor x).symm⟩
  · rintro ⟨y, ⟨x, hx, hxy⟩, hzy⟩
    refine ⟨x, hx, ?_⟩
    calc
      outer x = standard (active x) := hFactor x
      _ = standard y := congrArg standard hxy
      _ = z := hzy

/-- Every gluing vertex lies in the full standard-picture carrier if
its old active preimage lies in the carrier of the full old piece. -/
theorem StrongSupportEmbedding.supportPiece_carrier_subset_standard
    {H : Set (Set Src)} {K : Set (Set W)}
    (outer : StrongSupportEmbedding H K)
    (active : Src ↪ Old) (standard : Old ↪ W)
    (hFactor : ∀ x : Src, outer x = standard (active x))
    (oldFull : HypergraphPiece Old)
    (hSourceCarrier : ∀ x : Src, active x ∈ oldFull.carrier) :
    outer.supportPiece.carrier ⊆
      (oldFull.map standard).carrier := by
  intro y hy
  change y ∈ Set.range outer at hy
  obtain ⟨x, hxy⟩ := hy
  change y ∈ standard '' oldFull.carrier
  exact ⟨active x, hSourceCarrier x, (hFactor x).symm.trans hxy⟩

/-- Every support edge of a small gluing piece is a support edge
of its full standard picture whenever the corresponding old active
edge is an edge of the full old support piece. -/
theorem StrongSupportEmbedding.supportPiece_edges_subset_standard
    {H : Set (Set Src)} {K : Set (Set W)}
    (outer : StrongSupportEmbedding H K)
    (active : Src ↪ Old) (standard : Old ↪ W)
    (hFactor : ∀ x : Src, outer x = standard (active x))
    (oldFull : HypergraphPiece Old)
    (hSourceEdges :
      ∀ e₀ : Set Src, e₀ ∈ H →
        active '' e₀ ∈ oldFull.edges) :
    outer.supportPiece.edges ⊆
      (oldFull.map standard).edges := by
  intro e he
  obtain ⟨e₀, he₀, hEq⟩ := he
  change ∃ f : Set Old, f ∈ oldFull.edges ∧
    e = standard '' f
  refine ⟨active '' e₀, hSourceEdges e₀ he₀, ?_⟩
  exact hEq.trans
    (factorized_support_image
      (fun x : Src => outer x)
      (fun x : Src => active x)
      (fun x : Old => standard x)
      hFactor e₀)

/-- Combine the exact vertex and edge transport obligations needed by
the two-carrier forest-completion lemma. -/
theorem StrongSupportEmbedding.supportPiece_sub_standard
    {H : Set (Set Src)} {K : Set (Set W)}
    (outer : StrongSupportEmbedding H K)
    (active : Src ↪ Old) (standard : Old ↪ W)
    (hFactor : ∀ x : Src, outer x = standard (active x))
    (oldFull : HypergraphPiece Old)
    (hSourceCarrier : ∀ x : Src, active x ∈ oldFull.carrier)
    (hSourceEdges :
      ∀ e₀ : Set Src, e₀ ∈ H →
        active '' e₀ ∈ oldFull.edges) :
    outer.supportPiece.carrier ⊆ (oldFull.map standard).carrier ∧
      outer.supportPiece.edges ⊆ (oldFull.map standard).edges := by
  exact ⟨outer.supportPiece_carrier_subset_standard
      active standard hFactor oldFull hSourceCarrier,
    outer.supportPiece_edges_subset_standard
      active standard hFactor oldFull hSourceEdges⟩

/-- Support edges of a transported full old picture remain ambient
support edges whenever the full embedding carries each old support
edge into the new support. This is the corresponding hFullEdges
hypothesis in the circulated forest-completion assembly. -/
theorem HypergraphPiece.map_edges_subset_ambient
    (oldFull : HypergraphPiece Old) (standard : Old ↪ W)
    (oldSupport : Set (Set Old)) (ambient : Set (Set W))
    (hOldEdges : oldFull.edges ⊆ oldSupport)
    (hMapEdges : ∀ e₀ ∈ oldSupport, standard '' e₀ ∈ ambient) :
    (oldFull.map standard).edges ⊆ ambient := by
  rintro e ⟨e₀, he₀, rfl⟩
  exact hMapEdges e₀ (hOldEdges he₀)

end StructuralRamsey.Girth
