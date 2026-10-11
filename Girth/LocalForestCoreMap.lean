import Girth.LocalForestPieces
import Girth.ForestImage

/-! # Mapping the gluing support forest into the attached picture

The local witness lives on its own vertex type. Its support-embedding pieces
can be carried into the final picture by the injective core embedding.
There is no need to prove that the composite map is strong relative to every
new support edge of the whole picture: the hypergraph-piece forest itself,
nonempty edge families, and vertex coverage simply transport along the core
injection.
-/

namespace StructuralRamsey.Girth

universe v
variable {X Y Z Q : Type v}

/-- The image of a nonempty strong-support piece remains nonempty as a
support-edge family. -/
theorem StrongSupportEmbedding.mapped_supportPiece_edges_nonempty
    {H : Set (Set X)} {K : Set (Set Y)}
    (f : StrongSupportEmbedding H K)
    (hH : H.Nonempty)
    (core : Y ↪ Z) :
    ((f.supportPiece).map core).edges.Nonempty := by
  rcases hH with ⟨e, he⟩
  refine ⟨core '' (f '' e), ?_⟩
  exact ⟨f '' e, ⟨e, he, rfl⟩, rfl⟩

/-- Every vertex of a mapped strong-support piece lies in a mapped support
edge, provided the source support hypergraph covers its vertices. -/
theorem StrongSupportEmbedding.mapped_supportPiece_vertex_covered
    {H : Set (Set X)} {K : Set (Set Y)}
    (f : StrongSupportEmbedding H K)
    (hCover : ∀ x : X, ∃ e : Set X, e ∈ H ∧ x ∈ e)
    (core : Y ↪ Z)
    (z : Z)
    (hz : z ∈ ((f.supportPiece).map core).carrier) :
    ∃ e : Set Z, e ∈ ((f.supportPiece).map core).edges ∧
      z ∈ e := by
  rcases hz with ⟨y, hy, rfl⟩
  change y ∈ Set.range f at hy
  rcases hy with ⟨x, rfl⟩
  obtain ⟨e, he, hx⟩ := hCover x
  refine ⟨core '' (f '' e), ?_, ?_⟩
  · exact ⟨f '' e, ⟨e, he, rfl⟩, rfl⟩
  · exact ⟨f x, ⟨x, hx, rfl⟩, rfl⟩

/-- A forest of small strong-support copies in the local witness maps to a
forest of gluing support pieces in the full attached picture. -/
theorem strongSupportForest_map_core
    {H : Set (Set X)} {K : Set (Set Y)}
    (family : Q → StrongSupportEmbedding H K)
    (hForest :
      ForestOfCopies (fun q : Q => (family q).supportPiece))
    (core : Y ↪ Z) :
    ForestOfCopies
      (fun q : Q => ((family q).supportPiece).map core) :=
  hForest.map core

end StructuralRamsey.Girth
