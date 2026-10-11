import Girth.LocalForestPieces

/-!
# Support geometry of a genuine A-generated local gluing source

The direct mixed-owner forest increment does NOT need vertex
coverage of the entire FULL standard picture. It needs only
the SMALL local gluing support to be vertex-covered by A-edges.

For a genuine source support H, nonemptiness of H and coverage
of each source vertex by an H-edge transfer immediately through
every strong support embedding into the local core. These are
elementary source-geometry facts, not extra assumptions about the
recursive Ramsey witness or its designated-copy coverage.

The source used in circulation is the A-generated active subsystem,
whose full A-support is vertex-covered. Thus the old proof's
small-gluing separator choices are justified without imposing
support coverage on private full-picture vertices.
-/

namespace StructuralRamsey.Girth

universe v
variable {X Y : Type v}

/-- An image of any genuine source support edge witnesses that the
gluing copy's support-edge family is nonempty. -/
theorem StrongSupportEmbedding.supportPiece_edgesNonempty
    {H : Set (Set X)} {K : Set (Set Y)}
    (f : StrongSupportEmbedding H K)
    (hNonempty : H.Nonempty) :
    f.supportPiece.edges.Nonempty := by
  obtain ⟨e, he⟩ := hNonempty
  exact ⟨f '' e, ⟨e, he, rfl⟩⟩

/-- If every source vertex lies in a source support edge, then every
vertex of the small gluing copy is covered by one of its OWN support
edges. No hypothesis about the other vertices of a standard picture. -/
theorem StrongSupportEmbedding.supportPiece_vertexCovered
    {H : Set (Set X)} {K : Set (Set Y)}
    (f : StrongSupportEmbedding H K)
    (hCover : ∀ x : X, ∃ e : Set X, e ∈ H ∧ x ∈ e) :
    ∀ y : Y, y ∈ f.supportPiece.carrier →
      ∃ e : Set Y, e ∈ f.supportPiece.edges ∧ y ∈ e := by
  intro y hy
  change y ∈ Set.range f at hy
  obtain ⟨x, rfl⟩ := hy
  obtain ⟨e, he, hx⟩ := hCover x
  exact ⟨f '' e, ⟨e, he, rfl⟩, ⟨x, hx, rfl⟩⟩

/-- The small gluing support is contained in the local core
whenever its embedding lands there. -/
theorem StrongSupportEmbedding.supportPiece_carrier_subset_core
    {H : Set (Set X)} {K : Set (Set Y)}
    (f : StrongSupportEmbedding H K)
    (S : Set Y)
    (hRange : Set.range f ⊆ S) :
    f.supportPiece.carrier ⊆ S := by
  exact hRange

end StructuralRamsey.Girth
