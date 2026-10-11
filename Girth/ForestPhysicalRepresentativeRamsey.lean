import Girth.ForestPhysicalMixedOwners
import Girth.LocalCoveredWitnessReduction

/-!
# Deduplicate local gluing embeddings by their PHYSICAL support pieces

The induced picture attaches a fresh copy of the old picture for each
designated local embedding. Two different embedding labels can have
the SAME physical image/support (for example, due to a source
automorphism). They must not be silently identified after full
standard pictures have already been attached: those standard copies
can have different private vertices.

Instead, BEFORE performing the picture construction, choose exactly
one genuine designated embedding for each distinct physical support
piece. The retained family is a subset of the original family.
Every physical support piece occurs exactly once, and the edge-Ramsey
arrow survives: a monochromatic image has its entire support-edge
family monochromatic, independent of which source embedding presents
it. This gives the correct normalization needed for the mixed-owner
direct forest increment.

The theorem is about EDGE colourings, as intended in the first stage
of the girth project. It neither quotients existing full-standard
pictures nor assumes source-embedding labels are injective.
-/

namespace StructuralRamsey.Girth

universe v w
variable {X Y : Type v}

/-- The actual support pieces of the original designated copy family. -/
def physicalSupportPieces
    {H : Set (Set X)} {K : Set (Set Y)}
    (family : Set (StrongSupportEmbedding H K)) :
    Set (HypergraphPiece Y) :=
  {P | ∃ f : StrongSupportEmbedding H K,
    f ∈ family ∧ f.supportPiece = P}

/-- A physical support piece together with a certificate that it is
realized by an actual designated local strong embedding. -/
def PhysicalSupportOwner
    {H : Set (Set X)} {K : Set (Set Y)}
    (family : Set (StrongSupportEmbedding H K)) :=
  {P : HypergraphPiece Y // P ∈ physicalSupportPieces family}

/-- Select one GENUINE designated embedding, before attachment, for
each physical support piece. -/
noncomputable def physicalSupportRepresentative
    {H : Set (Set X)} {K : Set (Set Y)}
    (family : Set (StrongSupportEmbedding H K))
    (q : PhysicalSupportOwner family) :
    StrongSupportEmbedding H K :=
  Classical.choose q.2

/-- The chosen embedding was actually in the original Ramsey family,
and its complete support piece is exactly the physical owner. -/
theorem physicalSupportRepresentative_spec
    {H : Set (Set X)} {K : Set (Set Y)}
    (family : Set (StrongSupportEmbedding H K))
    (q : PhysicalSupportOwner family) :
    physicalSupportRepresentative family q ∈ family ∧
      (physicalSupportRepresentative family q).supportPiece = q.1 :=
  Classical.choose_spec q.2

/-- Different physical support owners have different chosen maps. -/
theorem physicalSupportRepresentative_injective
    {H : Set (Set X)} {K : Set (Set Y)}
    (family : Set (StrongSupportEmbedding H K)) :
    Function.Injective (physicalSupportRepresentative family) := by
  intro p q hRep
  apply Subtype.ext
  calc
    p.1 = (physicalSupportRepresentative family p).supportPiece :=
      (physicalSupportRepresentative_spec family p).2.symm
    _ = (physicalSupportRepresentative family q).supportPiece :=
      congrArg StrongSupportEmbedding.supportPiece hRep
    _ = q.1 := (physicalSupportRepresentative_spec family q).2

/-- The normalized representative family is literally a subset of
the given designated family, with one label per physical support. -/
theorem physicalSupportRepresentative_range_subset
    {H : Set (Set X)} {K : Set (Set Y)}
    (family : Set (StrongSupportEmbedding H K)) :
    Set.range (physicalSupportRepresentative family) ⊆ family := by
  rintro f ⟨q, rfl⟩
  exact (physicalSupportRepresentative_spec family q).1

/-- Every physical support piece is still represented, exactly, after
choosing one embedding per physical copy. -/
theorem physicalSupportRepresentative_surjective_support
    {H : Set (Set X)} {K : Set (Set Y)}
    (family : Set (StrongSupportEmbedding H K)) :
    ∀ f : StrongSupportEmbedding H K, f ∈ family →
      ∃ q : PhysicalSupportOwner family,
        (physicalSupportRepresentative family q).supportPiece =
          f.supportPiece := by
  intro f hf
  refine ⟨⟨f.supportPiece, ⟨f, hf, rfl⟩⟩, ?_⟩
  exact (physicalSupportRepresentative_spec family _).2

/-- The local EDGE-Ramsey arrow survives replacing all designated
embeddings by one genuine representative per physical support piece.
The same colour is constant on every image support edge, regardless
of how the source coordinates enumerate those edges. -/
theorem strongSupportEdgeArrow_physicalRepresentatives
    {H : Set (Set X)} {K : Set (Set Y)}
    (family : Set (StrongSupportEmbedding H K))
    (κ : Type w)
    (hArrow : StrongSupportEdgeArrow H family κ) :
    StrongSupportEdgeArrow H
      (Set.range (physicalSupportRepresentative family)) κ := by
  classical
  intro χ
  obtain ⟨f, hf, c, hMono⟩ := hArrow χ
  let q : PhysicalSupportOwner family :=
    ⟨f.supportPiece, ⟨f, hf, rfl⟩⟩
  let g := physicalSupportRepresentative family q
  have hSupport : g.supportPiece = f.supportPiece :=
    (physicalSupportRepresentative_spec family q).2
  refine ⟨g, ⟨q, rfl⟩, c, ?_⟩
  intro e he
  have hImage : g '' e ∈ f.supportPiece.edges := by
    rw [← hSupport]
    exact ⟨e, he, rfl⟩
  obtain ⟨eOld, heOld, hEq⟩ := hImage
  have hMonoOld : χ ⟨f '' eOld, f.mappedEdge_mem eOld heOld⟩ = c :=
    hMono eOld heOld
  have hSubtypeEq :
      (⟨g '' e, g.mappedEdge_mem e he⟩ : K) =
        ⟨f '' eOld, f.mappedEdge_mem eOld heOld⟩ :=
    Subtype.ext hEq
  rw [hSubtypeEq]
  exact hMonoOld

end StructuralRamsey.Girth
