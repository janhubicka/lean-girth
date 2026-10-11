import Girth.ForestPhysicalRepresentativeRamsey
import Girth.ForestMixedSetBound

/-!
# Exact preservation of the set-valued mixed forest invariant under
# physical representative normalization

Selecting one designated strong support embedding per physical support
piece BEFORE attachment preserves the edge Ramsey arrow (checked in
ForestPhysicalRepresentativeRamsey). It also preserves the bounded
mixed forest property exactly: the SET of actual designated support
pieces is unchanged, and every ambient one-edge piece is unchanged.

This is stronger and cleaner than appealing to heredity under
arbitrary deletion of labelled forest members, which is false in
general. All predicates below are sets of PHYSICAL support pieces,
not duplicates indexed by embedding labels.
-/

namespace StructuralRamsey.Girth

universe v
variable {X Y : Type v}

/-- Choosing one actual local embedding per physical image does not
change the set of physical designated support pieces at all. -/
theorem physicalSupportPieces_representative_range
    {H : Set (Set X)} {K : Set (Set Y)}
    (family : Set (StrongSupportEmbedding H K)) :
    physicalSupportPieces
      (Set.range (physicalSupportRepresentative family)) =
        physicalSupportPieces family := by
  classical
  ext T
  constructor
  · rintro ⟨g, ⟨q, rfl⟩, hPiece⟩
    exact ⟨physicalSupportRepresentative family q,
      (physicalSupportRepresentative_spec family q).1, hPiece⟩
  · rintro ⟨f, hf, hPiece⟩
    let q : PhysicalSupportOwner family :=
      ⟨T, ⟨f, hf, hPiece⟩⟩
    exact ⟨physicalSupportRepresentative family q,
      ⟨q, rfl⟩,
      (physicalSupportRepresentative_spec family q).2⟩

/-- Tested mixed support pieces are exactly the designated PHYSICAL
support pieces, together with the ambient one-edge pieces. -/
def PhysicalMixedSupportTest
    {H : Set (Set X)} {K : Set (Set Y)}
    (family : Set (StrongSupportEmbedding H K))
    (ambientEdges : Set (Set Y))
    (P : HypergraphPiece Y) : Prop :=
  P ∈ physicalSupportPieces family ∨
    ∃ e : Set Y, e ∈ ambientEdges ∧
      P = HypergraphPiece.oneEdge e

/-- Exact tested-piece equivalence under local family normalization. -/
theorem physicalMixedSupportTest_representatives_iff
    {H : Set (Set X)} {K : Set (Set Y)}
    (family : Set (StrongSupportEmbedding H K))
    (ambientEdges : Set (Set Y))
    (P : HypergraphPiece Y) :
    PhysicalMixedSupportTest
      (Set.range (physicalSupportRepresentative family))
      ambientEdges P ↔
    PhysicalMixedSupportTest family ambientEdges P := by
  rw [PhysicalMixedSupportTest, PhysicalMixedSupportTest,
    physicalSupportPieces_representative_range]

/-- Consequently ALL finite mixed forest-through-m assertions for
physical support piece SETS are invariant under this reduction,
without extra cardinal budgets or clone-insertion arguments. -/
theorem finiteMixedForestThrough_physicalRepresentatives_iff
    {H : Set (Set X)} {K : Set (Set Y)}
    (family : Set (StrongSupportEmbedding H K))
    (ambientEdges : Set (Set Y))
    (m : ℕ) :
    FiniteMixedForestThrough
      (PhysicalMixedSupportTest
        (Set.range (physicalSupportRepresentative family))
        ambientEdges) m ↔
    FiniteMixedForestThrough
      (PhysicalMixedSupportTest family ambientEdges) m := by
  have hTest : PhysicalMixedSupportTest
      (Set.range (physicalSupportRepresentative family))
      ambientEdges =
      PhysicalMixedSupportTest family ambientEdges := by
    funext P
    apply propext
    exact physicalMixedSupportTest_representatives_iff
      family ambientEdges P
  rw [hTest]
end StructuralRamsey.Girth
