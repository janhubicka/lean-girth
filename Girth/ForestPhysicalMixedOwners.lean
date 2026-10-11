import Girth.ForestMixedLocalForestBridge
import Girth.ForestMultiEdgeSupport

/-!
# Physical support pieces, not duplicate embedding labels, are the owners

A local Ramsey witness may present the same physical copy by more
than one embedding label.  The manuscript's forest condition is
set-valued: it speaks about distinct actual copies, not arbitrary
lists of their representations.

We can and should index regular gluing owners by their distinct
PHYSICAL HypergraphPiece supports.  Exceptional core edges are
likewise indexed by their distinct actual carrier sets. This makes
injectivity of both owner maps definitional and eliminates any need
to assume that the local family has no duplicate embedding labels.

When the common source has two different edges, every strong image
has at least two support edges, and hence cannot equal an exceptional
one-edge owner.  The honest finite mixed forest-through-m hypothesis
therefore gives precisely the labelled previous-cutoff property used
by the conditional direct forest increment.
-/

namespace StructuralRamsey.Girth

universe v
variable {X Y I : Type v}

/-- The set of distinct PHYSICAL support pieces of a labelled family
of strong support embeddings. -/
def physicalGluingPieces
    {H : Set (Set X)} {K : Set (Set Y)}
    (family : I → StrongSupportEmbedding H K) :
    Set (HypergraphPiece Y) :=
  Set.range (fun i : I => (family i).supportPiece)

/-- Physical regular owners are automatically injectively indexed. -/
theorem physicalGluingPieces_injective
    {H : Set (Set X)} {K : Set (Set Y)}
    (family : I → StrongSupportEmbedding H K) :
    Function.Injective
      (fun q : {P : HypergraphPiece Y // P ∈ physicalGluingPieces family} =>
        q.1) :=
  Subtype.val_injective

/-- Every physically indexed regular owner has more than one support
edge whenever its common source contains two distinct edges. -/
theorem physicalGluingPieces_notOneEdge
    {H : Set (Set X)} {K : Set (Set Y)}
    (family : I → StrongSupportEmbedding H K)
    (e f : Set X)
    (he : e ∈ H) (hf : f ∈ H) (hne : e ≠ f) :
    ∀ q : {P : HypergraphPiece Y // P ∈ physicalGluingPieces family},
      ¬ q.1.IsOneEdge := by
  intro q
  obtain ⟨i, hi⟩ := q.2
  have h : q.1 = (family i).supportPiece := hi.symm
  rw [h]
  exact (family i).supportPiece_notIsOneEdge_of_twoSourceEdges
    e f he hf hne

/-- The exact previous-cutoff local mixed-forest property on
physical regular copies and physical core edge owners.

There is NO injectivity premise for the originally given list of
strong embeddings: duplicates are eliminated by the support-piece
subtype indexing itself. -/
theorem physicalMixedOwners_localForest_of_twoSourceEdges
    {H : Set (Set X)} {K : Set (Set Y)}
    (family : I → StrongSupportEmbedding H K)
    (e f : Set X)
    (he : e ∈ H) (hf : f ∈ H) (hne : e ≠ f)
    (coreEdges : Set (Set Y))
    (tested : HypergraphPiece Y → Prop)
    (hRegularTest :
      ∀ i : I, tested (family i).supportPiece)
    (hCoreTest :
      ∀ ce : Set Y, ce ∈ coreEdges →
        tested (HypergraphPiece.oneEdge ce))
    (m : ℕ)
    (hFinite : FiniteMixedForestThrough tested m) :
    LocalForestThrough
      (mixedOwnerSmall
        (fun q : {P : HypergraphPiece Y // P ∈
            physicalGluingPieces family} => q.1)
        (fun ce : {ce : Set Y // ce ∈ coreEdges} => ce.1)) m := by
  have hRegTest :
      ∀ q : {P : HypergraphPiece Y // P ∈ physicalGluingPieces family},
        tested q.1 := by
    intro q
    obtain ⟨i, hi⟩ := q.2
    rw [hi.symm]
    exact hRegularTest i
  exact localForestThrough_mixedOwners_of_finiteMixed
    (fun q : {P : HypergraphPiece Y // P ∈ physicalGluingPieces family} =>
      q.1)
    (fun ce : {ce : Set Y // ce ∈ coreEdges} => ce.1)
    (physicalGluingPieces_injective family)
    Subtype.val_injective
    (physicalGluingPieces_notOneEdge family e f he hf hne)
    tested m hRegTest
    (fun ce => hCoreTest ce.1 ce.2)
    hFinite

end StructuralRamsey.Girth
