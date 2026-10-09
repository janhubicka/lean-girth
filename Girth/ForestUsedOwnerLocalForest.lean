import Girth.ForestUsedOwners
import Girth.Forest

/-!
# Bounded local foresthood only on the used standard-picture owners

The local-forest partite lemma does not assert that its entire Ramsey
witness family is a forest. It asserts that EVERY bounded subfamily of
distinct designated local copies (also allowing ambient one-A-edge pieces)
is a forest.

For the global circulation forest-completion step only the distinct local
B-copy owners of the selected global A/B-pieces are needed. Their index type
is exactly the image of the selected-piece owner map, not the entire local
Ramsey witness family. By surjectivity of that map, this used-owner family
has no more elements than the selected family.

This module isolates the precise reusable restriction theorem. In particular
it does not silently assume that foresthood is hereditary under arbitrary
deletion of members: it explicitly invokes the bounded-subfamily forest
hypothesis on the actual used-owner subfamily.
-/

namespace StructuralRamsey.Girth

universe v
variable {N I W : Type v}

/-- The distinct labelled local copies in every family of size at most m
form a forest. This is the named-copy part of the local-forest partite lemma,
not the stronger and generally false assertion that the whole local
Ramsey witness is a forest. -/
def LocalForestThrough (F : I → HypergraphPiece W) (m : ℕ) : Prop :=
  ∀ (Q : Type v) [Fintype Q] (idx : Q ↪ I),
    Fintype.card Q ≤ m →
      ForestOfCopies (fun q : Q => F (idx q))

/-- The local forest on the distinct owners ACTUALLY USED by the selected
family is available within the original selected-family size budget.
There is no ambient-finiteness assumption on I or W. -/
theorem localForest_usedOwners
    [Fintype N] (owner : N → I)
    (F : I → HypergraphPiece W) (m : ℕ)
    (hLocal : LocalForestThrough F m)
    (hCard : Fintype.card N ≤ m) :
    ForestOfCopies (fun q : UsedOwner owner => F q.1) := by
  classical
  letI : Fintype (UsedOwner owner) := usedOwnerFintype owner
  let incl : UsedOwner owner ↪ I :=
    ⟨Subtype.val, Subtype.val_injective⟩
  have hCount : Fintype.card (UsedOwner owner) ≤ m :=
    (usedOwner_card_le owner).trans hCard
  exact hLocal (UsedOwner owner) incl hCount

/-- Every family of at most m *distinct local copy indices* may be
selected from the local witness; here Q is a previously chosen finite
subfamily rather than the whole local copy family. -/
theorem localForest_of_finite_embedding
    (F : I → HypergraphPiece W)
    (m : ℕ) (hLocal : LocalForestThrough F m)
    {Q : Type v} [Fintype Q]
    (idx : Q ↪ I)
    (hBound : Fintype.card Q ≤ m) :
    ForestOfCopies (fun q : Q => F (idx q)) :=
  hLocal Q idx hBound

end StructuralRamsey.Girth
