import Girth.ForestDistinctLocalRequestJoin

/-!
# Repeated-owner direct forest lifting from the TRUE old q-bound

Combine two ingredients:
(1) the faithful set-valued old mixed forest-through-m property,
with the owner-fiber-plus-tree-degree bound;
(2) the duplicate-free join-tree lift on distinct local request
images, retaining selected labels and deleting only one-edge
separator pieces.

No local clone insertion, no arbitrary subfamily heredity, and
no independent assumption that the local request lists are forests.
The actual picture-step needs to provide the owner assignment and
support geometry, and the local Ramsey witness remains a separate
recursion.
-/

namespace StructuralRamsey.Girth

universe v
variable {W Q N : Type v}

/-- Under one old mixed m-forest property and exact outer gluing
geometry, the selected family is a forest. The only bound needed
is |selected| ≤ m. -/
theorem selectedForest_of_mixedRequestJoin
    [Fintype Q] [Nonempty Q] [DecidableEq Q] [Fintype N]
    {P : Q → HypergraphPiece W}
    (hOuter : PairwiseAllowed P)
    (JOuter : JoinTree P)
    [DecidableRel JOuter.tree.Adj]
    (hLinear : OuterEdgesLinear P)
    (owner : N → Q) (hSurj : Function.Surjective owner)
    (selected : N → HypergraphPiece W)
    (hSelectedInj : Function.Injective selected)
    (separator : (q : Q) → JOuter.tree.neighborSet q → HypergraphPiece W)
    (m : ℕ)
    (hCard : Fintype.card N ≤ m)
    (tested : HypergraphPiece W → Prop)
    (hOld : FiniteMixedForestThrough tested m)
    (hSelectedTest : ∀ n, tested (selected n))
    (hSeparatorTest : ∀ q r, tested (separator q r))
    (hSelectedContain :
      ∀ n, (selected n).carrier ⊆ (P (owner n)).carrier)
    (hSeparatorContain :
      ∀ q r, (separator q r).carrier ⊆ (P q).carrier)
    (hSeparatorOneEdge :
      ∀ q r, (separator q r).IsOneEdge)
    (hSeparatorCover :
      ∀ ⦃q r : Q⦄ (hadj : JOuter.tree.Adj q r),
        (P q).carrier ∩ (P r).carrier ⊆
          (separator q ⟨r, hadj⟩).carrier)
    (hSeparatorExact :
      ∀ ⦃q r : Q⦄ (hadj : JOuter.tree.Adj q r),
        ¬((P q).carrier ∩ (P r).carrier).Subsingleton →
          (separator q ⟨r, hadj⟩).carrier =
            (P q).carrier ∩ (P r).carrier) :
    ForestOfCopies selected := by
  classical
  have hDistinctRequestForest (q : Q) :
      ForestOfCopies
        (fun z : {x : HypergraphPiece W //
          x ∈ finitePieceImage
            (fun t : {n : N // owner n = q} ⊕
                JOuter.tree.neighborSet q =>
              match t with
              | .inl n => selected n.1
              | .inr r => separator q r)} => z.1) :=
    FiniteMixedForestThrough.distinctOwnerRequests
      owner hSurj JOuter.tree m hCard tested hOld
      selected hSelectedTest separator hSeparatorTest q
  exact selectedForest_of_distinctOwnerRequestImages
    hOuter JOuter hLinear owner hSurj selected hSelectedInj
    separator hDistinctRequestForest
    hSelectedContain hSeparatorContain hSeparatorOneEdge
    hSeparatorCover hSeparatorExact

end StructuralRamsey.Girth
