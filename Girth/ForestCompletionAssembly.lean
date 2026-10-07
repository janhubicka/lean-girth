import Girth.ForestAuxiliaryDeletion
import Girth.ForestJoinLiftLinear
import Girth.CompletionBudget

/-! # Assembly of the circulation forest-completion step

This joins three previously independent combinatorial arguments:

* at a selected local copy, the selected family plus one member for each
  outer tree neighbour fits within the global size bound;
* the outer join tree and local completed forests lift to a single forest;
* deleting all temporary one-edge connectors leaves a forest containing the
  original selected members.

The construction of the local completions, the choice of their designated
B-copy members, and the support geometry of the attachment are separate
inputs.  In particular this is not a proof of the full picture invariant.
-/

namespace StructuralRamsey.Girth

universe v
variable {W Q N : Type v}

/-- Assemble locally completed forests over a join tree, and then discard
all one-edge auxiliary members.  The selected global family remains present
among the retained labels.

The only assumptions on the keep-set are that it retains each selected label
and that all deleted labels carry one-edge pieces; there is no assumption that
arbitrary subfamilies of forests are forests. -/
theorem forestCompletion_assemble
    [Fintype Q] [Nonempty Q] [DecidableEq Q]
    [Fintype N]
    {K : Q → Type v}
    [∀ q, Fintype (K q)] [∀ q, Nonempty (K q)]
    {P : Q → HypergraphPiece W}
    (hOuter : PairwiseAllowed P)
    (JOuter : JoinTree P)
    [DecidableRel JOuter.tree.Adj]
    (hLinear : OuterEdgesLinear P)
    {F : (q : Q) → K q → HypergraphPiece W}
    (hLocalAllowed : ∀ q : Q, PairwiseAllowed (F q))
    (JLocal : ∀ q : Q, JoinTree (F q))
    (hContain :
      ∀ q (k : K q), (F q k).carrier ⊆ (P q).carrier)
    (connector : (q r : Q) → K q)
    (hConnector :
      ∀ ⦃q r : Q⦄, JOuter.tree.Adj q r →
        (P q).carrier ∩ (P r).carrier ⊆
          (F q (connector q r)).carrier)
    (hConnectorEdge :
      ∀ ⦃q r : Q⦄ (hadj : JOuter.tree.Adj q r),
        ¬((P q).carrier ∩ (P r).carrier).Subsingleton →
          (F q (connector q r)).IsOneEdge ∧
          (F q (connector q r)).carrier =
            (P q).carrier ∩ (P r).carrier)
    (owner : N → Q)
    (hSurj : Function.Surjective owner)
    (m : ℕ)
    (hCard : Fintype.card N ≤ m)
    (selected : N → Sigma K)
    (hSelectedOwner : ∀ n : N, (selected n).1 = owner n)
    (keep : Finset (Sigma K))
    (hKeep : ∀ n : N, selected n ∈ keep)
    (hAuxiliary :
      ∀ z : Sigma K, z ∉ keep → (F z.1 z.2).IsOneEdge) :
    (∀ q : Q,
      Fintype.card {n : N // owner n = q} +
        JOuter.tree.degree q ≤ m) ∧
      ForestOfCopies
        (fun z : {z : Sigma K // z ∈ keep} => F z.1.1 z.1.2) ∧
      (∀ n : N,
        ∃ z : {z : Sigma K // z ∈ keep},
          z.1 = selected n ∧ z.1.1 = owner n) := by
  classical
  have hJoined :
      ForestOfCopies (fun z : Sigma K => F z.1 z.2) :=
    forestOfCopies_lift_local_of_linear
      hOuter JOuter hLinear
      hLocalAllowed JLocal hContain
      connector hConnector hConnectorEdge
  have hKept :
      ForestOfCopies
        (fun z : {z : Sigma K // z ∈ keep} => F z.1.1 z.1.2) :=
    hJoined.restrict_of_oneEdge_outside keep hAuxiliary
  refine ⟨?_, hKept, ?_⟩
  · intro q
    exact
      (ownerFiber_card_add_degree_le owner hSurj JOuter.tree q).trans hCard
  · intro n
    exact ⟨⟨selected n, hKeep n⟩, rfl, hSelectedOwner n⟩

end StructuralRamsey.Girth
