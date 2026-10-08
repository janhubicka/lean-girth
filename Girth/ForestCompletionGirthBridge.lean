import Girth.ForestCompletionAssembly
import Girth.Berge

/-! # Ambient support girth supplies outer forest linearity

In the circulation completion argument, the outer pieces are designated
copies in one support hypergraph.  Their edges belong to the ambient support
family; girth greater than two makes all those edges linear.  Hence the
linearity assumption of the generic join-tree assembly is not an additional
condition on the local completion witnesses.
-/

namespace StructuralRamsey.Girth

universe v
variable {W Q N : Type v}

/-- Girth above two in a common ambient support hypergraph forces the edges
of all outer pieces to be pairwise linear, including across different pieces. -/
theorem outerEdgesLinear_of_ambient_girth
    {P : Q → HypergraphPiece W}
    {H : Set (Set W)}
    (hEdges :
      ∀ q : Q, ∀ ⦃e : Set W⦄, e ∈ (P q).edges → e ∈ H)
    (hGirth : GirthGT H 2) :
    OuterEdgesLinear P := by
  intro q r e f he hf hne
  exact pairwise_subsingleton_of_girthGT_two
    hGirth (hEdges q he) (hEdges r hf) hne

/-- Assemble local completed forests using an ambient girth bound instead of
a separately supplied outer-edge linearity hypothesis.  All other inputs are
the actual local completion and connector witnesses. -/
theorem forestCompletion_assemble_of_ambient_girth
    [Fintype Q] [Nonempty Q] [DecidableEq Q]
    [Fintype N]
    {K : Q → Type v}
    [∀ q, Fintype (K q)] [∀ q, Nonempty (K q)]
    {P : Q → HypergraphPiece W}
    (hOuter : PairwiseAllowed P)
    (JOuter : JoinTree P)
    [DecidableRel JOuter.tree.Adj]
    {H : Set (Set W)}
    (hEdges :
      ∀ q : Q, ∀ ⦃e : Set W⦄, e ∈ (P q).edges → e ∈ H)
    (hGirth : GirthGT H 2)
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
  exact forestCompletion_assemble
    hOuter JOuter
    (outerEdgesLinear_of_ambient_girth hEdges hGirth)
    hLocalAllowed JLocal hContain connector
    hConnector hConnectorEdge
    owner hSurj m hCard selected
    hSelectedOwner keep hKeep hAuxiliary

end StructuralRamsey.Girth
