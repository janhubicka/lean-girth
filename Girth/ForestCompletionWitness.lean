import Girth.ForestCompletionGirthBridge

/-! # The designated completion predicate

The circulation invariant asks for more than an abstract forest: each tested
member must survive, and every additional retained member must be an allowed
designated copy.  This records that output condition for a finite labelled
family, separately from the finite choice of local completion witnesses.

The theorem below combines the existing join-tree assembly, deletion of
auxiliary one-edge members, and global girth-based linearity into exactly that
completion predicate.
-/

namespace StructuralRamsey.Girth

universe v
variable {W Q N : Type v}

/-- A labelled completed family is a forest containing every selected piece,
and has no extra members beyond the permitted designated pieces. -/
def ForestCompletionWitness
    {K : Type v} [Fintype K]
    (selected : N → HypergraphPiece W)
    (designated : HypergraphPiece W → Prop)
    (family : K → HypergraphPiece W) : Prop :=
  ForestOfCopies family ∧
    (∀ n : N, ∃ k : K, family k = selected n) ∧
    (∀ k : K,
      (∃ n : N, family k = selected n) ∨ designated (family k))

/-- The abstract forest assembly already supplies a genuine completion
witness, provided the retained labels are either selected or designated.
The ambient support-girth assumption automatically supplies linearity. -/
theorem forestCompletion_witness_of_local_assembly
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
      ∀ z : Sigma K, z ∉ keep → (F z.1 z.2).IsOneEdge)
    (designated : HypergraphPiece W → Prop)
    (hKeptClassify :
      ∀ z : Sigma K, z ∈ keep →
        (∃ n : N, z = selected n) ∨
          designated (F z.1 z.2)) :
    ForestCompletionWitness
      (fun n : N => F (selected n).1 (selected n).2)
      designated
      (fun z : {z : Sigma K // z ∈ keep} => F z.1.1 z.1.2) := by
  classical
  obtain ⟨_hBudget, hForest, hSelected⟩ :=
    forestCompletion_assemble_of_ambient_girth
      hOuter JOuter hEdges hGirth
      hLocalAllowed JLocal hContain
      connector hConnector hConnectorEdge
      owner hSurj m hCard selected
      hSelectedOwner keep hKeep hAuxiliary
  refine ⟨hForest, ?_, ?_⟩
  · intro n
    obtain ⟨z, hz, _hOwner⟩ := hSelected n
    refine ⟨z, ?_⟩
    exact congrArg (fun t : Sigma K => F t.1 t.2) hz
  · intro z
    rcases hKeptClassify z.1 z.2 with ⟨n, hn⟩ | hDesignated
    · left
      refine ⟨n, ?_⟩
      exact congrArg (fun t : Sigma K => F t.1 t.2) hn
    · exact Or.inr hDesignated

end StructuralRamsey.Girth
