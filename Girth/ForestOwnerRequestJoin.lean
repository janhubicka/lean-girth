import Girth.ForestSigmaAuxDeletion
import Girth.ForestJoinLiftLinear
import Girth.ForestCompletionSeparatorRequests

/-!
# The repeated-owner join-tree assembly without completions

Given a forest of the actual used FULL standard pictures, take the
old-picture local forest on each owner consisting exactly of selected
tested A/B support pieces and one one-edge separator connector per
outer-tree neighbour. The verified join-tree lift combines these
forests, and dependent one-edge deletion removes exactly the
connector labels. The selected family is then reindexed by its
original labels, not by an enlarged completion family.

This theorem is the abstract repeated-owner forest lifting step.
Constructing the locally forested requests from the old q-bound
and actual picture geometry remains its application interface.
-/

namespace StructuralRamsey.Girth

universe v
variable {W Q N : Type v}

/-- Local forests of the actual owner requests, with correctly
chosen one-edge connectors, give a forest on precisely the
original selected family. No additional designated completion
members are introduced or later deleted. -/
theorem selectedForest_of_ownerRequests
    [Fintype Q] [Nonempty Q] [Fintype N]
    {P : Q → HypergraphPiece W}
    (hOuter : PairwiseAllowed P)
    (JOuter : JoinTree P)
    (hLinear : OuterEdgesLinear P)
    (owner : N → Q) (hSurj : Function.Surjective owner)
    (selected : N → HypergraphPiece W)
    (separator : (q : Q) → JOuter.tree.neighborSet q → HypergraphPiece W)
    (hLocal :
      ∀ q : Q, ForestOfCopies
        (fun z : {n : N // owner n = q} ⊕
            JOuter.tree.neighborSet q =>
          match z with
          | .inl n => selected n.1
          | .inr r => separator q r))
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
  let L : Q → Type v := fun q => {n : N // owner n = q}
  let R : Q → Type v := fun q => JOuter.tree.neighborSet q
  let F : (q : Q) → L q ⊕ R q → HypergraphPiece W :=
    fun q z =>
      match z with
      | .inl n => selected n.1
      | .inr r => separator q r
  letI : ∀ q : Q, Fintype (L q ⊕ R q) :=
    fun q => inferInstance
  have hNonempty (q : Q) : Nonempty (L q ⊕ R q) := by
    obtain ⟨n, hn⟩ := hSurj q
    exact ⟨.inl ⟨n, hn⟩⟩
  letI : ∀ q : Q, Nonempty (L q ⊕ R q) := hNonempty
  have hForest (q : Q) : ForestOfCopies (F q) := by
    simpa only [F, L, R] using hLocal q
  have hLocalAllowed : ∀ q, PairwiseAllowed (F q) :=
    fun q => (hForest q).pairwiseAllowed
  let JLocal : ∀ q, JoinTree (F q) :=
    fun q => Classical.choice ((hForest q).joinTree_of_nonempty)
  have hContain : ∀ q (k : L q ⊕ R q),
      (F q k).carrier ⊆ (P q).carrier := by
    intro q k
    cases k with
    | inl n =>
        change (selected n.1).carrier ⊆ (P q).carrier
        have h := hSelectedContain n.1
        rw [n.2] at h
        exact h
    | inr r =>
        exact hSeparatorContain q r
  let defaultSelected (q : Q) : L q :=
    ⟨Classical.choose (hSurj q), Classical.choose_spec (hSurj q)⟩
  let connector (q r : Q) : L q ⊕ R q :=
    if hadj : JOuter.tree.Adj q r then
      .inr ⟨r, hadj⟩
    else
      .inl (defaultSelected q)
  have hConnector :
      ∀ ⦃q r : Q⦄, JOuter.tree.Adj q r →
        (P q).carrier ∩ (P r).carrier ⊆
          (F q (connector q r)).carrier := by
    intro q r hadj
    simpa [F, connector, hadj] using hSeparatorCover hadj
  have hConnectorEdge :
      ∀ ⦃q r : Q⦄ (hadj : JOuter.tree.Adj q r),
        ¬((P q).carrier ∩ (P r).carrier).Subsingleton →
          (F q (connector q r)).IsOneEdge ∧
          (F q (connector q r)).carrier =
            (P q).carrier ∩ (P r).carrier := by
    intro q r hadj hLarge
    simpa [F, connector, hadj] using
      (show (separator q ⟨r, hadj⟩).IsOneEdge ∧
          (separator q ⟨r, hadj⟩).carrier =
            (P q).carrier ∩ (P r).carrier from
        ⟨hSeparatorOneEdge q ⟨r, hadj⟩,
          hSeparatorExact hadj hLarge⟩)
  have hAugmented :
      ForestOfCopies
        (fun z : Sigma (fun q => L q ⊕ R q) => F z.1 z.2) :=
    forestOfCopies_lift_local_of_linear
      hOuter JOuter hLinear
      hLocalAllowed JLocal hContain
      connector hConnector hConnectorEdge
  have hDependent :
      ForestOfCopies (fun z : Sigma L => F z.1 (.inl z.2)) :=
    ForestOfCopies.sigmaSum_left_of_oneEdge_right
      F hAugmented (by
        intro q r
        exact hSeparatorOneEdge q r)
  have hSelected :
      ForestOfCopies
        (fun z : Sigma (fun q : Q => {n : N // owner n = q}) =>
          selected z.2.1) := by
    simpa only [F, L] using hDependent
  exact hSelected.of_ownerFibers owner selected

end StructuralRamsey.Girth
