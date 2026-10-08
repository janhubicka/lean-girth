import Girth.ForestCompletionOwnerAssembly
import Girth.ForestCompletionChoices

/-! # Quantified forest completion from geometric local requests

The circulation preservation argument has a finite selected family and a
join tree of the standard pictures containing its members.  At each owner
the old finite completion property is applied to its selected members and
one separator connector per adjacent owner.  The local completions are
then glued and auxiliary one-edge connectors removed.

The result below discharges all finiteness, choice and combinatorial
assembly arguments.  What remains to apply it to the actual picture step
is the geometric construction of the requests, their containment in
standard pictures, and the separator identities.
-/

namespace StructuralRamsey.Girth

universe v
variable {W Q N : Type v}

/-- Local finite completion properties, together with compatible requests
along an outer join tree, give a designated completion of the selected
global family.  Local tested and designated predicates may depend on the
outer standard picture. -/
theorem ForestCompletionProperty.assemble_over_joinTree
    [Fintype Q] [Nonempty Q] [DecidableEq Q] [Fintype N]
    {P : Q → HypergraphPiece W}
    (hOuter : PairwiseAllowed P)
    (JOuter : JoinTree P)
    [DecidableRel JOuter.tree.Adj]
    {H : Set (Set W)}
    (hEdges :
      ∀ q : Q, ∀ ⦃e : Set W⦄, e ∈ (P q).edges → e ∈ H)
    (hGirth : GirthGT H 2)
    (owner : N → Q)
    (hSurj : Function.Surjective owner)
    (m : ℕ)
    (hCard : Fintype.card N ≤ m)
    (selectedGlobal : N → HypergraphPiece W)
    (requested :
      (q : Q) →
        ({n : N // owner n = q} ⊕
          JOuter.tree.neighborSet q) → HypergraphPiece W)
    (hSelectedRequest :
      ∀ q (n : {n : N // owner n = q}),
        requested q (.inl n) = selectedGlobal n.1)
    (hRequestContained :
      ∀ q (r : {n : N // owner n = q} ⊕
          JOuter.tree.neighborSet q),
        (requested q r).carrier ⊆ (P q).carrier)
    (hConnectorOneEdge :
      ∀ q (r : JOuter.tree.neighborSet q),
        (requested q (.inr r)).IsOneEdge)
    (hSeparator :
      ∀ ⦃q r : Q⦄ (hadj : JOuter.tree.Adj q r),
        (P q).carrier ∩ (P r).carrier ⊆
          (requested q (.inr ⟨r, hadj⟩)).carrier)
    (hSeparatorExact :
      ∀ ⦃q r : Q⦄ (hadj : JOuter.tree.Adj q r),
        ¬((P q).carrier ∩ (P r).carrier).Subsingleton →
          (requested q (.inr ⟨r, hadj⟩)).carrier =
            (P q).carrier ∩ (P r).carrier)
    (testedLocal designatedLocal :
      Q → HypergraphPiece W → Prop)
    (hOld :
      ∀ q,
        ForestCompletionProperty
          (testedLocal q) (designatedLocal q) m)
    (hTest :
      ∀ q (r : {n : N // owner n = q} ⊕
          JOuter.tree.neighborSet q),
        testedLocal q (requested q r))
    (designated : HypergraphPiece W → Prop)
    (hDesignatedContained :
      ∀ q (R : HypergraphPiece W),
        designatedLocal q R → R.carrier ⊆ (P q).carrier)
    (hDesignatedGlobal :
      ∀ q (R : HypergraphPiece W),
        designatedLocal q R → designated R) :
    ∃ (K : Q → Type v),
      ∃ (finite : ∀ q, Fintype (K q)),
        letI : ∀ q, Fintype (K q) := finite
        ∃ (family : (q : Q) → K q → HypergraphPiece W),
        ∃ keep : Finset (Sigma K),
          ForestCompletionWitness selectedGlobal designated
            (fun z : {z : Sigma K // z ∈ keep} =>
              family z.1.1 z.1.2) := by
  classical
  obtain ⟨K, finite, family, label, hPairs⟩ :=
    ForestCompletionProperty.choose_neighbor_local_completions_with_labels
      testedLocal designatedLocal hOld owner hSurj JOuter.tree
      requested hTest hCard
  letI : ∀ q : Q, Fintype (K q) := finite
  have hLocal :
      ∀ q,
        ForestCompletionWitness
          (requested q) (designatedLocal q) (family q) := by
    intro q
    exact (hPairs q).1
  have hLabel :
      ∀ q (r : {n : N // owner n = q} ⊕
          JOuter.tree.neighborSet q),
        family q (label q r) = requested q r := by
    intro q r
    exact (hPairs q).2 r
  obtain ⟨keep, hWitness⟩ :=
    forestCompletion_witness_of_compatible_local_completions
      hOuter JOuter hEdges hGirth
      owner hSurj m hCard
      selectedGlobal requested
      hSelectedRequest hRequestContained
      hConnectorOneEdge hSeparator hSeparatorExact
      designatedLocal designated
      hDesignatedContained hDesignatedGlobal
      family hLocal label hLabel
  exact ⟨K, finite, family, keep, hWitness⟩

end StructuralRamsey.Girth
