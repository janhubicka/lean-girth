import Girth.ForestCanonicalTransport

/-!
# Full standard-image carriers discharge local containment hypotheses

In the circulation partite construction the full standard picture indexed
by q contains the whole image of its old-picture embedding. Once this
single geometric fact is recorded, every tested or designated piece in
the canonical transported-image predicate is automatically contained in
that full standard picture.

This eliminates two separate containment assumptions from the quantified
forest completion transport. The remaining geometric premises (actual
selected-piece ownership, one-edge separator preimages, exact intersections
of standard pieces, and the local forest witness) are retained explicitly.
-/

namespace StructuralRamsey.Girth

universe v
variable {Old W Src Q N : Type v}

/-- The carrier of an image of any old piece lies inside the image of the
entire old picture. No finiteness or support-girth hypothesis is needed. -/
theorem transportedPiece_carrier_subset_range
    (tested : HypergraphPiece Old → Prop)
    (φ : Old ↪ W) (T : HypergraphPiece W)
    (hT : TransportedPiece tested φ T) :
    T.carrier ⊆ Set.range φ := by
  obtain ⟨S, _hS, rfl⟩ := hT
  intro x hx
  change x ∈ φ '' S.carrier at hx
  rcases hx with ⟨y, _hy, rfl⟩
  exact ⟨y, rfl⟩

/-- A full standard picture containing the range of its embedding contains
every canonically transported A- or B-support piece. -/
theorem transportedPiece_carrier_subset_full
    (tested : HypergraphPiece Old → Prop)
    (φ : Old ↪ W) (full : HypergraphPiece W)
    (hRange : Set.range φ ⊆ full.carrier)
    (T : HypergraphPiece W)
    (hT : TransportedPiece tested φ T) :
    T.carrier ⊆ full.carrier :=
  (transportedPiece_carrier_subset_range tested φ T hT).trans hRange

/-- Canonical version of the circulation two-carrier completion bridge:
the full standard copies' range inclusions discharge *both* the
selected-piece and the completed designated-piece carrier-containment
hypotheses. The old picture has just one completion property, shared
by all standard copies. -/
theorem ForestCompletionProperty.assemble_canonical_full_range
    [Fintype Q] [Nonempty Q] [DecidableEq Q] [Fintype N]
    {H : Set (Set Src)} {K Ambient : Set (Set W)}
    (hSourceNonempty : H.Nonempty)
    (hSourceCover :
      ∀ x : Src, ∃ e : Set Src, e ∈ H ∧ x ∈ e)
    (outer : Q → StrongSupportEmbedding H K)
    (full : Q → HypergraphPiece W)
    (hInnerForest :
      ForestOfCopies (fun q : Q => (outer q).supportPiece))
    (hSmallSub :
      ∀ q : Q,
        (outer q).supportPiece.carrier ⊆ (full q).carrier)
    (hPair :
      ∀ ⦃q r : Q⦄, q ≠ r →
        (full q).carrier ∩ (full r).carrier =
          (outer q).supportPiece.carrier ∩
            (outer r).supportPiece.carrier)
    (hSmallEdges :
      ∀ q : Q,
        (outer q).supportPiece.edges ⊆ (full q).edges)
    (hFullEdges :
      ∀ q : Q, ∀ ⦃e : Set W⦄,
        e ∈ (full q).edges → e ∈ Ambient)
    (hAmbientGirth : GirthGT Ambient 2)
    (owner : N → Q)
    (hSurj : Function.Surjective owner)
    (m : ℕ)
    (hCard : Fintype.card N ≤ m)
    (selectedGlobal : N → HypergraphPiece W)
    (testedOld designatedOld : HypergraphPiece Old → Prop)
    (hOld : ForestCompletionProperty testedOld designatedOld m)
    (standard : Q → Old ↪ W)
    (hFullRange : ∀ q, Set.range (standard q) ⊆ (full q).carrier)
    (hTestSelected :
      ∀ n : N,
        TransportedPiece testedOld (standard (owner n)) (selectedGlobal n))
    (hTestOneEdge :
      ∀ q (e : Set W), e ∈ (outer q).supportPiece.edges →
        TransportedPiece testedOld (standard q)
          (HypergraphPiece.oneEdge e))
    (designated : HypergraphPiece W → Prop)
    (hDesignatedGlobal :
      ∀ q (S : HypergraphPiece Old),
        designatedOld S → designated (S.map (standard q))) :
    ∃ (T : Q → Type v),
      ∃ (finite : ∀ q, Fintype (T q)),
        letI : ∀ q, Fintype (T q) := finite
        ∃ (family : (q : Q) → T q → HypergraphPiece W),
        ∃ keep : Finset (Sigma T),
          ForestCompletionWitness selectedGlobal designated
            (fun z : {z : Sigma T // z ∈ keep} =>
              family z.1.1 z.1.2) := by
  have hSelectedContained :
      ∀ n : N, (selectedGlobal n).carrier ⊆
        (full (owner n)).carrier := by
    intro n
    exact transportedPiece_carrier_subset_full
      testedOld (standard (owner n)) (full (owner n))
      (hFullRange (owner n)) (selectedGlobal n) (hTestSelected n)
  have hDesignatedContained :
      ∀ q (S : HypergraphPiece Old), designatedOld S →
        (S.map (standard q)).carrier ⊆ (full q).carrier := by
    intro q S hS
    exact transportedPiece_carrier_subset_full
      designatedOld (standard q) (full q) (hFullRange q)
      (S.map (standard q))
      (transportedPiece_map designatedOld (standard q) S hS)
  exact ForestCompletionProperty.assemble_canonical_standard_pictures
    hSourceNonempty hSourceCover outer full
    hInnerForest hSmallSub hPair hSmallEdges
    hFullEdges hAmbientGirth
    owner hSurj m hCard selectedGlobal hSelectedContained
    testedOld designatedOld hOld standard
    hTestSelected hTestOneEdge designated
    hDesignatedContained hDesignatedGlobal

end StructuralRamsey.Girth
