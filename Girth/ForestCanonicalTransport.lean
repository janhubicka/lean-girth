import Girth.ForestCompletionTransportedBridge

/-!
# Canonical transport of the circulation forest-completion invariant

The induction invariant is quantified over the old full picture. Each
standard picture is a fresh embedded copy of that old picture. Rather
than passing separate local tested/designated predicates and then
postulating their pullbacks, define the local predicates *exactly* as
images of tested and designated pieces of the old full picture.

This discharges all local completion-transport assumptions once and
for all. The remaining inputs are geometric: selected pieces and
one-edge separators really belong to their assigned standard image,
the small gluing pieces form a forest, full standard images have the
right intersections, and designated images stay inside their standard
copy and are designated globally.

This is not the full preservation proposition: the concrete
partite-attachment geometry must still establish those inputs.
-/

namespace StructuralRamsey.Girth

universe v

variable {Old W Src Q N : Type v}

/-- The canonical image predicate for hypergraph pieces under one
full-standard-picture embedding. The existential retains the actual
old piece as a witness; it is not an arbitrary subset of the image. -/
def TransportedPiece
    (old : HypergraphPiece Old → Prop)
    (φ : Old ↪ W) (T : HypergraphPiece W) : Prop :=
  ∃ S : HypergraphPiece Old, old S ∧ T = S.map φ

theorem transportedPiece_map
    (old : HypergraphPiece Old → Prop)
    (φ : Old ↪ W) (S : HypergraphPiece Old)
    (hS : old S) :
    TransportedPiece old φ (S.map φ) :=
  ⟨S, hS, rfl⟩

/-- The full old completion property transfers to its *canonical*
image predicates without any extra hypothesis about the predicates. -/
theorem ForestCompletionProperty.map_to_canonical_image
    (tested designated : HypergraphPiece Old → Prop) (m : ℕ)
    (hOld : ForestCompletionProperty tested designated m)
    (φ : Old ↪ W) :
    ForestCompletionProperty
      (TransportedPiece tested φ)
      (TransportedPiece designated φ) m := by
  exact hOld.map φ
    (TransportedPiece tested φ)
    (TransportedPiece designated φ)
    (fun T hT => hT)
    (fun S hS => transportedPiece_map designated φ S hS)

/-- The canonical-image version of the two-carrier completion bridge.
There is a SINGLE quantified old completion hypothesis; per-standard
completion hypotheses and preimage functions are not independent
assumptions. The remaining source/preimage conditions occur exactly
where the actual picture step must prove its selected and gluing
pieces were transported from the old full picture. -/
theorem ForestCompletionProperty.assemble_canonical_standard_pictures
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
    (hSelectedContained :
      ∀ n : N, (selectedGlobal n).carrier ⊆
        (full (owner n)).carrier)
    (testedOld designatedOld : HypergraphPiece Old → Prop)
    (hOld : ForestCompletionProperty testedOld designatedOld m)
    (standard : Q → Old ↪ W)
    (hTestSelected :
      ∀ n : N,
        TransportedPiece testedOld (standard (owner n)) (selectedGlobal n))
    (hTestOneEdge :
      ∀ q (e : Set W), e ∈ (outer q).supportPiece.edges →
        TransportedPiece testedOld (standard q)
          (HypergraphPiece.oneEdge e))
    (designated : HypergraphPiece W → Prop)
    (hDesignatedContained :
      ∀ q (S : HypergraphPiece Old),
        designatedOld S →
          (S.map (standard q)).carrier ⊆ (full q).carrier)
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
  classical
  have hContain (q : Q) (R : HypergraphPiece W)
      (hR : TransportedPiece designatedOld (standard q) R) :
      R.carrier ⊆ (full q).carrier := by
    obtain ⟨S, hS, rfl⟩ := hR
    exact hDesignatedContained q S hS
  have hGlobal (q : Q) (R : HypergraphPiece W)
      (hR : TransportedPiece designatedOld (standard q) R) :
      designated R := by
    obtain ⟨S, hS, rfl⟩ := hR
    exact hDesignatedGlobal q S hS
  exact ForestCompletionProperty.assemble_transported_strongSupportForest
    hSourceNonempty hSourceCover outer full
    hInnerForest hSmallSub hPair hSmallEdges
    hFullEdges hAmbientGirth
    owner hSurj m hCard
    selectedGlobal hSelectedContained
    testedOld designatedOld hOld standard
    (fun q => TransportedPiece testedOld (standard q))
    (fun q => TransportedPiece designatedOld (standard q))
    (fun q R hR => hR)
    (fun q S hS => transportedPiece_map designatedOld (standard q) S hS)
    hTestSelected hTestOneEdge
    designated hContain hGlobal

end StructuralRamsey.Girth
