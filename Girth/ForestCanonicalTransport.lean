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

/-- Two hypergraph pieces with equal carriers and equal edge families
are equal; the proof of edge containment is irrelevant. -/
private theorem hypergraphPiece_ext
    {F G : HypergraphPiece W}
    (hCarrier : F.carrier = G.carrier)
    (hEdges : F.edges = G.edges) : F = G := by
  cases F with
  | mk FC FE Fh =>
    cases G with
    | mk GC GE Gh =>
      dsimp at hCarrier hEdges
      cases hCarrier
      cases hEdges
      rfl

/-- A source auxiliary one-edge A-piece transports to the corresponding
one-edge piece on the image edge; it has no extra support edges. -/
theorem HypergraphPiece.oneEdge_map
    (e : Set Old) (φ : Old ↪ W) :
    (HypergraphPiece.oneEdge e).map φ =
      HypergraphPiece.oneEdge (φ '' e) := by
  apply hypergraphPiece_ext
  · rfl
  · ext F
    constructor
    · rintro ⟨e₀, he₀, hF⟩
      have heq : e₀ = e := by
        simpa [HypergraphPiece.oneEdge] using he₀
      subst e₀
      exact hF
    · intro hF
      have hEq : F = φ '' e := by
        simpa [HypergraphPiece.oneEdge] using hF
      exact ⟨e, by simp [HypergraphPiece.oneEdge], hEq⟩

/-- Testing the source one-A-edge piece makes its image a canonical
local tested piece. This is the elementary part of the local connector
preimage obligation in the circulation proof. -/
theorem transportedOneEdge_of_source_test
    (tested : HypergraphPiece Old → Prop)
    (φ : Old ↪ W) (e : Set Old)
    (hTest : tested (HypergraphPiece.oneEdge e)) :
    TransportedPiece tested φ (HypergraphPiece.oneEdge (φ '' e)) := by
  refine ⟨HypergraphPiece.oneEdge e, hTest, ?_⟩
  exact (HypergraphPiece.oneEdge_map e φ).symm

/-- The local gluing connector is tested whenever its support edge is
the image of one tested old A-edge. -/
theorem transportedOneEdge_of_source_preimage
    (tested : HypergraphPiece Old → Prop)
    (φ : Old ↪ W) (e : Set W)
    (hPreimage : ∃ e₀ : Set Old,
      tested (HypergraphPiece.oneEdge e₀) ∧ e = φ '' e₀) :
    TransportedPiece tested φ (HypergraphPiece.oneEdge e) := by
  obtain ⟨e₀, hTest, rfl⟩ := hPreimage
  exact transportedOneEdge_of_source_test tested φ e₀ hTest

/-- A gluing edge from a strong support embedding has a tested
one-edge preimage inside the full old standard picture, provided the
gluing embedding factors through that standard embedding and old active
support edges are tested. -/
theorem StrongSupportEmbedding.oneEdge_transported_of_factor
    {H : Set (Set Src)} {K : Set (Set W)}
    (outer : StrongSupportEmbedding H K)
    (active : Src ↪ Old) (standard : Old ↪ W)
    (hFactor : ∀ x : Src, outer x = standard (active x))
    (tested : HypergraphPiece Old → Prop)
    (hOldEdges : ∀ e₀ : Set Src, e₀ ∈ H →
      tested (HypergraphPiece.oneEdge (active '' e₀)))
    (e : Set W) (he : e ∈ outer.supportPiece.edges) :
    TransportedPiece tested standard (HypergraphPiece.oneEdge e) := by
  obtain ⟨e₀, he₀, hEq⟩ := he
  apply transportedOneEdge_of_source_preimage tested standard e
  refine ⟨active '' e₀, hOldEdges e₀ he₀, ?_⟩
  calc
    e = outer '' e₀ := hEq
    _ = standard '' (active '' e₀) := by
      apply Set.ext
      intro z
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact ⟨active x, ⟨x, hx, rfl⟩, (hFactor x).symm⟩
      · rintro ⟨y, ⟨x, hx, hxy⟩, hzy⟩
        refine ⟨x, hx, ?_⟩
        calc
          outer x = standard (active x) := hFactor x
          _ = standard y := congrArg standard hxy
          _ = z := hzy

/-- All connector one-edge pieces are canonical transported tests when
the local gluing maps for every standard copy factor through its full
old-picture embedding. -/
theorem allGluingOneEdges_transported_of_factor
    {H : Set (Set Src)} {K : Set (Set W)}
    (outer : Q → StrongSupportEmbedding H K)
    (active : Q → Src ↪ Old)
    (standard : Q → Old ↪ W)
    (hFactor : ∀ q x, outer q x = standard q (active q x))
    (tested : HypergraphPiece Old → Prop)
    (hOldEdges : ∀ q (e₀ : Set Src), e₀ ∈ H →
      tested (HypergraphPiece.oneEdge ((active q) '' e₀))) :
    ∀ q (e : Set W), e ∈ (outer q).supportPiece.edges →
      TransportedPiece tested (standard q)
        (HypergraphPiece.oneEdge e) := by
  intro q e he
  exact (outer q).oneEdge_transported_of_factor
    (active q) (standard q) (hFactor q) tested
    (hOldEdges q) e he

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
