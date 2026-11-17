import Girth.ForestDuplicateLabelGeometry
import Girth.ForestAuxiliaryDeletion

/-!
# Exact retained finite SET after general join-tree lifting

The manuscript retains selected members and the designated pieces
added by local completion, but deletes auxiliary one-edge requests.
The preceding general lift now gives a forest of DISTINCT physical
pieces. This module restricts that finite set to the chosen
retained set. Every omitted physical member is explicitly
assumed one-edge; no arbitrary-subfamily heredity is asserted.

Source-level candidate. It has not been Lean-compiled or axiom-audited.
-/

namespace StructuralRamsey.Girth

universe v
variable {W Q : Type v}

/-- Restrict a forest of distinct support pieces to a finite
retained subset, provided EVERY omitted member is one-edge.
The proof uses the existing short-auxiliary deletion theorem
on the subtype of the original finite set and then reindexes
the survivors by their exact physical pieces. -/
theorem ForestOfCopies.restrict_to_retained_finset
    (all kept : Finset (HypergraphPiece W))
    (hForest :
      ForestOfCopies
        (fun P : {P : HypergraphPiece W // P ∈ all} => P.1))
    (hKept : kept ⊆ all)
    (hOmitted :
      ∀ P : HypergraphPiece W, P ∈ all → P ∉ kept →
        P.IsOneEdge) :
    ForestOfCopies
      (fun P : {P : HypergraphPiece W // P ∈ kept} => P.1) := by
  classical
  let I := {P : HypergraphPiece W // P ∈ all}
  let R := {P : HypergraphPiece W // P ∈ kept}
  let keep : Finset I :=
    Finset.univ.filter (fun P : I => P.1 ∈ kept)
  have hAux :
      ∀ P : I, P ∉ keep → P.1.IsOneEdge := by
    intro P hnot
    have hNotKept : P.1 ∉ kept := by
      intro hP
      apply hnot
      simp [keep, hP]
    exact hOmitted P.1 P.2 hNotKept
  have hRestrict :
      ForestOfCopies
        (fun z : {z : I // z ∈ keep} => z.1.1) :=
    hForest.restrict_of_oneEdge_outside keep hAux
  let e : R ≃ {z : I // z ∈ keep} :=
    { toFun := fun P =>
        ⟨⟨P.1, hKept P.2⟩, by
          simp [keep, P.2]⟩
      invFun := fun P =>
        ⟨P.1.1, (Finset.mem_filter.mp P.2).2⟩
      left_inv := by
        intro P
        apply Subtype.ext
        rfl
      right_inv := by
        intro P
        apply Subtype.ext
        apply Subtype.ext
        rfl }
  have hResult := hRestrict.reindex e
  change ForestOfCopies (fun P : R => P.1) at hResult
  exact hResult

/-- Keep exactly the selected members and the locally added designated
members of a forest on its DISTINCT physical image.

The input labelled family may contain repeated request edges, and
a request edge may itself be selected or designated. The only
discarded members are pieces which belong to neither target set;
the classification hypothesis guarantees that these are one-edge.
This avoids arbitrary-subfamily heredity. -/
theorem ForestOfCopies.restrict_image_to_selected_added
    {I : Type v} [Fintype I]
    (F : I → HypergraphPiece W)
    (hForest :
      ForestOfCopies
        (fun T : {T : HypergraphPiece W //
          T ∈ Finset.univ.image F} => T.1))
    (selected added : Finset (HypergraphPiece W))
    (hSelected :
      ∀ T : HypergraphPiece W, T ∈ selected →
        ∃ i : I, F i = T)
    (hAdded :
      ∀ T : HypergraphPiece W, T ∈ added →
        ∃ i : I, F i = T)
    (hClassify :
      ∀ i : I,
        F i ∈ selected ∨ F i ∈ added ∨ (F i).IsOneEdge) :
    ForestOfCopies
      (fun T : {T : HypergraphPiece W //
        T ∈ selected ∪ added} => T.1) := by
  classical
  let all : Finset (HypergraphPiece W) := Finset.univ.image F
  let kept : Finset (HypergraphPiece W) := selected ∪ added
  have hKeepSub : kept ⊆ all := by
    intro T hT
    rcases Finset.mem_union.mp hT with hSel | hAdd
    · obtain ⟨i, hi⟩ := hSelected T hSel
      exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, hi⟩
    · obtain ⟨i, hi⟩ := hAdded T hAdd
      exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, hi⟩
  have hOmitted :
      ∀ T : HypergraphPiece W, T ∈ all →
        T ∉ kept → T.IsOneEdge := by
    intro T hIn hNot
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hIn
    rcases hClassify i with hSel | hAdd | hOne
    · exfalso
      apply hNot
      apply Finset.mem_union.mpr
      left
      simpa only [hi] using hSel
    · exfalso
      apply hNot
      apply Finset.mem_union.mpr
      right
      simpa only [hi] using hAdd
    · simpa [hi] using hOne
  exact ForestOfCopies.restrict_to_retained_finset
    all kept hForest hKeepSub hOmitted

/-- Fully retained finite-set version of the general join-tree
lift, with no request on singleton separators. The hypotheses
are exactly: local completed forests with nonempty edge
supports, linear ambient support, genuine one-edge requests
only on nonsubsingleton separators, and a chosen finite keep
set whose omitted members are one-edge requests.

No edge coverage of isolated separator vertices is assumed. -/
theorem forestOfCopies_lift_without_singleton_retained_set
    {K : Q → Type v}
    [Fintype Q] [Nonempty Q]
    [∀ q : Q, Fintype (K q)]
    [∀ q : Q, Nonempty (K q)]
    {P : Q → HypergraphPiece W}
    (hOuter : PairwiseAllowed P)
    (JOuter : JoinTree P)
    {F : (q : Q) → K q → HypergraphPiece W}
    (hLocal : ∀ q : Q, ForestOfCopies (F q))
    (hContain :
      ∀ q (k : K q), (F q k).carrier ⊆ (P q).carrier)
    (hEdgeRequest :
      ∀ ⦃q r : Q⦄ (hadj : JOuter.tree.Adj q r),
        ¬((P q).carrier ∩ (P r).carrier).Subsingleton →
        ∃ k : K q,
          F q k = HypergraphPiece.oneEdge
            ((P q).carrier ∩ (P r).carrier))
    (H : Set (Set W))
    (hLinear : LinearEdgeSet H)
    (hLarge : ∀ e : Set W, e ∈ H → ¬ e.Subsingleton)
    (hOuterEdges :
      ∀ q : Q, (P q).edges ⊆ H)
    (hLocalEdges :
      ∀ q : Q, ∀ k : K q, (F q k).edges ⊆ H)
    (hLocalNonempty :
      ∀ q : Q, ∀ k : K q, (F q k).edges.Nonempty)
    (kept : Finset (HypergraphPiece W))
    (hKeepSub :
      kept ⊆ Finset.univ.image
        (fun z : Sigma K => F z.1 z.2))
    (hOmitted :
      ∀ T : HypergraphPiece W,
        T ∈ Finset.univ.image
          (fun z : Sigma K => F z.1 z.2) →
        T ∉ kept → T.IsOneEdge) :
    ForestOfCopies
      (fun T : {T : HypergraphPiece W // T ∈ kept} => T.1) := by
  classical
  let all : Finset (HypergraphPiece W) :=
    Finset.univ.image (fun z : Sigma K => F z.1 z.2)
  have hAll :
      ForestOfCopies
        (fun T : {T : HypergraphPiece W // T ∈ all} => T.1) :=
    forestOfCopies_lift_local_without_singleton_on_set
      hOuter JOuter hLocal hContain hEdgeRequest H hLinear
      hLarge hOuterEdges hLocalEdges hLocalNonempty
  exact ForestOfCopies.restrict_to_retained_finset
    all kept hAll hKeepSub hOmitted


/-- Complete finite-SET formulation including the EMPTY outer family.

The manuscript allows an empty forest of outer copies. In that case
there is no selected member and the retained image is empty. For
nonempty outer families the chosen join tree and its edge requests
enter the existing retained-set lifting theorem. No extra local
edge-coverage hypothesis is introduced. -/
theorem forestOfCopies_lift_retained_set_including_empty_outer
    {K : Q → Type v}
    [Fintype Q]
    [∀ q : Q, Fintype (K q)]
    [∀ q : Q, Nonempty (K q)]
    {P : Q → HypergraphPiece W}
    (hOuterAllowed : PairwiseAllowed P)
    {F : (q : Q) → K q → HypergraphPiece W}
    (hLocal : ∀ q : Q, ForestOfCopies (F q))
    (hContain :
      ∀ q (k : K q), (F q k).carrier ⊆ (P q).carrier)
    (hOuterPlan :
      IsEmpty Q ∨
        ∃ JOuter : JoinTree P,
          ∀ ⦃q r : Q⦄ (hadj : JOuter.tree.Adj q r),
            ¬((P q).carrier ∩ (P r).carrier).Subsingleton →
            ∃ k : K q,
              F q k = HypergraphPiece.oneEdge
                ((P q).carrier ∩ (P r).carrier))
    (H : Set (Set W))
    (hLinear : LinearEdgeSet H)
    (hLarge : ∀ e : Set W, e ∈ H → ¬ e.Subsingleton)
    (hOuterEdges :
      ∀ q : Q, (P q).edges ⊆ H)
    (hLocalEdges :
      ∀ q : Q, ∀ k : K q, (F q k).edges ⊆ H)
    (hLocalNonempty :
      ∀ q : Q, ∀ k : K q, (F q k).edges.Nonempty)
    (kept : Finset (HypergraphPiece W))
    (hKeepSub :
      kept ⊆ Finset.univ.image
        (fun z : Sigma K => F z.1 z.2))
    (hOmitted :
      ∀ T : HypergraphPiece W,
        T ∈ Finset.univ.image
          (fun z : Sigma K => F z.1 z.2) →
        T ∉ kept → T.IsOneEdge) :
    ForestOfCopies
      (fun T : {T : HypergraphPiece W // T ∈ kept} => T.1) := by
  classical
  by_cases hQ : Nonempty Q
  · letI : Nonempty Q := hQ
    rcases hOuterPlan with hEmpty | ⟨JOuter, hEdgeRequest⟩
    · exact (not_isEmpty_of_nonempty Q hEmpty).elim
    · exact forestOfCopies_lift_without_singleton_retained_set
        hOuterAllowed JOuter hLocal hContain hEdgeRequest
        H hLinear hLarge hOuterEdges hLocalEdges hLocalNonempty
        kept hKeepSub hOmitted
  · letI : IsEmpty Q := ⟨fun q => hQ ⟨q⟩⟩
    letI : IsEmpty (Sigma K) := ⟨fun z => isEmptyElim z.1⟩
    haveI : IsEmpty
        {T : HypergraphPiece W // T ∈ kept} := by
      constructor
      intro T
      have hIn : T.1 ∈ Finset.univ.image
          (fun z : Sigma K => F z.1 z.2) :=
        hKeepSub T.2
      obtain ⟨z, _, _⟩ := Finset.mem_image.mp hIn
      exact isEmptyElim z
    constructor
    · intro x
      exact isEmptyElim x
    · left
      infer_instance

end StructuralRamsey.Girth
