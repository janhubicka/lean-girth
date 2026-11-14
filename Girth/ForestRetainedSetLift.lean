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

end StructuralRamsey.Girth
