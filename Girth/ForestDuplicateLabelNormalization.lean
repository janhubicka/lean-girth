import Girth.ForestAuxiliaryDeletion
import Girth.ForestMixedSetBound
import Girth.ForestGeneralJoinLift

/-!
# From labelled forests to forests on their DISTINCT physical members

For the manuscript, finite families are SETS of hypergraph pieces,
not lists of labels. The global join-tree proof naturally glues
dependent, owner-labelled local families. Multiple owner labels
may represent the SAME one-edge separator request.

A duplicate multi-edge designated B-piece cannot be deleted as an
auxiliary, so the exact hypothesis is: if two distinct labels carry
the same physical piece, that piece is one-edge. Choose exactly
one label for each distinct physical piece and delete all other
one-edge labels. The retained family is equivalent to the finite
image set, so it is a forest. No arbitrary-subforest heredity is
assumed.

Candidate source only: requires a focused Lean compilation and
executed #print axioms before use as a certification.
-/

namespace StructuralRamsey.Girth

universe v
variable {W I : Type v}

/-- A labelled forest descends to its set of DISTINCT physical
pieces if every duplicated member is genuinely one-edge.

The result has type
`ForestOfCopies (fun P : {P // P ∈ image F} => P.1)`,
which is exactly the set-valued forest property used in the
manuscript and in `FiniteMixedForestThrough`. -/
theorem ForestOfCopies.finiteImage_of_duplicate_oneEdge
    [Fintype I]
    (F : I → HypergraphPiece W)
    (hForest : ForestOfCopies F)
    (hDuplicateOneEdge :
      ∀ ⦃i j : I⦄, i ≠ j → F i = F j →
        (F i).IsOneEdge) :
    ForestOfCopies
      (fun P : {P : HypergraphPiece W //
        P ∈ Finset.univ.image F} => P.1) := by
  classical
  let K := {P : HypergraphPiece W // P ∈ Finset.univ.image F}
  let rep : K → I :=
    fun P => Classical.choose (Finset.mem_image.mp P.2)
  have hRep (P : K) : F (rep P) = P.1 := by
    exact (Classical.choose_spec (Finset.mem_image.mp P.2)).2
  let keep : Finset I := Finset.univ.image rep
  have hKeep (P : K) : rep P ∈ keep := by
    exact Finset.mem_image.mpr ⟨P, Finset.mem_univ P, rfl⟩
  have hAux : ∀ i : I, i ∉ keep → (F i).IsOneEdge := by
    intro i hi
    have hImage : F i ∈ Finset.univ.image F :=
      Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
    let P : K := ⟨F i, hImage⟩
    have hiNe : i ≠ rep P := by
      intro heq
      apply hi
      simpa [heq] using hKeep P
    have hEq : F i = F (rep P) := (hRep P).symm
    exact hDuplicateOneEdge hiNe hEq
  have hRestrict :
      ForestOfCopies
        (fun z : {i : I // i ∈ keep} => F z.1) :=
    hForest.restrict_of_oneEdge_outside keep hAux
  let label : K → {i : I // i ∈ keep} :=
    fun P => ⟨rep P, hKeep P⟩
  have hLabelInj : Function.Injective label := by
    intro P R h
    apply Subtype.ext
    have hRepEq : rep P = rep R :=
      congrArg Subtype.val h
    calc
      P.1 = F (rep P) := (hRep P).symm
      _ = F (rep R) := congrArg F hRepEq
      _ = R.1 := hRep R
  have hLabelSurj : Function.Surjective label := by
    intro z
    obtain ⟨P, _, hP⟩ := Finset.mem_image.mp z.2
    refine ⟨P, ?_⟩
    exact Subtype.ext hP
  let e : K ≃ {i : I // i ∈ keep} :=
    Equiv.ofBijective label ⟨hLabelInj, hLabelSurj⟩
  have hResult := hRestrict.reindex e
  have hEqFamily :
      (fun P : K => F (e P).1) = (fun P : K => P.1) := by
    funext P
    change F (rep P) = P.1
    exact hRep P
  rw [hEqFamily] at hResult
  exact hResult


/-- Set-valued conclusion of the singleton-free dependent join-tree
lift, provided copies repeated under different owner labels
are one-edge requests. This is the exact image-normalization
premise left by the general forest proof. -/
theorem forestOfCopies_lift_without_singleton_on_distinct_image
    {Q : Type v} {K : Q → Type v}
    [Fintype Q] [Nonempty Q]
    [∀ q : Q, Fintype (K q)]
    [∀ q : Q, Nonempty (K q)]
    {P : Q → HypergraphPiece W}
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
    (hDuplicateOneEdge :
      ∀ ⦃x y : Sigma K⦄,
        x ≠ y →
        F x.1 x.2 = F y.1 y.2 →
        (F x.1 x.2).IsOneEdge) :
    ForestOfCopies
      (fun t : {t : HypergraphPiece W //
        t ∈ Finset.univ.image
          (fun z : Sigma K => F z.1 z.2)} => t.1) := by
  classical
  let family : Sigma K → HypergraphPiece W :=
    fun z => F z.1 z.2
  have hWhole : ForestOfCopies family :=
    forestOfCopies_lift_local_without_singleton_requests
      JOuter hLocal hContain hEdgeRequest
  exact ForestOfCopies.finiteImage_of_duplicate_oneEdge
    family hWhole hDuplicateOneEdge

end StructuralRamsey.Girth
