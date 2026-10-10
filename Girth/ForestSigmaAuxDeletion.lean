import Girth.ForestAuxiliaryDeletion
import Girth.ForestReindex

/-!
# Remove connector labels from dependent local forest families

At every used standard-picture owner q, the request family is indexed by
a disjoint sum of selected labels and temporary one-edge separator
connectors. After the local join trees are lifted, only the latter
should be deleted.

The exact selected family is the dependent sum of the left labels.
The complement can be erased because every right label carries one
one-edge piece. This is NOT arbitrary subfamily heredity.
-/

namespace StructuralRamsey.Girth

universe v
variable {W Q : Type v}

/-- An outer-indexed forest of selected and one-edge connector
members restricts to exactly the dependent family of selected
members. The index type need not be a constant product. -/
theorem ForestOfCopies.sigmaSum_left_of_oneEdge_right
    {L R : Q → Type v}
    [Fintype Q] [∀ q, Fintype (L q)] [∀ q, Fintype (R q)]
    (F : (q : Q) → L q ⊕ R q → HypergraphPiece W)
    (hForest :
      ForestOfCopies (fun z : Sigma (fun q => L q ⊕ R q) =>
        F z.1 z.2))
    (hAux : ∀ (q : Q) (r : R q), (F q (.inr r)).IsOneEdge) :
    ForestOfCopies
      (fun z : Sigma L => F z.1 (.inl z.2)) := by
  classical
  let T := Sigma (fun q : Q => L q ⊕ R q)
  let keep : Finset T :=
    Finset.univ.filter (fun z : T =>
      match z.2 with
      | .inl _ => True
      | .inr _ => False)
  have hInl (q : Q) (i : L q) :
      (⟨q, Sum.inl i⟩ : T) ∈ keep := by
    simp [keep]
  have hInr (q : Q) (r : R q) :
      (⟨q, Sum.inr r⟩ : T) ∉ keep := by
    simp [keep]
  have hOne : ∀ z : T, z ∉ keep → (F z.1 z.2).IsOneEdge := by
    intro z hz
    rcases z with ⟨q, x⟩
    cases x with
    | inl i =>
        exact (hz (hInl q i)).elim
    | inr r =>
        exact hAux q r
  have hRestricted :
      ForestOfCopies
        (fun z : {z : T // z ∈ keep} => F z.1.1 z.1.2) :=
    hForest.restrict_of_oneEdge_outside keep hOne
  let relabel : Sigma L ≃ {z : T // z ∈ keep} :=
    { toFun := fun z => ⟨⟨z.1, .inl z.2⟩, hInl z.1 z.2⟩
      invFun := fun z =>
        match hx : z.1.2 with
        | .inl i => ⟨z.1.1, i⟩
        | .inr r => False.elim (hInr z.1.1 r (by
            simpa [hx] using z.2))
      left_inv := by
        intro z
        rcases z with ⟨q, i⟩
        rfl
      right_inv := by
        intro z
        rcases z with ⟨⟨q, x⟩, hx⟩
        cases x with
        | inl i =>
            apply Subtype.ext
            rfl
        | inr r =>
            exact (hInr q r hx).elim }
  have hSelected := hRestricted.reindex relabel
  simpa [relabel] using hSelected


/-- Reindex the dependent sum of the exact fibers of a selected
owner map by the original selected-label type. There are no
duplicate or omitted selected labels. -/
theorem ForestOfCopies.of_ownerFibers
    {N Q : Type v}
    (owner : N → Q)
    (selected : N → HypergraphPiece W)
    (hForest :
      ForestOfCopies
        (fun z : Sigma (fun q : Q => {n : N // owner n = q}) =>
          selected z.2.1)) :
    ForestOfCopies selected := by
  let e : N ≃ Sigma (fun q : Q => {n : N // owner n = q}) :=
    { toFun := fun n => ⟨owner n, ⟨n, rfl⟩⟩
      invFun := fun z => z.2.1
      left_inv := by
        intro n
        rfl
      right_inv := by
        intro z
        rcases z with ⟨q, n, hn⟩
        cases hn
        rfl }
  have h := hForest.reindex e
  simpa [e] using h

end StructuralRamsey.Girth
