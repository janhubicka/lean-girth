import Girth.ForestSingletonAttachment
import Girth.ForestReindex
import Mathlib.Logic.Equiv.Set

/-!
# Appending a finite family of singleton separators

The strengthened join-tree lifting lemma completes each owner-local forest
before singleton separators are added.  One singleton can already be appended
by `ForestOfCopies.append_subsingletonCarrier`.  This file packages the finite
iteration needed by the manuscript.
-/

namespace StructuralRamsey.Girth

universe v
variable {W I J : Type v}

/-- Append finitely many empty/singleton-carrier pieces to a nonempty forest.
The new labels are the selected elements of `s`.

This is not arbitrary forest heredity: every added member has subsingleton
carrier, so it may be attached as a leaf at each induction step. -/
theorem ForestOfCopies.append_subsingletonFinset
    [Fintype I] [Nonempty I] [DecidableEq J]
    {F : I → HypergraphPiece W}
    (hF : ForestOfCopies F)
    (S : J → HypergraphPiece W)
    (s : Finset J)
    (hSmall : ∀ j : J, j ∈ s → (S j).carrier.Subsingleton) :
    ForestOfCopies
      (sumPieces F (fun j : (s : Set J) => S j.1)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      let e : I ⊕ (∅ : Set J) ≃ I := Equiv.sumEmpty _ _
      have h := hF.reindex e
      have heq :
          (fun k => F (e k)) =
            sumPieces F (fun j : (∅ : Set J) => S j.1) := by
        funext k
        cases k with
        | inl i => rfl
        | inr j => exact False.elim j.2
      rw [← heq]
      exact h
  | @insert a s ha ih =>
      have ih' : ForestOfCopies
          (sumPieces F (fun j : (s : Set J) => S j.1)) :=
        ih (fun j hj => hSmall j (Finset.mem_insert_of_mem hj))
      have haSmall : (S a).carrier.Subsingleton :=
        hSmall a (Finset.mem_insert_self a s)
      have happ :=
        ih'.append_subsingletonCarrier (S a) haSmall
      have haSet : a ∉ (↑s : Set J) := by
        simpa using ha
      let es :
          (↑(insert a s) : Set J) ≃ (↑s : Set J) ⊕ PUnit :=
        Equiv.Set.insert haSet
      let e :
          I ⊕ (↑(insert a s) : Set J) ≃
            (I ⊕ (↑s : Set J)) ⊕ PUnit :=
        (Equiv.sumCongr (Equiv.refl I) es).trans
          (Equiv.sumAssoc I (↑s : Set J) PUnit).symm
      have hr := happ.reindex e
      simpa [sumPieces, e, es] using hr

end StructuralRamsey.Girth
