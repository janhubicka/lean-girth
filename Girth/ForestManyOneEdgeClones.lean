import Girth.ForestDuplicateOneEdge
import Mathlib.Data.Fintype.Option

/-!
# Any finite number of duplicate one-edge requests preserves forests

The clone-one-edge lemma can be iterated: start from a forest of
DISTINCT support pieces and attach a finite list of additional
labels, each naming an already present ONE-EDGE member. New
labels attach at the original representative, never to arbitrary
non-one-edge B supports.

This is the label-completion step needed to pass from the old
mixed forest property on a SET of pieces to a local request list
containing duplicate separator edges.
-/

namespace StructuralRamsey.Girth

universe v
variable {W I : Type v}

/-- Finite one-edge clones of members of an existing nonempty
forest may all be added without spoiling allowed intersections
or running intersections. -/
theorem ForestOfCopies.sum_finite_oneEdgeClones
    [Fintype I] [Nonempty I]
    (F : I → HypergraphPiece W)
    (hF : ForestOfCopies F)
    {X : Type v} [Fintype X]
    (extra : X → HypergraphPiece W)
    (hClones : ∀ x : X, ∃ i : I,
      extra x = F i ∧ (F i).IsOneEdge) :
    ForestOfCopies (sumPieces F extra) := by
  classical
  let P : ∀ (X : Type v) [Fintype X], Prop :=
    fun X _ => ∀ extra : X → HypergraphPiece W,
      (∀ x : X, ∃ i : I, extra x = F i ∧ (F i).IsOneEdge) →
      ForestOfCopies (sumPieces F extra)
  have hAll : ∀ (X : Type v) [Fintype X], P X := by
    intro X _
    apply Fintype.induction_empty_option (P := P)
    · intro α β _ e hα
      intro xs hXs
      let oldXs : α → HypergraphPiece W := fun a => xs (e a)
      have hOld : ForestOfCopies (sumPieces F oldXs) := by
        apply hα oldXs
        intro a
        exact hXs (e a)
      let ren : (I ⊕ β) ≃ (I ⊕ α) :=
        (Equiv.refl I).sumCongr e.symm
      have hNew := hOld.reindex ren
      simpa [sumPieces, oldXs, ren] using hNew
    · intro xs _
      let ren : (I ⊕ PEmpty.{v+1}) ≃ I :=
        { toFun := fun z =>
            match z with
            | .inl i => i
            | .inr a => isEmptyElim a
          invFun := Sum.inl
          left_inv := by
            intro z
            cases z with
            | inl i => rfl
            | inr a => exact isEmptyElim a
          right_inv := by intro i; rfl }
      have hNew := hF.reindex ren
      simpa [sumPieces, ren] using hNew
    · intro α _ hα
      intro xs hXs
      let oldXs : α → HypergraphPiece W :=
        fun a => xs (some a)
      have hOld : ForestOfCopies (sumPieces F oldXs) := by
        apply hα oldXs
        intro a
        exact hXs (some a)
      obtain ⟨p, hpEq, hpOne⟩ := hXs none
      have hOne : ((sumPieces F oldXs) (Sum.inl p)).IsOneEdge :=
        hpOne
      have hApp :=
        hOld.append_duplicate_oneEdge (Sum.inl p) hOne
      let ren : (I ⊕ Option α) ≃
          ((I ⊕ α) ⊕ PUnit.{v+1}) :=
        { toFun := fun z =>
            match z with
            | .inl i => .inl (.inl i)
            | .inr (some a) => .inl (.inr a)
            | .inr none => .inr PUnit.unit
          invFun := fun z =>
            match z with
            | .inl (.inl i) => .inl i
            | .inl (.inr a) => .inr (some a)
            | .inr _ => .inr none
          left_inv := by
            intro z
            cases z with
            | inl i => rfl
            | inr o => cases o <;> rfl
          right_inv := by
            intro z
            rcases z with ⟨i | a⟩ | u
            · cases i with
              | inl i => rfl
              | inr a => rfl
            · cases u
              rfl }
      have hNew := hApp.reindex ren
      have hEq :
          (fun z : I ⊕ Option α =>
            sumPieces (sumPieces F oldXs)
              (fun _ : PUnit.{v+1} =>
                (sumPieces F oldXs) (.inl p))
              (ren z)) =
          sumPieces F xs := by
        funext z
        cases z with
        | inl i => rfl
        | inr o =>
            cases o with
            | none => exact hpEq.symm
            | some a => rfl
      rw [hEq] at hNew
      exact hNew
  exact hAll X extra hClones

end StructuralRamsey.Girth
