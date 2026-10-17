import Girth.TrainOutputOldPos
import Girth.TrainArbitraryLongA2Geometry
import Girth.TrainSupremeLabelProvenance

/-!
# Circulation: designated labels in arbitrary literal replacements

The strict PlanValid case has only one surviving designated label.
For the broader admissible-replacement lemma, other designated labels
may survive: they must be exactly the labels of KEPT source
occurrences, since every new short or long piece carries only actual
edge labels.

This is a literal ordered-word provenance theorem. It identifies
the precise oldPos of every output designated occurrence and needs
no chosen supreme label, PlanValid, acceptability or wagon linearity.

Consequently a later supreme label of the output already occurs
as a designated source label. This supplies the target index for
composing arbitrary replacements back into the source cycle.
No appendix theorem is used.
-/

namespace StructuralRamsey.Girth.OrderOneData

universe v
variable {V E I P : Type v} (D : OrderOneData V E I P)

/-- Every designated occurrence in an arbitrary literal output comes
from a kept original designated occurrence at its genuine oldPos.
In particular, no newly inserted physical edge label can be mistaken
for a designated source copy. -/
theorem BigCycle.output_designated_origin_of_literalWord
    {n m : ℕ} (C : D.BigCycle n) (B : D.BigCycle m)
    (pieces : Fin n → TrainSupremePiece E P)
    (hWord : List.ofFn (fun t : Fin m =>
      (B.label t, B.connector t)) = C.resultWord D pieces)
    (oldPos : Fin n → Fin m)
    (hConnector : ∀ i : Fin n,
      B.connector (oldPos i) = C.connector i)
    (j : Fin m) (hDes : D.designated (B.label j)) :
    ∃ i : Fin n,
      j = oldPos i ∧
      pieces i = .keep ∧
      C.label i = B.label j := by
  classical
  have hMember :
      (B.label j, B.connector j) ∈ C.resultWord D pieces := by
    rw [← hWord]
    exact List.mem_ofFn.mpr ⟨j, rfl⟩
  unfold BigCycle.resultWord at hMember
  obtain ⟨block, hBlock, hEntry⟩ := List.mem_flatten.mp hMember
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hBlock
  cases hp : pieces i with
  | keep =>
      have hEq :
          (B.label j, B.connector j) =
            (C.label i, C.connector i) := by
        simpa [BigCycle.pieceWord, hp] using hEntry
      refine ⟨i, ?_, hp, ?_⟩
      · apply B.connector_injective
        calc
          B.connector j = C.connector i := congrArg Prod.snd hEq
          _ = B.connector (oldPos i) := (hConnector i).symm
      · exact (congrArg Prod.fst hEq).symm
  | short e =>
      have hEq :
          (B.label j, B.connector j) =
            (Sum.inr e, C.connector i) := by
        simpa [BigCycle.pieceWord, hp] using hEntry
      have hLabel : B.label j = Sum.inr e :=
        congrArg Prod.fst hEq
      simp [OrderOneData.designated, hLabel] at hDes
  | long e w f =>
      have hCases :
          (B.label j, B.connector j) =
            ((Sum.inr e : I ⊕ E), (Sum.inr w : V ⊕ P)) ∨
          (B.label j, B.connector j) =
            ((Sum.inr f : I ⊕ E), C.connector i) := by
        simpa [BigCycle.pieceWord, hp] using hEntry
      rcases hCases with hNew | hOld
      · have hLabel : B.label j = Sum.inr e :=
          congrArg Prod.fst hNew
        simp [OrderOneData.designated, hLabel] at hDes
      · have hLabel : B.label j = Sum.inr f :=
          congrArg Prod.fst hOld
        simp [OrderOneData.designated, hLabel] at hDes

/-- The designated label of any actual output occurrence is already
represented by a designated occurrence of the original source, even
when the first replacement is not a strict single-supreme plan. -/
theorem BigCycle.output_designated_label_from_source
    {n m : ℕ} (C : D.BigCycle n) (B : D.BigCycle m)
    (pieces : Fin n → TrainSupremePiece E P)
    (hWord : List.ofFn (fun t : Fin m =>
      (B.label t, B.connector t)) = C.resultWord D pieces)
    (j : Fin m) (hDes : D.designated (B.label j)) :
    ∃ i : Fin n, C.label i = B.label j := by
  obtain ⟨oldPos, hConnector, _hVertexPos⟩ :=
    C.oldPos_exists_of_literal_resultWord D B pieces hWord
  obtain ⟨i, _hIndex, _hKeep, hLabel⟩ :=
    C.output_designated_origin_of_literalWord
      D B pieces hWord oldPos hConnector j hDes
  exact ⟨i, hLabel⟩

/-- If an arbitrary literal output has an indexed supreme label,
that same designated label already occurs in the original source
cycle and may be used as the target of a composed plan. -/
theorem BigCycle.supreme_target_occurs_in_source
    {n m : ℕ} (C : D.BigCycle n) (B : D.BigCycle m)
    (pieces : Fin n → TrainSupremePiece E P)
    (hWord : List.ofFn (fun t : Fin m =>
      (B.label t, B.connector t)) = C.resultWord D pieces)
    (j : Fin m) (hSupreme : B.HasSupremeAt D j) :
    ∃ i : Fin n, C.label i = B.label j := by
  exact C.output_designated_label_from_source
    D B pieces hWord j hSupreme.1

end StructuralRamsey.Girth.OrderOneData
