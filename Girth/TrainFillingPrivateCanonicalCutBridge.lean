import Girth.TrainFillingPrivateCanonicalParentwise
import Girth.TrainFillingPrivateSelectedOldRange
import Girth.TrainFillingOrderStageCanonicalAllCutGirth

set_option Elab.async false

/-!
# Identifying the indexed parent record with canonical inherited cut data

The genuine OrderStage provides all-cut old full system girth on
selected parent carriers and the ENTIRE ambient physical A-support.
The canonical filling theorem returns FullSystemGirthGT for its
inheritedCutData, whose copyEdges(i) are ALL filled edges with old
cover contained in the parent carrier.

The parentwise scattering constructor instead stores the image
of the actual selected contracted old-edge injection beta_i.
For a genuine induced selected M-copy the checked/constructed
range theorem identifies these two old families exactly.

This adapter records the literal OrderOneData identity. It requires
only the exact beta_i RANGE identity, not any output girth or
realization field. No ambient edge set is restricted.

The final application must still instantiate the beta_i range from
the actual selected OrderStage and the canonical X placement. This
file is a candidate until exact-head local Lean checking.
-/

namespace StructuralRamsey.Girth.IndexedPrivateChoice

universe v

variable {C V P X Y I : Type v}
variable (U : C → PrivateWagonInput V P X)

/-- The actual copied-edge range is the only difference between the
parentwise canonical record and the existing filled inheritedCutData.
Once beta_i contains precisely the old edges inside selected parent
i, the two complete incidence records are definitionally the same
after this extensional rewrite. -/
theorem canonicalFilledSelectedData_eq_inheritedCutData
    (H : UniformFillingData Y X)
    (vertex : I → Vertex U ↪ Y)
    (β : I → (C × P) ↪ H.OldEdge)
    {m : ℕ} (S : EdgeTrainLevels H.OldEdge m)
    (ν : Fin (m + 1))
    (hRange : ∀ i : I, Set.range (β i) =
      {f : H.OldEdge | f.1 ⊆ Set.range (vertex i)}) :
    canonicalFilledSelectedData U H vertex β S ν =
      H.toTrainFilling.inheritedCutData S
        (fun i : I => Set.range (vertex i))
        (fun i : I => {f : H.OldEdge |
          f.1 ⊆ Set.range (vertex i)}) ν := by
  classical
  simp only [canonicalFilledSelectedData,
    TrainFilling.inheritedCutData, hRange]

/-- Transport the checked canonical filled system-girth theorem to
the exact parentwise incidence record, with no assumed output bound.
The OLD bound remains explicit and is supplied by OrderStage in the
actual application. -/
theorem canonicalFilledSelectedData_fullSystemGirthGT_of_inherited
    (H : UniformFillingData Y X)
    (vertex : I → Vertex U ↪ Y)
    (β : I → (C × P) ↪ H.OldEdge)
    {m : ℕ} (S : EdgeTrainLevels H.OldEdge m)
    (ν : Fin (m + 1))
    (hRange : ∀ i : I, Set.range (β i) =
      {f : H.OldEdge | f.1 ⊆ Set.range (vertex i)})
    {g : ℕ}
    (hGirth :
      (H.toTrainFilling.inheritedCutData S
        (fun i : I => Set.range (vertex i))
        (fun i : I => {f : H.OldEdge |
          f.1 ⊆ Set.range (vertex i)}) ν).FullSystemGirthGT g) :
    (canonicalFilledSelectedData U H vertex β S ν).FullSystemGirthGT g := by
  rw [canonicalFilledSelectedData_eq_inheritedCutData
    U H vertex β S ν hRange]
  exact hGirth

/-- Full system girth of the actual labelled (parent,choice)
family follows from the SAME inherited canonical filling record,
using only physical filled-edge carrier equality. No pointwise
coordinate identity or output girth is a premise of scattering. -/
theorem canonicalFilledSelected_targetFullSystemGirthGT_of_inherited_carrier
    (H : UniformFillingData Y X)
    (hTemplate : ∀ c : C, (U c).templateEdges = H.templateEdges)
    (vertex : I → Vertex U ↪ Y)
    (β : I → (C × P) ↪ H.OldEdge)
    {m : ℕ} (T : EdgeTrainLevels P m) (hm : 0 < m)
    (S : EdgeTrainLevels H.OldEdge m)
    (ν : Fin (m + 1)) (hProper : ν.val < m)
    (hLocal : ∀ c : C, Nonempty (U c).LocalEdge)
    (hFaithful : ∀ i : I, ∀ a b : C × P,
      (contractedChoiceTrain U T hm).rel ν a b ↔
        S.rel ν (β i a) (β i b))
    (hEdgeCarrier : ∀ (i : I) (a : Edge U),
      (selectedIndexedFilledEdgeEmbedding U H hTemplate (β i) a).1 =
        vertex i '' edgeCarrier U a)
    (hRange : ∀ i : I, Set.range (β i) =
      {f : H.OldEdge | f.1 ⊆ Set.range (vertex i)})
    {g : ℕ}
    (hGirth :
      (H.toTrainFilling.inheritedCutData S
        (fun i : I => Set.range (vertex i))
        (fun i : I => {f : H.OldEdge |
          f.1 ⊆ Set.range (vertex i)}) ν).FullSystemGirthGT g) :
    (((canonicalFilledSelectedFaithfulRealization_of_carrier U H hTemplate
        vertex β T hm S ν hProper hLocal hFaithful hEdgeCarrier)
        .toParentwiseRealization).designatedFamily.target).FullSystemGirthGT g := by
  have hBound :
      (canonicalFilledSelectedData U H vertex β S ν).FullSystemGirthGT g :=
    canonicalFilledSelectedData_fullSystemGirthGT_of_inherited
      U H vertex β S ν hRange hGirth
  exact (canonicalFilledSelectedFaithfulRealization_of_carrier
    U H hTemplate vertex β T hm S ν hProper hLocal
      hFaithful hEdgeCarrier).target_fullSystemGirthGT hBound

end StructuralRamsey.Girth.IndexedPrivateChoice
