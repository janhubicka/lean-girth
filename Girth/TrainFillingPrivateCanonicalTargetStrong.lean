import Girth.TrainFillingPrivateCanonicalParentwise
import Girth.TrainFillingPrivateActualParentStrong
import Girth.TrainDesignatedSubcopyStrong

set_option Elab.async false

/-!
# Strong inducedness of actual labelled selected targets

A filled physical H-edge meeting a selected old parent twice
has its UNIQUE old N-cover meeting the parent twice. Genuine
old A-strongness then puts the cover in the old selected
parent, so that the new H-edge belongs to its exact full
cover-pullback edge family.

The checked component-scattering theorem upgrades this OLD
parent strongness to the actual (old parent, EHN choice) target
when the component-local strongness and edge coverage hold.
Those component properties are already constructed by the
checked IndexedPrivateChoice.ParentwiseRealization modules.

This isolates the exact last part of "strongly induced designated
target" in the cutoff-two lemma. It never assumes the output
target is already strong and does not remove unused ambient H edges.

These declarations are candidate Lean source, not kernel checked.
-/

namespace StructuralRamsey.Girth.IndexedPrivateChoice

universe v
variable {C V P X Y I Q GQ : Type v}
variable (U : C → PrivateWagonInput V P X)

/-- In the canonical full filled incidence record the strongness
condition for an OLD parent is obtained by transporting distinct
common vertices to the UNIQUE old cover and applying its actual
old strongness. No containment of the new H-edge is hypothesized. -/
theorem canonicalFilledSelectedData_parentStrong
    (H : UniformFillingData Y X)
    (vertex : I → Vertex U ↪ Y)
    (β : I → (C × P) ↪ H.OldEdge)
    {m : ℕ} (S : EdgeTrainLevels H.OldEdge m)
    (ν : Fin (m + 1))
    (hOldStrong : ∀ i : I, ∀ f : H.OldEdge,
      ¬ (f.1 ∩ Set.range (vertex i)).Subsingleton →
        f ∈ Set.range (β i))
    (i : I) :
    ∀ (e : H.toTrainFilling.NewEdge) (x y : Y),
      x ≠ y →
      x ∈ (canonicalFilledSelectedData U H vertex β S ν).edgeCarrier e →
      y ∈ (canonicalFilledSelectedData U H vertex β S ν).edgeCarrier e →
      x ∈ (canonicalFilledSelectedData U H vertex β S ν).copyCarrier i →
      y ∈ (canonicalFilledSelectedData U H vertex β S ν).copyCarrier i →
      e ∈ (canonicalFilledSelectedData U H vertex β S ν).copyEdges i := by
  intro e x y hxy hxE hyE hxParent hyParent
  change H.toTrainFilling.cover e ∈ Set.range (β i)
  apply hOldStrong i (H.toTrainFilling.cover e)
  intro hSmall
  exact hxy (hSmall
    ⟨H.toTrainFilling.contained e hxE, hxParent⟩
    ⟨H.toTrainFilling.contained e hyE, hyParent⟩)

/-- Reuse the CHECKED scattering strongness theorem. The complete
parentwise realization already builds sibling-disjoint components,
their correct edge cover, and the local strongness/pointwise
coverage of the selected target in every component. -/
theorem ParentwiseRealization.targetStrong_of_parentStrong
    {GVertex GEdge : Type v}
    {D : OrderOneData GVertex GEdge I GQ}
    {parent : P → Q}
    (R : ParentwiseRealization U parent D)
    (hParentStrong : ∀ i : I, ∀ (e : GEdge) (x y : GVertex),
      x ≠ y →
      x ∈ D.edgeCarrier e → y ∈ D.edgeCarrier e →
      x ∈ D.copyCarrier i → y ∈ D.copyCarrier i →
      e ∈ D.copyEdges i)
    (j : R.Target) :
    ∀ (e : GEdge) (x y : GVertex),
      x ≠ y →
      x ∈ D.edgeCarrier e → y ∈ D.edgeCarrier e →
      x ∈ R.targetCarrier j → y ∈ R.targetCarrier j →
      e ∈ R.targetEdges j := by
  exact (R.componentDecomposition.target_strong_of_parent_strong
    j (R.componentGeometry j) rfl (hParentStrong j.1))

/-- Each resulting ACTUAL labelled target (old parent, EHN choice)
is strongly induced in the unchanged full ambient H, provided the
old selected N parents have their genuine strongness condition.

No arbitrary output "target strongness" field appears: the source
hypothesis concerns only old physical N edges, and this theorem
derives the complete strongness of the selected H target using
the already checked generic scattering constructor. -/
theorem canonicalFilledSelected_targetStrong
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
    (hOldStrong : ∀ i : I, ∀ f : H.OldEdge,
      ¬ (f.1 ∩ Set.range (vertex i)).Subsingleton →
        f ∈ Set.range (β i))
    (j : I × C) :
    let R := canonicalFilledSelectedFaithfulRealization_of_carrier
      U H hTemplate vertex β T hm S ν hProper hLocal hFaithful
        hEdgeCarrier
    ∀ (e : H.toTrainFilling.NewEdge) (x y : Y),
      x ≠ y → x ∈ e.1 → y ∈ e.1 →
      x ∈ R.toParentwiseRealization.targetCarrier j →
      y ∈ R.toParentwiseRealization.targetCarrier j →
      e ∈ R.toParentwiseRealization.targetEdges j := by
  let R := canonicalFilledSelectedFaithfulRealization_of_carrier
    U H hTemplate vertex β T hm S ν hProper hLocal hFaithful
      hEdgeCarrier
  apply R.toParentwiseRealization.targetStrong_of_parentStrong
  intro i e x y hxy hxE hyE hxParent hyParent
  exact canonicalFilledSelectedData_parentStrong U H vertex β S ν
    hOldStrong i e x y hxy hxE hyE hxParent hyParent

end StructuralRamsey.Girth.IndexedPrivateChoice
