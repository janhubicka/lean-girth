import Girth.TrainFillingSelectedEdgeRange
import Girth.TrainFillingFaithfulWagonMap
import Girth.TrainFillingInheritedTrain

set_option Elab.async false

/-!
# Faithful inherited proper-cut wagons for a selected contracted copy

The selected old M-copy has a physical old-edge embedding β into the old
N hypergraph. At a proper old cut ν, it preserves and reflects the actual
old train relation. The filled physical-edge embedding is then the
previously constructed edgeEquiv (β(s), templateEdge).

At restored cut ν.succ, the inherited relation is the pullback of the
old relation along the physical cover. Consequently the selected
filled-edge map preserves AND REFLECTS exact wagon-parent equality.

With a nonempty template-edge type, every source quotient wagon has a
physical filled-edge representative. The checked FaithfulPhysicalWagonMap
then constructs the actual injective quotient-wagon map without assuming
one. In particular, there is no surjectivity requirement on ambient wagons,
no top-cut system-girth assertion and no ambient edge pruning.

The remaining application must instantiate the old relation reflection
for the genuine selected contracted M-copy in N.
-/

namespace StructuralRamsey.Girth.UniformFillingData

universe v
variable {V X S : Type v} (U : UniformFillingData V X)
variable {m : ℕ} (T : EdgeTrainLevels U.OldEdge m)

/-- The nonempty local-template-edge hypothesis needed for quotient-wagon
representatives follows from pointwise coverage whenever the uniform
Ramsey template has at least one vertex. It is not an independent
geometric premise in the intended cutoff-two application. -/
theorem nonempty_templateEdge_of_nonempty [Nonempty X] : Nonempty U.TemplateEdge := by
  obtain ⟨x⟩ := (inferInstance : Nonempty X)
  obtain ⟨a, _⟩ := U.template_covers x
  exact ⟨a⟩

/-- A selected old edge embedding faithfully reflects the specified old
wagon relation. No new-filled-wagon hypothesis is supplied. -/
noncomputable def selectedFilledFaithfulWagonMap
    (β : S ↪ U.OldEdge)
    (G : EdgeTrainLevels S m)
    (ν : Fin (m + 1))
    [Nonempty U.TemplateEdge]
    (hOldFaithful : ∀ s t : S,
      G.rel ν s t ↔ T.rel ν (β s) (β t)) :
    FaithfulPhysicalWagonMap
      (S × U.TemplateEdge)
      U.toTrainFilling.NewEdge
      (Quotient (G.wagonSetoid ν))
      (Quotient ((U.toTrainFilling.inheritedTrain T).wagonSetoid ν.succ)) where
  localParent := fun c => Quotient.mk (G.wagonSetoid ν) c.1
  ambientParent := fun e =>
    Quotient.mk ((U.toTrainFilling.inheritedTrain T).wagonSetoid ν.succ) e
  edge := U.selectedFilledEdgeEmbedding β
  local_surjective := by
    intro q
    induction q using Quotient.inductionOn with
    | h s =>
      obtain ⟨a⟩ := (inferInstance : Nonempty U.TemplateEdge)
      exact ⟨(s, a), rfl⟩
  parent_iff := by
    intro a b
    constructor
    · intro h
      have hSource : G.rel ν a.1 b.1 := Quotient.exact h
      have hTarget : T.rel ν (β a.1) (β b.1) :=
        (hOldFaithful a.1 b.1).mp hSource
      apply Quotient.sound
      apply (U.toTrainFilling.inheritedTrain_rel_succ T ν
        (U.selectedFilledEdgeEmbedding β a)
        (U.selectedFilledEdgeEmbedding β b)).mpr
      simpa only [U.selectedFilledEdgeEmbedding_cover] using hTarget
    · intro h
      have hInherited :
          (U.toTrainFilling.inheritedTrain T).rel ν.succ
            (U.selectedFilledEdgeEmbedding β a)
            (U.selectedFilledEdgeEmbedding β b) := Quotient.exact h
      have hTarget := (U.toTrainFilling.inheritedTrain_rel_succ T ν
        (U.selectedFilledEdgeEmbedding β a)
        (U.selectedFilledEdgeEmbedding β b)).mp hInherited
      have hOld : T.rel ν (β a.1) (β b.1) := by
        simpa only [U.selectedFilledEdgeEmbedding_cover] using hTarget
      exact Quotient.sound ((hOldFaithful a.1 b.1).mpr hOld)

/-- The selected filled physical-edge embedding therefore determines
its own injective ambient quotient-wagon map at each restored cut. -/
noncomputable def selectedFilledWagonEmbedding
    (β : S ↪ U.OldEdge)
    (G : EdgeTrainLevels S m) (ν : Fin (m + 1))
    [Nonempty U.TemplateEdge]
    (hOldFaithful : ∀ s t : S,
      G.rel ν s t ↔ T.rel ν (β s) (β t)) :
    Quotient (G.wagonSetoid ν) ↪
      Quotient ((U.toTrainFilling.inheritedTrain T).wagonSetoid ν.succ) :=
  (U.selectedFilledFaithfulWagonMap T β G ν hOldFaithful).wagonEmbedding

/-- The reconstructed wagon map commutes literally with the actual
source and restored ambient parent maps on every filled physical edge. -/
theorem selectedFilledWagonEmbedding_parent
    (β : S ↪ U.OldEdge)
    (G : EdgeTrainLevels S m) (ν : Fin (m + 1))
    [Nonempty U.TemplateEdge]
    (hOldFaithful : ∀ s t : S,
      G.rel ν s t ↔ T.rel ν (β s) (β t))
    (a : S × U.TemplateEdge) :
    U.selectedFilledWagonEmbedding T β G ν hOldFaithful
      (Quotient.mk (G.wagonSetoid ν) a.1) =
    Quotient.mk ((U.toTrainFilling.inheritedTrain T).wagonSetoid ν.succ)
      (U.selectedFilledEdgeEmbedding β a) := by
  exact (U.selectedFilledFaithfulWagonMap T β G ν hOldFaithful).wagonEmbedding_parent a

end StructuralRamsey.Girth.UniformFillingData
