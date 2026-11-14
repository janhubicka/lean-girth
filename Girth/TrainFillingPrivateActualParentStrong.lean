import Girth.TrainFillingPrivateActualOrderParent
import Girth.TrainFillingSelectedEdgeRange

set_option Elab.async false

/-!
# A selected shorter OrderStage parent is strong after FULL filling

The selected lower M-copy b is A-strong in the actual N output
of the shorter OrderStage. The complete old-edge range of b is
the set of ALL ambient N A-support edges contained in b(M).

Every filled H=N[X] physical edge has at least two vertices,
since X has the nontrivial coloured edge type. Consequently a
filled H-edge lying inside b(M) has an old cover meeting b(M)
twice. The old A-strongness forces this cover into the full
old-edge image of b, and EVERY filled edge over that cover is
part of b[X]. This proves actual strong inducedness of the
selected filled parent.

The theorem reuses the checked
  UniformFillingData.selectedFilledEdgeEmbedding_range_eq_contained
rather than re-proving old-cover/cycle geometry. The complete
ambient H edge type remains unchanged, and no output girth
or selected T-copy strongness is assumed.
-/

namespace StructuralRamsey.Girth.IndexedPrivateChoice

open StructuralRamsey.RelStructure

universe u v

variable {L : RelLanguage.{u}}
variable {C V P X UA : Type v}
variable (U : C → PrivateWagonInput V P X)

/-- A genuine selected shorter OrderStage copy, with its actual
full A-support old edges, owns PRECISELY those filled H-edges
whose entire carriers lie inside the selected parent vertex set.

This is the correct parent strongness needed before applying the
existing local-to-global scattering theorem to the (parent,choice)
designated target copies. -/
theorem actualOrderParent_filledEdges_eq_contained [Nontrivial X]
    (A : RelStructure L UA)
    (M : RelStructure L (Vertex U))
    {t : List ℕ} (T : EdgeTrainLevels P t.length) (hm : 0 < t.length)
    (hSupport : supportCopies A M = Set.range (contractedCarrier U))
    (hLinear : ∀ c : C, ∀ p q : P, p ≠ q →
      ((U c).oldCarrier p ∩ (U c).oldCarrier q).Subsingleton)
    {Base : Type v} (D : RelStructure L Base)
    (family : Set (Embedding M D))
    (allowed : Fin (t.length + 1) → Set Base)
    (S : TrainRecursiveWitness.OrderStage A M D family t
      (contractedPhysicalTrain U A M T hm hSupport hLinear) allowed)
    (H : UniformFillingData S.Vertex X)
    (hOld : H.oldEdges = supportCopies A S.system.toRelStructure)
    (i : ActualOrderParent U A M T hm
      hSupport hLinear D family allowed S) :
    Set.range (H.selectedFilledEdgeEmbedding
      (actualOrderParentOldEdge U A M T hm
        hSupport hLinear D family allowed S H hOld i)) =
      {e : H.toTrainFilling.NewEdge |
        e.1 ⊆ Set.range
          (actualOrderParentVertex U A M T hm
            hSupport hLinear D family allowed S i)} := by
  let β := actualOrderParentOldEdge U A M T hm
    hSupport hLinear D family allowed S H hOld i
  have hRange : Set.range β =
      {f : H.OldEdge | f.1 ⊆ copyCarrier i.1.embedding} :=
    actualOrderParentOldEdge_range_eq_contained U A M T hm
      hSupport hLinear D family allowed S H hOld i
  have hSelectedContained : ∀ cp : C × P,
      (β cp).1 ⊆ copyCarrier i.1.embedding := by
    intro cp
    have hMem : β cp ∈ Set.range β := ⟨cp, rfl⟩
    exact (hRange.mp hMem)
  have hOldStrong : ∀ f : H.OldEdge,
      ¬ (f.1 ∩ copyCarrier i.1.embedding).Subsingleton →
        f ∈ Set.range β := by
    intro f hMeet
    have hfSupport : f.1 ∈ supportCopies A S.system.toRelStructure := by
      rw [← hOld]
      exact f.2
    obtain ⟨a, ha⟩ := hfSupport
    have hMeetA :
        ¬ (copyCarrier a ∩ copyCarrier i.1.embedding).Subsingleton := by
      rw [← ha]
      exact hMeet
    have hInside : copyCarrier a ⊆ copyCarrier i.1.embedding :=
      S.toForestTailStage.strong i.1 i.2 a hMeetA
    apply hRange.mpr
    rw [ha]
    exact hInside
  change Set.range (H.selectedFilledEdgeEmbedding β) =
    {e : H.toTrainFilling.NewEdge |
      e.1 ⊆ copyCarrier i.1.embedding}
  exact H.selectedFilledEdgeEmbedding_range_eq_contained β
    (copyCarrier i.1.embedding) hSelectedContained hOldStrong

end StructuralRamsey.Girth.IndexedPrivateChoice
