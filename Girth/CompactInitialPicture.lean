import Girth.TrainRecursiveInitialTailSystem
import Girth.ForestRecursiveInitialMixed
import Girth.TrainRecursiveBottomEqualityBridge

/-!
# Picture zero: all system bounds together with the bottom mixed forest

The compact paper uses both conclusions of picture zero in its conversion
and recursive initialization.  The existing initial-system theorem works
at every proper cut, whereas the existing finite-stage interface records
only its positive cuts.  This file closes that interface gap at the bottom:
ordinary target support girth gives labelled bottom-cut girth because the
bottom train relation is equality of physical edges.  Consequently the
same literal initial picture has full system girth at every requested cut
and the complete mixed bottom forest bound.

The forest conclusion includes every ambient A-copy, not just the chosen
target components.  Its existing proof uses a star only when the selected
component centre is present; otherwise it uses the target edge girth.  It
never removes an unselected centre from a join tree.

No system-girth or forest conclusion for the initial picture is assumed.
The hypotheses are target support girth and target positive labelled-cut
girth.  Finiteness of the target is used only by the forest theorem.
Neither a nondecreasing cutoff vector nor target support coverage is needed
for these two initial-picture conclusions.
-/

namespace StructuralRamsey.Girth.TrainRecursiveWitness

universe u v
variable {L : RelLanguage.{u}} {UA VB P : Type v}

/-- The physical bottom cut of the initial picture has full system girth
from ordinary target support girth; no separate labelled bottom premise is
needed because the train's bottom quotient is its physical edge type. -/
theorem initial_bottomSystemGirth_of_supportGirth
    (A : RelStructure L UA) (hA : A.Irreducible) [Nonempty UA]
    (B : RelStructure L VB) [Nonempty VB]
    (D : RelStructure L P)
    (family : Set (RelStructure.Embedding B D)) [Nonempty family]
    {m : ℕ} (T : EdgeTrainLevels (OldACarrierEdge A B) m) (hm : 0 < m)
    (q : ℕ) (hq : 2 ≤ q)
    (hGirth : GirthGT (supportCopies A B) q) :
    (selectedPictureOrderOneData A B D
      (StructuralRamsey.Partite.Initial.picture B
        (fun b : family => b.1.toFunctionEmbedding))
      family (initialSelected B D family)
      (initialTrain A hA B (fun b : family => b.1.toFunctionEmbedding) T hm)
      (⟨0, Nat.zero_lt_succ m⟩ : Fin (m + 1))).FullSystemGirthGT q := by
  exact initialTrain_fullSystemGirth_of_targetCut A hA B D family T hm
    ⟨0, Nat.zero_lt_succ m⟩ hm q hq
    (aLinear_of_girthGT_two A B (girthGT_mono hGirth hq))
    (T.bottom_labelledCutGirth_of_edgeGirth (fun edge => edge.1) q
      (physicalASupport_labelledGirth_of_girth A B q hGirth))

/-- Exact joint conclusion of picture zero on the literal selected initial
picture: all proper-cut full system bounds, including the bottom, and the
mixed forest bound through the head cutoff.  Positive target cut bounds
are labelled; the head input is ordinary physical support girth. -/
theorem initialPicture_systemGirth_and_mixedForest
    (A : RelStructure L UA) (hA : A.Irreducible) [Nonempty UA]
    (B : RelStructure L VB) [Nonempty VB] [Finite VB]
    (D : RelStructure L P)
    (family : Set (RelStructure.Embedding B D)) [Nonempty family]
    (t : List ℕ) (ht : t ≠ [])
    (hTwo : ∀ j : Fin t.length, 2 ≤ t.get j)
    (T : EdgeTrainLevels (OldACarrierEdge A B) t.length)
    (hGirth : GirthGT (supportCopies A B) (t.headD 0))
    (hTargetCuts : ∀ j : Fin t.length, 0 < j.val →
      LabelledGirthGT (T.wagonClassCarrier (fun edge => edge.1) j.castSucc)
        (t.get j)) :
    (∀ j : Fin t.length,
      (selectedPictureOrderOneData A B D
        (StructuralRamsey.Partite.Initial.picture B
          (fun b : family => b.1.toFunctionEmbedding))
        family (initialSelected B D family)
        (initialTrain A hA B (fun b : family => b.1.toFunctionEmbedding)
          T (List.length_pos_iff.mpr ht)) j.castSucc).FullSystemGirthGT (t.get j)) ∧
    FiniteMixedForestThrough
      (testedAB A B D
        (StructuralRamsey.Partite.Initial.picture B
          (fun b : family => b.1.toFunctionEmbedding)) family
        (initialSelected B D family)) (t.headD 0) := by
  have hHeadTwo : 2 ≤ t.headD 0 := by
    cases t with
    | nil => exact (ht rfl).elim
    | cons q tail => exact hTwo ⟨0, Nat.zero_lt_succ tail.length⟩
  constructor
  · intro j
    by_cases hj : j.val = 0
    · have hCut : j.castSucc =
          (⟨0, Nat.zero_lt_succ t.length⟩ : Fin (t.length + 1)) := Fin.ext hj
      have hThreshold : t.get j = t.headD 0 := by
        cases t with
        | nil => exact (ht rfl).elim
        | cons q tail =>
            have hz : j = ⟨0, Nat.zero_lt_succ tail.length⟩ := Fin.ext hj
            subst j
            rfl
      rw [hCut, hThreshold]
      exact initial_bottomSystemGirth_of_supportGirth A hA B D family T
        (List.length_pos_iff.mpr ht) (t.headD 0) hHeadTwo hGirth
    · exact initialTrain_fullSystemGirth_of_targetCut A hA B D family T
        (List.length_pos_iff.mpr ht) j.castSucc j.isLt (t.get j) (hTwo j)
        (aLinear_of_girthGT_two A B (girthGT_mono hGirth hHeadTwo))
        (hTargetCuts j (Nat.pos_of_ne_zero hj))
  · exact initialSelected_mixedForest A hA B D family
      (t.headD 0) hHeadTwo hGirth

end StructuralRamsey.Girth.TrainRecursiveWitness
