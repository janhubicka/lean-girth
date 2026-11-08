import Girth.ForestToSupremeActualGeometry
import Girth.TrainBigCycleOrderBudget
import Girth.TrainRecursiveWitnessPass

set_option Elab.async false

/-!
# A sufficient *doubled* bottom-forest budget for full system girth

The true FullSystemGirthGT q predicate requires a simultaneous
supreme replacement for EVERY acceptable big cycle of twice-order
at most 2*q, in addition to physical pretrain linearity.

For any such cycle, its number of actual occurrences is at most its
twice-order, hence at most 2*q. The checked bottom forest-to-supreme
lemma therefore applies if the selected mixed-copy forest property
is available through **2*q**, not merely q.

This exposes a valid sufficiency criterion for the delicate equality
cut without mistaking labelled horizontal girth for full A2/A3
simultaneous supremeness. Crucially, the ordinary ForestTailStage
carries bottomForest only through its own head bound. We make the
extra 2*q forest assumption VISIBLE instead of pretending it follows
from the shorter witness. Either constructing that stronger forest
budget or proving a tighter owner/support compression remains open.

The source designated copies are assumed rigid and non-single-edge,
as in the already checked selected-picture forest theorem. No new
irreducibility, output girth, or global replacement plan is assumed.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}} {UA VB P X : Type v}
variable (A : RelStructure L UA) (B : RelStructure L VB)
variable (D : RelStructure L P)
variable (C : StructuralRamsey.Partite.System L P X)
variable (family : Set (Embedding B D))
variable (selected : Set (DesignatedCopy B D C family))
variable {m : ℕ} (T : EdgeTrainLevels (OldACarrierEdge A C.toRelStructure) m)

/-- A mixed forest certificate through 2*q gives TRUE bottom
FullSystemGirthGT q, with both physical linearity and simultaneous
supremeness of all acceptable A1--A3 cycles of the prescribed
twice-order budget.

The factor two is explicit. This is not a claim that the ordinary
stage bottomForest(q) already supplies bottom FullSystemGirthGT(q). -/
theorem selectedPicture_bottom_fullSystemGirthGT_of_doubleForest
    [Nontrivial UA]
    (hLinear : ALinear A C.toRelStructure)
    (hRigid : ∀ b c : Embedding B C.toRelStructure,
      SameCopy b c → b = c)
    (a b : Embedding A B) (hne : ¬ SameCopy a b)
    (q : ℕ)
    (hDoubleForest : FiniteMixedForestThrough
      (RelationalMixedSupportTest A
        (fun z : {x : DesignatedCopy B D C family // x ∈ selected} =>
          z.1.embedding)) (2 * q)) :
    (selectedPictureOrderOneData A B D C family selected T
      (0 : Fin (m + 1))).FullSystemGirthGT q := by
  let O := selectedPictureOrderOneData A B D C family selected T
    (0 : Fin (m + 1))
  let H : O.BottomForestGeometry :=
    selectedPicture_bottomForestGeometry A B D C family selected T hLinear
  change O.FullSystemGirthGT q
  refine ⟨OrderOneData.BottomForestGeometry.linearPretrain O H, ?_⟩
  intro n cycle hAccept hOrder
  have hLength : n ≤ 2 * q :=
    cycle.length_le_twiceOrder.trans hOrder
  exact selectedPicture_bottom_cycle_supreme_of_mixedForest
    A B D C family selected T hLinear hRigid a b hne
    (2 * q) hDoubleForest cycle hAccept hLength

namespace TrainRecursiveWitness

variable {A : RelStructure L UA} {B : RelStructure L VB}
variable {D : RelStructure L P}
variable {family : Set (Embedding B D)} {t : List ℕ}
variable {targetTrain : EdgeTrainLevels (OldACarrierEdge A B) t.length}
variable {allowed : Fin (t.length + 1) → Set P}

/-- The genuine shorter witness's selected bottom incidence satisfies
full A2/A3 system girth when it ALSO has an explicitly supplied
forest-through-2q certificate.

That certificate is stronger than the usual stage.bottomForest(q)
field, so the theorem does not smuggle in an unproved bottom step. -/
theorem ForestTailStage.bottom_fullSystemGirthGT_of_doubleForest
    [Nontrivial UA]
    (S : ForestTailStage A B D family t targetTrain allowed)
    (hRigid : ∀ b c : Embedding B S.system.toRelStructure,
      SameCopy b c → b = c)
    (a b : Embedding A B) (hne : ¬ SameCopy a b)
    (q : ℕ)
    (hDoubleForest : FiniteMixedForestThrough
      (RelationalMixedSupportTest A
        (fun z : {x : DesignatedCopy B D S.system family // x ∈ S.selected} =>
          z.1.embedding)) (2 * q)) :
    (selectedPictureOrderOneData A B D S.system family S.selected
      S.train (0 : Fin (t.length + 1))).FullSystemGirthGT q :=
  selectedPicture_bottom_fullSystemGirthGT_of_doubleForest
    A B D S.system family S.selected S.train S.aLinear
    hRigid a b hne q hDoubleForest

end TrainRecursiveWitness
end StructuralRamsey.Girth
