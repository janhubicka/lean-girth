import Girth.TrainFillingIndexedActualMPhysicalTrain
import Girth.TrainBottomOrdinaryLabelledGirth
import Girth.ForestRecursiveOutputGirth
import Girth.TrainRecursiveWitnessPass

set_option Elab.async false

/-!
# The genuine shorter witness at the OLD equality cut

At train cut zero, two physical support edges are in one wagon iff
their actual occurrence labels are equal. Thus the true quotient
wagon label sort is canonically equivalent to the complete
OldACarrierEdge A N type, and each quotient wagon has precisely
its own physical edge as carrier.

The shorter witness's bottomForest controls every physical A-edge
of N, so its complete support has ordinary girth above the head
cutoff. Physical A-support labels are actual carrier subtypes and
hence injective; the existing labelled-girth lemma gives a
labelled girth bound at this equality cut.

This does NOT itself give the entire A2/A3 FullSystemGirthGT at cut
zero. The real remaining obligation is simultaneous supremeness
for acceptable twice-order-bounded cycles (rather than merely
ordinary/labelled cut girth). No stronger claim is made.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v
variable {E W : Type v}

/-- Genuine bottom train wagon names are exactly the physical
edge occurrence labels. No unused or duplicate wagon is introduced. -/
noncomputable def EdgeTrainLevels.bottomWagonEquiv
    {m : ℕ} (T : EdgeTrainLevels E m) :
    Quotient (T.wagonSetoid (0 : Fin (m + 1))) ≃ E := by
  let toEdge :
      Quotient (T.wagonSetoid (0 : Fin (m + 1))) → E :=
    fun q => Quotient.liftOn q id (by
      intro a b hab
      exact (T.bottom a b).mp hab)
  let toWagon : E →
      Quotient (T.wagonSetoid (0 : Fin (m + 1))) :=
    fun e => Quotient.mk _ e
  refine ⟨toEdge, toWagon, ?_, ?_⟩
  · intro q
    induction q using Quotient.inductionOn with
    | h e => rfl
  · intro e
    rfl

/-- At bottom equality, the entire wagon carrier of a true quotient
label is literally the physical edge represented by the label. -/
theorem EdgeTrainLevels.bottom_wagonClassCarrier
    {m : ℕ} (T : EdgeTrainLevels E m)
    (edge : E → Set W)
    (q : Quotient (T.wagonSetoid (0 : Fin (m + 1)))) :
    T.wagonClassCarrier edge 0 q =
      edge (T.bottomWagonEquiv q) := by
  induction q using Quotient.inductionOn with
  | h e =>
    change T.wagonCarrier edge 0 e = edge e
    ext x
    constructor
    · rintro ⟨b, hRel, hx⟩
      have heq : e = b := (T.bottom e b).mp hRel
      simpa only [← heq] using hx
    · intro hx
      exact ⟨e, (T.bottom e e).mpr rfl, hx⟩

/-- The complete labelled horizontal girth bound at the actual old
equality cut follows just from ordinary girth on all physical
support edge labels. It does not assert a system-girth/supremeness
certificate at this cut. -/
theorem EdgeTrainLevels.bottom_labelledCutGirth_of_physical
    {m : ℕ} (T : EdgeTrainLevels E m)
    (edge : E → Set W) (g : ℕ)
    (hPhysical : LabelledGirthGT edge g) :
    LabelledGirthGT (T.wagonClassCarrier edge 0) g := by
  have hReindex : LabelledGirthGT
      (fun q : Quotient (T.wagonSetoid (0 : Fin (m + 1))) =>
        edge (T.bottomWagonEquiv q)) g :=
    labelledGirthGT_of_injective_reindex edge T.bottomWagonEquiv
      T.bottomWagonEquiv.injective g hPhysical
  have hEq : T.wagonClassCarrier edge 0 =
      (fun q => edge (T.bottomWagonEquiv q)) := by
    funext q
    exact T.bottom_wagonClassCarrier edge q
  rw [hEq]
  exact hReindex

namespace TrainRecursiveWitness

variable {L : RelLanguage.{u}} {UA VB P : Type v}
variable {A : RelStructure L UA} {B : RelStructure L VB}
variable {D : RelStructure L P}
variable {family : Set (Embedding B D)} {t : List ℕ}
variable {targetTrain : EdgeTrainLevels (OldACarrierEdge A B) t.length}
variable {allowed : Fin (t.length + 1) → Set P}

/-- The genuine shortened ForestTailStage itself supplies the old
equality cut's complete LABELLED girth (not FullSystemGirthGT).
The mixed forest hypothesis is applied to every physical A-edge,
not just edges lying inside a selected target. -/
theorem ForestTailStage.oldEqualityCut_labelledGirth
    (stage : ForestTailStage A B D family t targetTrain allowed) :
    LabelledGirthGT
      (stage.train.wagonClassCarrier
        (fun e : OldACarrierEdge A stage.system.toRelStructure => e.1)
        (0 : Fin (t.length + 1)))
      (t.headD 0) := by
  have hSupport :
      GirthGT (supportCopies A stage.system.toRelStructure)
        (t.headD 0) := by
    apply girthGT_of_finiteMixedForestThrough _ _
      (t.headD 0) stage.bottomForest
    rintro edge ⟨a, rfl⟩
    exact Or.inl ⟨a, rfl⟩
  have hPhysical :
      LabelledGirthGT
        (fun e : OldACarrierEdge A stage.system.toRelStructure => e.1)
        (t.headD 0) :=
    physicalASupport_labelledGirth_of_girth A stage.system.toRelStructure
      (t.headD 0) hSupport
  exact stage.train.bottom_labelledCutGirth_of_physical
    (fun e : OldACarrierEdge A stage.system.toRelStructure => e.1)
    (t.headD 0) hPhysical

end TrainRecursiveWitness
end StructuralRamsey.Girth
