import Girth.TrainPictureExtremeCuts
import Girth.TrainPhysicalPictureEdgePushout
import Girth.TrainEquivalenceRestriction
import Girth.TrainWagonClassRestriction

/-!
# The complete hierarchy of generated wagon equivalences in one picture

The real edge-pushout admits a generated equivalence at EACH train
cut: take the equivalence closure of the old standard-wagon and
core-wagon generators at that cut.

We show these equivalences form an actual nested train, with
bottom equality and a universal top provided each attached standard
picture shares an ACTUAL edge with the core. Nesting follows by
inclusion of the elementary generator relations.

No parameter/allowed sibling intersection predicate or acceptable
cycle A1--A3 is inferred merely from the train hierarchy.
-/

namespace StructuralRamsey.Girth

universe v
variable {Shared OldEdge CoreEdge I E : Type v}

/-- Inclusion of elementary edge relations lifts through the
reflexive/symmetric/transitive generated equivalence closure. -/
theorem TrainEdgeGenerated.of_step_mono
    (step1 step2 : E → E → Prop)
    (hMono : ∀ a b, step1 a b → step2 a b)
    {a b : E} (h : TrainEdgeGenerated step1 a b) :
    TrainEdgeGenerated step2 a b := by
  induction h with
  | basic a b hab =>
      exact TrainEdgeGenerated.basic a b (hMono a b hab)
  | reflexive a =>
      exact TrainEdgeGenerated.reflexive a
  | symmetric a b _ ih =>
      exact TrainEdgeGenerated.symmetric a b ih
  | transitive a b c _ _ ihab ihbc =>
      exact TrainEdgeGenerated.transitive a b c ihab ihbc

/-- Elementary generator relation of the physical picture at the
cut μ, with actual old/core quotient ancestor labels. -/
def physicalPictureCutStep
    {m : ℕ}
    (oldTrain : EdgeTrainLevels OldEdge m)
    (coreTrain : EdgeTrainLevels CoreEdge m)
    (μ : Fin (m + 1))
    (inOld : Shared ↪ OldEdge)
    (inCore : I → Shared ↪ CoreEdge) :
    PhysicalPictureEdge inOld I CoreEdge →
      PhysicalPictureEdge inOld I CoreEdge → Prop :=
  PictureWagonStep
    (physicalCoreEdge inOld I)
    (physicalStandardEdge inOld inCore)
    (fun b : CoreEdge => Quotient.mk (coreTrain.wagonSetoid μ) b)
    (fun a : OldEdge => Quotient.mk (oldTrain.wagonSetoid μ) a)

/-- Elementary generators at a finer level are also generators
at any coarser level, by the nesting of old/core wagon relations. -/
theorem physicalPictureCutStep_mono
    {m : ℕ}
    (oldTrain : EdgeTrainLevels OldEdge m)
    (coreTrain : EdgeTrainLevels CoreEdge m)
    (μ ν : Fin (m + 1)) (hμν : μ ≤ ν)
    (inOld : Shared ↪ OldEdge)
    (inCore : I → Shared ↪ CoreEdge) :
    ∀ a b, physicalPictureCutStep oldTrain coreTrain μ inOld inCore a b →
      physicalPictureCutStep oldTrain coreTrain ν inOld inCore a b := by
  intro a b hab
  cases hab with
  | core x y h =>
      exact PictureWagonStep.core x y
        (Quotient.sound
          (coreTrain.nested μ ν hμν x y (Quotient.exact h)))
  | standard i x y h =>
      exact PictureWagonStep.standard i x y
        (Quotient.sound
          (oldTrain.nested μ ν hμν x y (Quotient.exact h)))

/-- The generated wagon hierarchy on one actual physical
picture-edge pushout. Each level is the least equivalence generated
by old standard-wagon and core-wagon equalities at that level.

The top class is universal ONLY because every attached standard
copy has at least one genuine shared physical edge. -/
noncomputable def physicalPictureGeneratedTrain
    {m : ℕ}
    (oldTrain : EdgeTrainLevels OldEdge m)
    (coreTrain : EdgeTrainLevels CoreEdge m)
    (inOld : Shared ↪ OldEdge)
    (inCore : I → Shared ↪ CoreEdge)
    (hShared : ∀ i : I, Nonempty Shared) :
    EdgeTrainLevels (PhysicalPictureEdge inOld I CoreEdge) m where
  rel := fun μ a b =>
    TrainEdgeGenerated
      (physicalPictureCutStep oldTrain coreTrain μ inOld inCore) a b
  equivalent := by
    intro μ
    exact ⟨
      (fun a => TrainEdgeGenerated.reflexive a),
      (fun {a b} h => TrainEdgeGenerated.symmetric a b h),
      (fun {a b c} hab hbc =>
        TrainEdgeGenerated.transitive a b c hab hbc)⟩
  nested := by
    intro μ ν hμν a b hab
    exact TrainEdgeGenerated.of_step_mono
      (physicalPictureCutStep oldTrain coreTrain μ inOld inCore)
      (physicalPictureCutStep oldTrain coreTrain ν inOld inCore)
      (physicalPictureCutStep_mono
        oldTrain coreTrain μ ν hμν inOld inCore)
      hab
  bottom := by
    intro a b
    let μ : Fin (m + 1) := ⟨0, Nat.zero_lt_succ m⟩
    let coreClass : CoreEdge → Quotient (coreTrain.wagonSetoid μ) :=
      fun x => Quotient.mk (coreTrain.wagonSetoid μ) x
    let oldClass : OldEdge → Quotient (oldTrain.wagonSetoid μ) :=
      fun x => Quotient.mk (oldTrain.wagonSetoid μ) x
    have hCoreInj : Function.Injective coreClass := by
      intro x y h
      exact (coreTrain.bottom x y).mp (Quotient.exact h)
    have hOldInj : Function.Injective oldClass := by
      intro x y h
      exact (oldTrain.bottom x y).mp (Quotient.exact h)
    exact pictureWagonGenerated_bottom_eq
      (physicalCoreEdge inOld I)
      (physicalStandardEdge inOld inCore)
      coreClass oldClass hCoreInj hOldInj a b
  top := by
    intro a b
    let μ : Fin (m + 1) := ⟨m, Nat.lt_succ_self m⟩
    let coreClass : CoreEdge → Quotient (coreTrain.wagonSetoid μ) :=
      fun x => Quotient.mk (coreTrain.wagonSetoid μ) x
    let oldClass : OldEdge → Quotient (oldTrain.wagonSetoid μ) :=
      fun x => Quotient.mk (oldTrain.wagonSetoid μ) x
    have hCore : ∀ x y, coreClass x = coreClass y := by
      intro x y
      exact Quotient.sound (coreTrain.top x y)
    have hOld : ∀ x y, oldClass x = oldClass y := by
      intro x y
      exact Quotient.sound (oldTrain.top x y)
    have hCover : ∀ e : PhysicalPictureEdge inOld I CoreEdge,
        (∃ x, e = physicalCoreEdge inOld I x) ∨
        ∃ i x, e = physicalStandardEdge inOld inCore i x :=
      physicalPictureEdge_covered inOld inCore
    have hOverlap : ∀ i : I, ∃ x : OldEdge, ∃ y : CoreEdge,
        physicalStandardEdge inOld inCore i x =
          physicalCoreEdge inOld I y := by
      intro i
      obtain ⟨s⟩ := hShared i
      exact ⟨inOld s, inCore i s,
        physicalStandardEdge_shared inOld inCore i s⟩
    exact pictureWagonGenerated_top_universal
      (physicalCoreEdge inOld I)
      (physicalStandardEdge inOld inCore)
      coreClass oldClass
      hCore hOld hCover hOverlap a b

/-- The generated train's levels are precisely the elementary
core/standard wagon equivalence closures, without inserted
imaginary relations. -/
theorem physicalPictureGeneratedTrain_rel_iff
    {m : ℕ}
    (oldTrain : EdgeTrainLevels OldEdge m)
    (coreTrain : EdgeTrainLevels CoreEdge m)
    (inOld : Shared ↪ OldEdge)
    (inCore : I → Shared ↪ CoreEdge)
    (hShared : ∀ i : I, Nonempty Shared)
    (μ : Fin (m + 1))
    (a b : PhysicalPictureEdge inOld I CoreEdge) :
    (physicalPictureGeneratedTrain oldTrain coreTrain
      inOld inCore hShared).rel μ a b ↔
    TrainEdgeGenerated
      (physicalPictureCutStep oldTrain coreTrain μ inOld inCore) a b :=
  Iff.rfl

end StructuralRamsey.Girth
