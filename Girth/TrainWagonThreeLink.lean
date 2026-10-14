import Girth.TrainWagonPairUniqueness
import Girth.TrainPhysicalPictureGeneratedTrain

/-!
# Circulation: a three-link path through the generated wagon quotient

The simplified two-standard lemma needs only FORWARD generation:
old-standard wagon class -> genuine shared edge -> one core wagon
-> another genuine shared edge -> old-standard wagon class.

No converse/exact restriction, wagon-tag representation, or
additional global cycle is needed for this elementary implication.
We first prove it for arbitrary core/standard edge generators and
then instantiate it at every physical picture train cut.

This is the quotient component only; geometry is provided by the
separate wagon-pair uniqueness lemma, while identifying the local
copies in a genuine partite step remains a separate obligation.
No appendix.
-/

namespace StructuralRamsey.Girth

universe u v w x y z

/-- A short path in the *generated* equivalence: one standard step,
one core step, and another standard step, joined at actual physical
shared edges. Purely algebraic and independent of exactness. -/
theorem pictureWagonGenerated_three_link
    {E : Type u} {Core : Type v} {Old : Type w}
    {I : Type x} {CoreEdge : Type y} {OldEdge : Type z}
    (coreEmbed : CoreEdge → E)
    (std : I → OldEdge → E)
    (coreClass : CoreEdge → Core)
    (oldClass : OldEdge → Old)
    (i j : I)
    (a a' b' b : OldEdge) (u v : CoreEdge)
    (hA : oldClass a = oldClass a')
    (hSharedA : std i a' = coreEmbed u)
    (hCore : coreClass u = coreClass v)
    (hSharedB : coreEmbed v = std j b')
    (hB : oldClass b' = oldClass b) :
    TrainEdgeGenerated
      (PictureWagonStep coreEmbed std coreClass oldClass)
      (std i a) (std j b) := by
  let step := PictureWagonStep coreEmbed std coreClass oldClass
  have hFirst : TrainEdgeGenerated step (std i a) (std i a') :=
    TrainEdgeGenerated.basic _ _
      (PictureWagonStep.standard i a a' hA)
  have hMiddle : TrainEdgeGenerated step (coreEmbed u) (coreEmbed v) :=
    TrainEdgeGenerated.basic _ _
      (PictureWagonStep.core u v hCore)
  have hLast : TrainEdgeGenerated step (std j b') (std j b) :=
    TrainEdgeGenerated.basic _ _
      (PictureWagonStep.standard j b' b hB)
  rw [hSharedA] at hFirst
  rw [hSharedB] at hMiddle
  exact TrainEdgeGenerated.transitive _ _ _
    (TrainEdgeGenerated.transitive _ _ _ hFirst hMiddle) hLast

universe v0

/-- At ANY physical picture train cut, two standard edges become
wagon-equivalent whenever their old wagons each contain a genuine
shared edge and the two core images lie in the same core wagon.
This is the exact three-link route used in Section 12. -/
theorem physicalPictureGeneratedTrain_three_link
    {Shared OldEdge CoreEdge I : Type v0} {m : ℕ}
    (oldTrain : EdgeTrainLevels OldEdge m)
    (coreTrain : EdgeTrainLevels CoreEdge m)
    (inOld : Shared ↪ OldEdge)
    (inCore : I → Shared ↪ CoreEdge)
    (hShared : ∀ i : I, Nonempty Shared)
    (μ : Fin (m + 1)) (i j : I)
    (a b : OldEdge) (s t : Shared)
    (hA : oldTrain.rel μ a (inOld s))
    (hCore : coreTrain.rel μ (inCore i s) (inCore j t))
    (hB : oldTrain.rel μ (inOld t) b) :
    (physicalPictureGeneratedTrain oldTrain coreTrain
      inOld inCore hShared).rel μ
      (physicalStandardEdge inOld inCore i a)
      (physicalStandardEdge inOld inCore j b) := by
  have hChain :=
    pictureWagonGenerated_three_link
      (physicalCoreEdge inOld I)
      (physicalStandardEdge inOld inCore)
      (fun d : CoreEdge =>
        Quotient.mk (coreTrain.wagonSetoid μ) d)
      (fun d : OldEdge =>
        Quotient.mk (oldTrain.wagonSetoid μ) d)
      i j a (inOld s) (inOld t) b
      (inCore i s) (inCore j t)
      (Quotient.sound hA)
      (physicalStandardEdge_shared inOld inCore i s)
      (Quotient.sound hCore)
      (physicalStandardEdge_shared inOld inCore j t).symm
      (Quotient.sound hB)
  exact (physicalPictureGeneratedTrain_rel_iff
    oldTrain coreTrain inOld inCore hShared μ _ _).2
      (by simpa only [physicalPictureCutStep] using hChain)

end StructuralRamsey.Girth
