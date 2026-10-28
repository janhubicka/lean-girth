import Girth.TrainActualStandardLongReplacement
import Girth.AttachmentLinearity
import Girth.TrainSelectedPictureOutputIncidence

/-!
# No new ambient pair edges inside an A-strong attached standard

For any two DISTINCT old vertices x,y, if their actual output
standard images share one physical A-support edge, then this edge's
A-copy meets the standard in two points. A-strongness of the standard
forces the entire A-copy into that standard; factor the genuine
A-embedding back through the standard embedding. This produces an
actual OLD A-support edge through x,y.

No pair reflection is inferred merely from the word "induced": the
required hypothesis is the exact A-strongness condition. The older
attachment_copy_aStrong theorem derives it when (i) the gluing
subsystem is A-strong in the old picture and (ii) every gluing image
is A-strong in the core. These hypotheses are retained explicitly,
as they must later be discharged by the picture-step induction.

Combining the no-new-pair result with the conditional LongValid
lifting theorem transports each old LONG supreme-replacement piece
without any further geometric axiom. The GLOBAL simultaneous plan
is still an open separate obligation. No appendix.
-/

namespace StructuralRamsey.Girth
open StructuralRamsey.RelStructure

universe u v
section ActualStandardNoNewPair

variable {L : RelLanguage.{u}} {UA VB P X Y I : Type v}
variable (A : RelStructure L UA) (hA : A.Irreducible)
variable (B : RelStructure L VB) (D : RelStructure L P)
variable (C : StructuralRamsey.Partite.System L P X)
variable (family : Set (RelStructure.Embedding B D))
variable (selected : Set (DesignatedCopy B D C family))
variable (e : RelStructure.Embedding A D) (R : RelStructure L Y)
variable (f : I → RelStructure.Embedding
  (C.toRelStructure.induce (activeCarrier A C e.toFunctionEmbedding)) R)
variable {m : ℕ}
variable (T : EdgeTrainLevels (OldACarrierEdge A C.toRelStructure) m)
variable (U : EdgeTrainLevels (OldACarrierEdge A R) m)
variable (hShared : ∀ _i : I, Nonempty (SharedOldACarrierEdge A C.toRelStructure
  (activeCarrier A C e.toFunctionEmbedding)))
variable (hRel : ∀ (ν : Fin (m + 1)) (j : I)
  (p q : SharedOldACarrierEdge A C.toRelStructure
    (activeCarrier A C e.toFunctionEmbedding)),
  T.rel ν p.1 q.1 ↔
    U.rel ν (sharedOldACarrierCoreEmbedding A C.toRelStructure
      (activeCarrier A C e.toFunctionEmbedding) R f j p)
      (sharedOldACarrierCoreEmbedding A C.toRelStructure
        (activeCarrier A C e.toFunctionEmbedding) R f j q))
variable (μ : Fin (m + 1))

local notation "S" => activeCarrier A C e.toFunctionEmbedding
local notation "OldEdge" => OldACarrierEdge A C.toRelStructure
local notation "ActualEdge" =>
  OldACarrierEdge A (RelStructure.Attachment.attach C.toRelStructure S R f)
local notation "Std" => RelStructure.Attachment.copyEmbedding C.toRelStructure S R f
local notation "StdEdge" => fun (i : I) (old : OldEdge) =>
  actualAPictureEdgeEquiv A hA C.toRelStructure S R f
    (physicalStandardEdge (sharedOldACarrierInclusion A C.toRelStructure S)
      (sharedOldACarrierCoreEmbedding A C.toRelStructure S R f) i old)
local notation "StdWagon" => generatedActualASupportTrain_standardWagonEmbedding
  A hA C.toRelStructure S R f T U hRel hShared μ
local notation "Old" => selectedPictureOrderOneData
  A B D C family selected T μ
local notation "Out" => attachedSelectedPictureOrderOneData
  A hA B D C family selected e R f T U hShared μ
local notation "LabelMap" => attachedSelectedPictureLabel
  A hA B D C family selected e R f

include hRel

/-- Actual output A-support edges do not create new pair edges
between two DIFFERENT vertices of an A-strong standard copy. -/
theorem attachedSelectedPicture_standard_pairEdge_back_of_aStrong
    (i : I)
    (hStdStrong : AStrong A
      (RelStructure.Attachment.attach C.toRelStructure S R f)
      (copyCarrier (Std i)))
    (x y : X) (hxy : x ≠ y)
    (hPair : (Out).PairEdge (Std i x) (Std i y)) :
    (Old).PairEdge x y := by
  obtain ⟨edge, hx, hy⟩ := hPair
  obtain ⟨b, hb⟩ := edge.2
  have hxB : Std i x ∈ copyCarrier b := by
    rw [← hb]
    exact hx
  have hyB : Std i y ∈ copyCarrier b := by
    rw [← hb]
    exact hy
  have hBig : ¬(copyCarrier b ∩ copyCarrier (Std i)).Subsingleton := by
    intro hSmall
    have hImages : Std i x = Std i y :=
      hSmall ⟨hxB, ⟨x, rfl⟩⟩ ⟨hyB, ⟨y, rfl⟩⟩
    exact hxy ((Std i).injective hImages)
  have hSub : edge.1 ⊆ copyCarrier (Std i) := by
    rw [hb]
    exact hStdStrong b hBig
  have hImage : edge.1 ⊆
      ((fun z : X => Std i z) '' (Set.univ : Set X)) := by
    intro z hz
    obtain ⟨old, heq⟩ := hSub hz
    exact ⟨old, Set.mem_univ old, heq⟩
  obtain ⟨old, _hOld, hCarrier⟩ :=
    oldACarrierEdge_pullback_of_subset_image
      A C.toRelStructure
      (RelStructure.Attachment.attach C.toRelStructure S R f)
      (Std i) Set.univ edge hImage
  have hxOld : x ∈ old.1 := by
    have him : Std i x ∈ ((fun z : X => Std i z) '' old.1) := by
      rw [hCarrier]
      exact hx
    obtain ⟨u, hu, hux⟩ := him
    have hEq : u = x := (Std i).injective hux
    simpa [hEq] using hu
  have hyOld : y ∈ old.1 := by
    have him : Std i y ∈ ((fun z : X => Std i z) '' old.1) := by
      rw [hCarrier]
      exact hy
    obtain ⟨u, hu, huy⟩ := him
    have hEq : u = y := (Std i).injective huy
    simpa [hEq] using hu
  exact ⟨old, hxOld, hyOld⟩

/-- The exact A-strongness hypotheses of the generic free-attachment
lemma discharge the pair-reflection assumption of long-piece lifting.
The gluing image's A-strongness in the core is NOT suppressed. -/
theorem attachedSelectedPicture_standard_longValid_lift_of_aStrong
    (hOldStrong : AStrong A C.toRelStructure S)
    (hCoreStrong : ∀ i : I, AStrong A R (copyCarrier (f i)))
    (i : I) {n : ℕ}
    (Z : (Old).BigCycle n) (K : (Out).BigCycle n)
    (hLabel : ∀ j : Fin n,
      LabelMap i (Z.label j) = K.label j)
    (hConnector : ∀ j : Fin n,
      Sum.map (Std i) (StdWagon i) (Z.connector j) = K.connector j)
    (k j : Fin n) (a b : OldEdge) (p : Quotient (T.wagonSetoid μ))
    (hLong : OrderOneData.BigCycle.LongValid (Old) Z k j a p b) :
    OrderOneData.BigCycle.LongValid
      (Out) K k j (StdEdge i a) (StdWagon i p) (StdEdge i b) := by
  have hStdStrong :
      AStrong A (RelStructure.Attachment.attach C.toRelStructure S R f)
        (copyCarrier (Std i)) :=
    attachment_copy_aStrong
      C.toRelStructure S R f hA hOldStrong hCoreStrong i
  exact attachedSelectedPicture_standard_longValid_lift
    A hA B D C family selected e R f T U hShared hRel μ
    i Z K hLabel hConnector
    (fun x y hxy hp =>
      attachedSelectedPicture_standard_pairEdge_back_of_aStrong
        A hA B D C family selected e R f T U hShared hRel μ
        i hStdStrong x y hxy hp)
    k j a b p hLong

end ActualStandardNoNewPair
end StructuralRamsey.Girth
