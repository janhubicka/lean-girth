import Girth.TrainSelectedPictureOutputIncidence
import Girth.TrainCoreWagonEmbedding
import Girth.TrainActualStandardCoreIncidence
import Girth.TrainGeneratedActualAllLevelRestriction
import Girth.TrainSimultaneousSupreme
import Girth.TrainShortOnlyPlanGlobal
import Mathlib.Tactic

set_option autoImplicit false
set_option Elab.async false

/-!
# Path A: an original selected B-copy inherits a genuine mixed short

This is a physical source-local transfer for the unresolved length-two
vertex/wagon case. The original label is literally (i,q), NOT a chosen
geometric owner. The actual output B-label meets a true core wagon, and
the original selected old copy contains the old preimage of a core vertex.
A real lower shared-witness bridge through that vertex and wagon yields
one shared OLD A-edge in the right wagon. Exact restriction of the
generated physical train reflects its wagon class to the old standard,
where old SupremeCycleBound (at cutoff >=1) probes against the selected
B-copy's own wagon incidence. This obtains a bridge INSIDE the original
old selected B-copy, and transports that exact edge back to a genuine
output ShortPiece of the ORIGINAL B-label.

No whole-cycle pullback, no source-label/geometric-owner identification,
no strength of the Hales--Jewett power, no support pruning, and no
appendix or manuscript change. This lemma does not assert that a lower
bridge exists; obtaining it from the actual two-cut geometry is separate.
-/

namespace StructuralRamsey.Girth
open StructuralRamsey.RelStructure
universe u v

section OriginalSelectedMixedBridge

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
variable (hShared : ∀ _i : I, Nonempty
  (SharedOldACarrierEdge A C.toRelStructure
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
local notation "CoreEdge" => OldACarrierEdge A R
local notation "Shared" => SharedOldACarrierEdge A C.toRelStructure S
local notation "Selected" =>
  {q : DesignatedCopy B D C family // q ∈ selected}
local notation "InOld" => sharedOldACarrierInclusion A C.toRelStructure S
local notation "Emb" => sharedOldACarrierCoreEmbedding
  A C.toRelStructure S R f
local notation "Std" => RelStructure.Attachment.copyEmbedding
  C.toRelStructure S R f
local notation "CoreEmb" => RelStructure.Attachment.coreEmbedding
  C.toRelStructure S R f
local notation "Eqv" => actualAPictureEdgeEquiv
  A hA C.toRelStructure S R f
local notation "StdEdge" => (fun (i : I) (a : OldEdge) =>
  Eqv (physicalStandardEdge InOld Emb i a))
local notation "CoreActual" => (fun (b : CoreEdge) =>
  Eqv (physicalCoreEdge InOld I b))
local notation "Train" => generatedActualASupportTrain
  A hA C.toRelStructure S R f T U hShared
local notation "CoreWagon" => generatedActualASupportTrain_coreWagonEmbedding
  A hA C.toRelStructure S R f T U
  (fun ν j p q h => Iff.mp (hRel ν j p q) h) hShared μ
local notation "Old" => selectedPictureOrderOneData
  A B D C family selected T μ
local notation "Out" => attachedSelectedPictureOrderOneData
  A hA B D C family selected e R f T U hShared μ
local notation "Wit" => sharedWitnessOrderOneData U μ
  Emb (Subtype.val : CoreEdge → Set Y)

include hRel

/-- A genuine core vertex belonging to the ORIGINAL output
designated B-label has a genuine old selected-copy preimage, and that
same core vertex belongs to its literal standard's lower Y-witness.
This performs the explicit CoreEmb pullback that an attached-vertex
witness membership by itself does not supply. -/
theorem attachedSelectedPicture_original_B_core_vertex_preimage_Y
    (i : I) (q : Selected) (x : Y)
    (hX : CoreEmb x ∈ (Out).copyCarrier (i,q)) :
    ∃ x0 : X,
      x0 ∈ copyCarrier q.1.embedding ∧
      Std i x0 = CoreEmb x ∧
      x ∈ (Wit).copyCarrier i := by
  change CoreEmb x ∈
    ((fun z : X => Std i z) '' copyCarrier q.1.embedding) at hX
  obtain ⟨x0, hx0, hEq⟩ := hX
  have hStd : CoreEmb x ∈ copyCarrier (Std i) :=
    ⟨x0, hEq⟩
  have hCore : CoreEmb x ∈ copyCarrier CoreEmb := ⟨x, rfl⟩
  obtain ⟨s, _edge, hs, _hz, _hEq⟩ :=
    activeAttached_coreStandard_pointwise_sharedAEdge
      A C e.toFunctionEmbedding R f i (CoreEmb x) hStd hCore
  have hImage :
      CoreEmb x ∈ attachedCoreAEdgeCarrier
        A C.toRelStructure S R f (Emb i s) := by
    rw [← attachedSharedAEdgeCarrier_eq
      A C.toRelStructure S R f i s]
    exact hs
  change CoreEmb x ∈
    (fun z : Y => CoreEmb z) '' (Emb i s).1 at hImage
  obtain ⟨y, hy, hY⟩ := hImage
  have hyx : y = x := (RelStructure.Attachment.coreEmbedding C.toRelStructure S R f).injective hY
  refine ⟨x0, hx0, hEq, s, ?_⟩
  simpa [hyx] using hy

/-- An actual designated B-copy's true output incidence with a CORE
wagon forces the ORIGINAL standard i to meet that same wagon in the
real lower Y-vertex witness. The result does not need a geometric
owner identity or any girth hypothesis. -/
theorem attachedSelectedPicture_original_B_core_wagon_lower_meets
    (i : I) (q : Selected)
    (p : Quotient (U.wagonSetoid μ))
    (hMeets : (Out).Meets (Sum.inl (i,q)) (CoreWagon p)) :
    (Wit).Meets (Sum.inl i) p := by
  obtain ⟨b, rfl⟩ := Quotient.exists_rep p
  have hOriginal :
      (Out).Meets (attachedSelectedPictureLabel
        A hA B D C family selected e R f i (Sum.inl q))
        (CoreWagon (Quotient.mk (U.wagonSetoid μ) b)) :=
    hMeets
  obtain ⟨old, _hOldInQ, hOldParent⟩ :=
    (attachedSelectedPicture_meets_iff
      A hA B D C family selected e R f T U hShared μ
      i (Sum.inl q) (CoreWagon (Quotient.mk (U.wagonSetoid μ) b))).mp
      hOriginal
  have hCoreParent :
      (Out).parent (CoreActual b) =
        CoreWagon (Quotient.mk (U.wagonSetoid μ) b) := by
    change Quotient.mk ((Train).wagonSetoid μ) (CoreActual b) =
      CoreWagon (Quotient.mk (U.wagonSetoid μ) b)
    exact (generatedActualASupportTrain_coreWagonEmbedding_mk
      A hA C.toRelStructure S R f T U
      (fun ν j v w h => (hRel ν j v w).mp h)
      hShared μ b).symm
  have hSame : (Train).rel μ (StdEdge i old) (CoreActual b) :=
    Quotient.exact (hOldParent.trans hCoreParent.symm)
  obtain ⟨s, _hOldRel, hCoreRel, _hLocal⟩ :=
    generatedActualASupportTrain_standard_core_copy_local_incidence
      A hA C.toRelStructure S R f T U hShared hRel μ i old b hSame
  exact ⟨Emb i s, ⟨s, rfl⟩, Quotient.sound hCoreRel⟩

/-- A true mixed lower bridge at the ORIGINAL selected copy's standard
gives an ACTUAL output short owned by that same original selected B-label.
The ambient wagon is preserved, with no inserted wagon or relabelling. -/
theorem attachedSelectedPicture_original_mixed_short_of_lower_bridge
    {qcut : ℕ} (hq : 1 ≤ qcut)
    (hOld : (Old).SupremeCycleBound qcut)
    (i : I) (q : Selected) (x0 : X) (x : Y)
    (hQx : x0 ∈ copyCarrier q.1.embedding)
    (hX : Std i x0 = CoreEmb x)
    (p : Quotient (U.wagonSetoid μ))
    (hMeets : (Out).Meets (Sum.inl (i,q)) (CoreWagon p))
    (hWitness : (Wit).Bridge (Sum.inl i) x p) :
    (Out).ShortPiece (Sum.inl (i,q))
      (Sum.inl (CoreEmb x)) (Sum.inr (CoreWagon p)) := by
  have hMeetsOriginal :
      (Out).Meets (attachedSelectedPictureLabel
        A hA B D C family selected e R f i (Sum.inl q)) (CoreWagon p) :=
    hMeets
  obtain ⟨t, htOwned, htParent⟩ :=
    (attachedSelectedPicture_meets_iff
      A hA B D C family selected e R f T U hShared μ
      i (Sum.inl q) (CoreWagon p)).mp hMeetsOriginal
  obtain ⟨b, hbOwned, hbParent, hbX⟩ := hWitness
  change b ∈ Set.range (Emb i) at hbOwned
  obtain ⟨s, hs⟩ := hbOwned
  subst b
  have hOldVertex : x0 ∈ (InOld s).1 := by
    have hxImage : Std i x0 ∈
        (fun z : X => Std i z) '' s.1.1 := by
      rw [sharedOldACarrierCoreMap_image
        A C.toRelStructure S R f i s]
      exact ⟨x, hbX, hX.symm⟩
    obtain ⟨z, hz, hzEq⟩ := hxImage
    have hzx : z = x0 := (Std i).injective hzEq
    exact hzx ▸ hz
  have hSamePhysical : StdEdge i (InOld s) = CoreActual (Emb i s) := by
    change Eqv (physicalStandardEdge InOld Emb i (InOld s)) =
      Eqv (physicalCoreEdge InOld I (Emb i s))
    rw [physicalStandardEdge_shared]
    rfl
  have hsOutParent :
      (Out).parent (StdEdge i (InOld s)) = CoreWagon p := by
    rw [hSamePhysical]
    change Quotient.mk ((Train).wagonSetoid μ)
      (CoreActual (Emb i s)) = CoreWagon p
    calc
      Quotient.mk ((Train).wagonSetoid μ) (CoreActual (Emb i s)) =
          CoreWagon (Quotient.mk (U.wagonSetoid μ) (Emb i s)) :=
        (generatedActualASupportTrain_coreWagonEmbedding_mk
          A hA C.toRelStructure S R f T U
          (fun ν j v w h => (hRel ν j v w).mp h)
          hShared μ (Emb i s)).symm
      _ = CoreWagon p := congrArg CoreWagon hbParent
  have hOldRel : T.rel μ (InOld s) t := by
    apply (generatedActualASupportTrain_restrict_standard
      A hA C.toRelStructure S R f T U hRel hShared μ i (InOld s) t).mp
    exact Quotient.exact (hsOutParent.trans htParent.symm)
  have hOldParent : (Old).parent (InOld s) = (Old).parent t :=
    Quotient.sound hOldRel
  have hOneLocal : (Old).LocalPieceSystemBound 1 := by
    intro n Z hAcc hBudget
    exact (Old).localPieceSystemBound_of_supremeCycleBound
      qcut hOld n Z hAcc (by omega)
  have hBound : (Old).Bound :=
    (Old).bound_of_localPieceSystemBound hOneLocal
  have hCopyVertex : x0 ∈ (Old).copyCarrier q := hQx
  have hOldMeets : (Old).Meets (Sum.inl q) ((Old).parent t) :=
    ⟨t, htOwned, rfl⟩
  have hOriginalBridge : (Old).Bridge (Sum.inl q) x0 ((Old).parent t) :=
    (Old).bridge_of_incident_edge hBound (Sum.inl q)
      x0 ((Old).parent t) hCopyVertex hOldMeets
      (InOld s) hOldParent hOldVertex
  obtain ⟨bOld, hbOldOwned, hbOldParent, hbOldX⟩ := hOriginalBridge
  have hbOutOwned : StdEdge i bOld ∈
      (Out).edges (Sum.inl (i,q)) :=
    (attachedSelectedPicture_edges
      A hA B D C family selected e R f T U hShared μ
      i (Sum.inl q) (StdEdge i bOld)).mpr
      ⟨bOld, hbOldOwned, rfl⟩
  have hbOutX : CoreEmb x ∈ (StdEdge i bOld).1 := by
    rw [actualAPictureEdgeEquiv_standard_carrier
      A hA C.toRelStructure S R f i bOld]
    exact ⟨x0, hbOldX, hX⟩
  have hbOutRel :
      (Train).rel μ (StdEdge i bOld) (StdEdge i t) := by
    apply (generatedActualASupportTrain_restrict_standard
      A hA C.toRelStructure S R f T U hRel hShared μ i bOld t).mpr
    exact Quotient.exact hbOldParent
  have hbOutParent :
      (Out).parent (StdEdge i bOld) = CoreWagon p :=
    (Quotient.sound hbOutRel).trans htParent
  refine ⟨StdEdge i bOld, hbOutOwned, ?_, ?_⟩
  · change CoreEmb x ∈ (StdEdge i bOld).1
    exact hbOutX
  · change (Out).Meets (Sum.inr (StdEdge i bOld)) (CoreWagon p)
    exact ⟨StdEdge i bOld, rfl, hbOutParent⟩

/-- The old selected-copy mixed short can be obtained directly from
the REAL lower FullSystemGirthGT certificate and a second distinct
witness shadow label, once both lower vertex incidences are known.
The selected copy's lower wagon incidence is derived above from the
literal original output B-copy, never assumed from geometric ownership.
This is the intended composition point for the n=2 cut geometry. -/
theorem attachedSelectedPicture_original_mixed_short_of_shadow
    {qcut : ℕ} (hq : 1 ≤ qcut)
    (hOld : (Old).SupremeCycleBound qcut)
    (hWitness : (Wit).FullSystemGirthGT qcut)
    (i : I) (q : Selected) (x0 : X) (x : Y)
    (hQx : x0 ∈ copyCarrier q.1.embedding)
    (hX : Std i x0 = CoreEmb x)
    (hIx : x ∈ (Wit).copyCarrier i)
    (p : Quotient (U.wagonSetoid μ))
    (hMeets : (Out).Meets (Sum.inl (i,q)) (CoreWagon p))
    (a : I ⊕ CoreEdge)
    (hOther : Sum.inl i ≠ a)
    (hAx : x ∈ (Wit).carrier a)
    (hAp : (Wit).Meets a p) :
    (Out).ShortPiece (Sum.inl (i,q))
      (Sum.inl (CoreEmb x)) (Sum.inr (CoreWagon p)) := by
  have hLocal : (Wit).LocalPieceSystemBound 1 := by
    intro n Z hAccept hOrder
    exact (Wit).localPieceSystemBound_of_supremeCycleBound
      qcut hWitness.2 n Z hAccept (by omega)
  have hBound : (Wit).Bound :=
    (Wit).bound_of_localPieceSystemBound hLocal
  have hIp : (Wit).Meets (Sum.inl i) p :=
    attachedSelectedPicture_original_B_core_wagon_lower_meets
      A hA B D C family selected e R f T U hShared hRel μ
      i q p hMeets
  have hBridge : (Wit).Bridge (Sum.inl i) x p :=
    ((Wit).both_bridges hBound (Sum.inl i) a x p
      hOther hIx hAx hIp hAp).1
  exact attachedSelectedPicture_original_mixed_short_of_lower_bridge
    A hA B D C family selected e R f T U hShared hRel μ
    hq hOld i q x0 x hQx hX p hMeets hBridge

/-- In a TRUE original source length-two mixed cycle, the short
just constructed yields a complete globally valid simultaneous-supreme
replacement of the ORIGINAL designated label. All boundary indices and
both cyclic orientations are explicit; the other label is never pulled
back into the original standard or replaced by a geometric owner. -/
theorem attachedSelectedPicture_two_cycle_mixed_supreme_of_shadow
    {qcut : ℕ} (hq : 1 ≤ qcut)
    (hOld : (Old).SupremeCycleBound qcut)
    (hWitness : (Wit).FullSystemGirthGT qcut)
    (K : (Out).BigCycle 2) (hAccept : K.Acceptable)
    (target : Fin 2) (i : I) (q : Selected)
    (hOriginal : K.label target = Sum.inl (i,q))
    (x0 : X) (x : Y)
    (hQx : x0 ∈ copyCarrier q.1.embedding)
    (hX : Std i x0 = CoreEmb x)
    (hIx : x ∈ (Wit).copyCarrier i)
    (p : Quotient (U.wagonSetoid μ))
    (hMixed :
      (K.connector 0 = Sum.inl (CoreEmb x) ∧
        K.connector 1 = Sum.inr (CoreWagon p)) ∨
      (K.connector 0 = Sum.inr (CoreWagon p) ∧
        K.connector 1 = Sum.inl (CoreEmb x)))
    (hMeets : (Out).Meets (Sum.inl (i,q)) (CoreWagon p))
    (a : I ⊕ CoreEdge)
    (hOther : Sum.inl i ≠ a)
    (hAx : x ∈ (Wit).carrier a)
    (hAp : (Wit).Meets a p) :
    K.HasSimultaneousSupreme := by
  have hShort :=
    attachedSelectedPicture_original_mixed_short_of_shadow
      A hA B D C family selected e R f T U hShared hRel μ
      hq hOld hWitness i q x0 x hQx hX hIx p hMeets
      a hOther hAx hAp
  obtain ⟨edge, hOwned, hXEdge, hPEdge⟩ := hShort
  have hOwnTarget : edge ∈ (Out).edges (K.label target) := by
    rw [hOriginal]
    exact hOwned
  have hAllInc : ∀ j : Fin 2,
      (Out).Incident (Sum.inr edge) (K.connector j) := by
    intro j
    fin_cases j
    · rcases hMixed with ⟨h0, _h1⟩ | ⟨h0, _h1⟩
      · rw [h0]
        exact hXEdge
      · rw [h0]
        exact hPEdge
    · rcases hMixed with ⟨_h0, h1⟩ | ⟨_h0, h1⟩
      · rw [h1]
        exact hPEdge
      · rw [h1]
        exact hXEdge
  have hTarget : (Out).designated (K.label target) := by
    rw [hOriginal]
    trivial
  apply K.hasSimultaneousSupreme_of_all_shortValid
    (Out) hAccept target hTarget
  intro j _hNe
  exact ⟨edge, hOwnTarget, hAllInc (trainCyclicPred j), hAllInc j⟩

end OriginalSelectedMixedBridge
end StructuralRamsey.Girth
