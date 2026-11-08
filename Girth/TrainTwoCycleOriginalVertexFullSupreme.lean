import Girth.TrainOriginalSelectedBVertexProbe
import Girth.TrainOriginalSelectedCoreVertexPreimage
import Girth.TrainActualMinimalTwoCycleShadow
import Girth.TrainTwoCycleOriginalLocalToGlobal
import Girth.TrainActualStandardPhysicalMap
import Girth.TrainGeometricVertexCutTargetIncidence
import Girth.TrainActualCutConnectorLift
import Mathlib.Tactic

set_option autoImplicit false
set_option Elab.async false

/-!
# Path A: the REAL original length-two two-vertex source is globally supreme

The two geometric owner cuts at n=2 are both actual connector cuts.
Both vertex connectors are therefore physical core vertices. For a
literal ORIGINAL designated selected B-label (i,q), actual original
incidence provides true OLD selected-copy endpoints x0,y0 in the
standard i; they need NOT be endpoints of a one-standard source cycle.

The OTHER geometric owner is a different lower shadow by minimality,
even when the literal original B-label is NOT its own chosen geometric
owner. Genuine vertex-cut incidence ensures this other witness label
meets BOTH lower core endpoints. Thus witness FullSystemGirthGT gives
one real lower short/long, and true shared-edge/parent reflection and
OLD SupremeCycleBound give a local OLD short/long of the ORIGINAL q.

The true literal physical map from OLD standard i transfers this
SINGLE local piece into the ORIGINAL attached output B-label (i,q).
The checked length-two short/long all-length plan constructor then
gives an actual, globally legal HasSimultaneousSupreme of the ORIGINAL
source BigCycle. No pulling back its other original label.

Both the pair-edge and no-pair/common-wagon branches are covered,
without assuming attached-output FullSystemGirthGT, original B-label =
geometric owner, HJ power girth, or physical support pruning.
The non-appendix draft is otherwise untouched.
-/

namespace StructuralRamsey.Girth
open StructuralRamsey.RelStructure

universe v
private theorem pathA_two_vertex_each_cut
    {I CoreEdge : Type v}
    (owner : Fin 2 → I ⊕ CoreEdge)
    (hTwo : cyclicOwnerChanges owner = 2)
    (k : Fin 2) : owner k ≠ owner (cyclicSucc k) := by
  have hDifferent : owner (0 : Fin 2) ≠ owner (1 : Fin 2) := by
    intro hEq
    have hZero : cyclicOwnerChanges owner = 0 :=
      (cyclicOwnerChanges_eq_zero_iff owner).2 (by
        intro j
        fin_cases j
        · simpa [cyclicSucc] using hEq
        · simpa [cyclicSucc] using hEq.symm)
    omega
  fin_cases k
  · simpa [cyclicSucc] using hDifferent
  · simpa [cyclicSucc] using hDifferent.symm

universe u
section PathATwoVertexOriginal

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
variable (hShared : ∀ i : I, Nonempty
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
local notation "CoreEdge" => OldACarrierEdge A R
local notation "Selected" =>
  {q : DesignatedCopy B D C family // q ∈ selected}
local notation "Out" => attachedSelectedPictureOrderOneData
  A hA B D C family selected e R f T U hShared μ
local notation "Old" => selectedPictureOrderOneData
  A B D C family selected T μ
local notation "Emb" => sharedOldACarrierCoreEmbedding
  A C.toRelStructure S R f
local notation "Wit" => sharedWitnessOrderOneData U μ
  Emb (Subtype.val : CoreEdge → Set Y)
local notation "Std" => RelStructure.Attachment.copyEmbedding
  C.toRelStructure S R f
local notation "CoreEmb" => RelStructure.Attachment.coreEmbedding
  C.toRelStructure S R f
local notation "Vertex" => RelStructure.Attachment.Vertex S (W := Y) (I := I)
local notation "GeomAllowed" => selectedOutputGeometricOwnerAllowed
  A hA B D C family selected e R f T U hShared μ

include hRel

/-- All literal labels of a two-occurrence source touch both original
connectors; this is independent of its geometric owner assignment. -/
private theorem pathA_two_original_incident
    (K : (Out).BigCycle 2) (t k : Fin 2) :
    (Out).Incident (K.label t) (K.connector k) := by
  fin_cases t <;> fin_cases k
  · exact K.left_incident 0
  · simpa [cyclicSucc] using K.right_incident 1
  · simpa [cyclicSucc] using K.right_incident 0
  · exact K.left_incident 1

/-- With two original vertex connectors already represented in the
physical core, minimal two-cut geometry and literal original selected
provenance yield a complete ORIGINAL globally supreme output source.
This covers original physical pair edges and no-pair long replacements. -/
theorem attachedSelectedPicture_two_vertex_full_supreme_of_core_connectors
    {qcut : ℕ} (hq : 2 ≤ qcut)
    (hOld : (Old).SupremeCycleBound qcut)
    (hWitness : (Wit).FullSystemGirthGT qcut)
    (hLinear : (Out).LinearPretrain)
    (hOldStrong : AStrong A C.toRelStructure S)
    (hCoreStrong : ∀ j : I, AStrong A R (copyCarrier (f j)))
    (K : (Out).BigCycle 2) (hAccept : K.Acceptable)
    (owner : Fin 2 → I ⊕ CoreEdge)
    (hAllowed : ∀ k, GeomAllowed (K.label k) (owner k))
    (hTwo : cyclicOwnerChanges owner = 2)
    (hMinimal : ∀ other : Fin 2 → I ⊕ CoreEdge,
      (∀ k, GeomAllowed (K.label k) (other k)) →
        cyclicOwnerChanges owner ≤ cyclicOwnerChanges other)
    (target : Fin 2) (i : I) (q : Selected)
    (hOriginal : K.label target = Sum.inl (i,q))
    (x y : Y)
    (hX0 : K.connector 0 = Sum.inl (CoreEmb x))
    (hY1 : K.connector 1 = Sum.inl (CoreEmb y)) :
    K.HasSimultaneousSupreme := by
  have hCoreXY : x ≠ y := by
    intro hxy
    have hConn : K.connector (0 : Fin 2) = K.connector (1 : Fin 2) := by
      rw [hX0, hY1, hxy]
    exact (by decide : (0 : Fin 2) ≠ 1) (K.connector_injective hConn)
  have hOther :
      Sum.inl i ≠ owner (cyclicSucc target) :=
    attachedSelectedPicture_two_cycle_original_standard_diff_shadow
      A hA B D C family selected e R f T U hShared μ
      K owner hAllowed hMinimal hTwo target i q hOriginal
  have hVX :=
    attachedSelectedPicture_geometric_vertex_cut_target_incidence
      A hA B D C family selected e R f T U hShared μ
      K owner hAllowed 0 x hX0
      (pathA_two_vertex_each_cut owner hTwo 0)
  have hVY :=
    attachedSelectedPicture_geometric_vertex_cut_target_incidence
      A hA B D C family selected e R f T U hShared μ
      K owner hAllowed 1 y hY1
      (pathA_two_vertex_each_cut owner hTwo 1)
  have hAx : x ∈ (Wit).carrier (owner (cyclicSucc target)) := by
    fin_cases target
    · simpa [cyclicSucc, OrderOneData.Incident] using hVX.2
    · simpa [cyclicSucc, OrderOneData.Incident] using hVX.1
  have hAy : y ∈ (Wit).carrier (owner (cyclicSucc target)) := by
    fin_cases target
    · simpa [cyclicSucc, OrderOneData.Incident] using hVY.1
    · simpa [cyclicSucc, OrderOneData.Incident] using hVY.2
  have hXCopy : CoreEmb x ∈ (Out).carrier (Sum.inl (i,q)) := by
    have h := pathA_two_original_incident
      A hA B D C family selected e R f T U hShared hRel μ K target 0
    rw [hOriginal, hX0] at h
    exact h
  have hYCopy : CoreEmb y ∈ (Out).carrier (Sum.inl (i,q)) := by
    have h := pathA_two_original_incident
      A hA B D C family selected e R f T U hShared hRel μ K target 1
    rw [hOriginal, hY1] at h
    exact h
  obtain ⟨x0, hQx, hStdX, hIx⟩ :=
    attachedSelectedPicture_original_B_core_vertex_old_preimage
      A hA B D C family selected e R f T U hShared μ i q x hXCopy
  obtain ⟨y0, hQy, hStdY, hIy⟩ :=
    attachedSelectedPicture_original_B_core_vertex_old_preimage
      A hA B D C family selected e R f T U hShared μ i q y hYCopy
  have hOldXY : x0 ≠ y0 := by
    intro hEq
    have hCoreEq : CoreEmb x = CoreEmb y := by
      calc
        CoreEmb x = Std i x0 := hStdX.symm
        _ = Std i y0 := by rw [hEq]
        _ = CoreEmb y := hStdY
    exact hCoreXY (CoreEmb.injective hCoreEq)
  have hOldPiece :=
    original_selected_B_vertex_local_of_lower_shadow
      A B D C family selected e R f T U hRel μ
      hq hOld hWitness q i (owner (cyclicSucc target)) hOther
      x0 y0 x y hOldXY hCoreXY hQx hQy
      hStdX hStdY hIx hIy hAx hAy
  let M := attachedSelectedPicture_standard_physicalMap
    A hA B D C family selected e R f T U hShared hRel μ
    hOldStrong hCoreStrong i
  have hMapped := M.localPiece_map
    (Sum.inl q) (Sum.inl x0) (Sum.inl y0) hOldPiece
  have hMapLabel :
      M.mapLabel (Sum.inl q) = Sum.inl (i,q) := rfl
  have hMapX :
      M.mapConnector (Sum.inl x0) = Sum.inl (CoreEmb x) := by
    change Sum.inl (Std i x0) = Sum.inl (CoreEmb x)
    rw [hStdX]
  have hMapY :
      M.mapConnector (Sum.inl y0) = Sum.inl (CoreEmb y) := by
    change Sum.inl (Std i y0) = Sum.inl (CoreEmb y)
    rw [hStdY]
  have hOutputPiece :
      (Out).ShortPiece (Sum.inl (i,q))
          (Sum.inl (CoreEmb x)) (Sum.inl (CoreEmb y)) ∨
      (Out).LongPiece (Sum.inl (i,q))
          (Sum.inl (CoreEmb x)) (Sum.inl (CoreEmb y)) := by
    simpa only [hMapLabel, hMapX, hMapY] using hMapped
  have hTarget : (Out).designated (K.label target) := by
    rw [hOriginal]
    trivial
  have hPred :
      trainCyclicPred (cyclicSucc target) = target :=
    trainCyclicPred_cyclicSucc_of_two_le
      (by decide : 2 ≤ 2) target
  have hPiece :
      (Out).ShortPiece (K.label target)
        (K.connector (trainCyclicPred (cyclicSucc target)))
        (K.connector (cyclicSucc target)) ∨
      (Out).LongPiece (K.label target)
        (K.connector (trainCyclicPred (cyclicSucc target)))
        (K.connector (cyclicSucc target)) := by
    rw [hPred, hOriginal]
    fin_cases target
    · simpa [cyclicSucc, hX0, hY1] using hOutputPiece
    · have hReverse :=
        (Out).piece_vertices_reverse
          (Sum.inl (i,q)) (CoreEmb x) (CoreEmb y) hOutputPiece
      simpa [cyclicSucc, hX0, hY1] using hReverse
  have hSupreme :=
    OrderOneData.BigCycle.two_hasSupremeAt_of_original_local_piece
      (Out) K hAccept hLinear target hTarget hPiece
  exact OrderOneData.BigCycle.hasSimultaneousSupreme_of_hasSupremeAt
    (Out) K target hSupreme

/-- The exact original source two-vertex case has no independent
"all connectors are core" assumption: both actual owner cuts force
core representations, even if the original labelled source uses
unrelated physical standard-provenance tags. -/
theorem attachedSelectedPicture_two_vertex_full_supreme
    {qcut : ℕ} (hq : 2 ≤ qcut)
    (hOld : (Old).SupremeCycleBound qcut)
    (hWitness : (Wit).FullSystemGirthGT qcut)
    (hLinear : (Out).LinearPretrain)
    (hOldStrong : AStrong A C.toRelStructure S)
    (hCoreStrong : ∀ j : I, AStrong A R (copyCarrier (f j)))
    (K : (Out).BigCycle 2) (hAccept : K.Acceptable)
    (owner : Fin 2 → I ⊕ CoreEdge)
    (hAllowed : ∀ k, GeomAllowed (K.label k) (owner k))
    (hTwo : cyclicOwnerChanges owner = 2)
    (hMinimal : ∀ other : Fin 2 → I ⊕ CoreEdge,
      (∀ k, GeomAllowed (K.label k) (other k)) →
        cyclicOwnerChanges owner ≤ cyclicOwnerChanges other)
    (target : Fin 2) (i : I) (q : Selected)
    (hOriginal : K.label target = Sum.inl (i,q))
    (v w : Vertex)
    (hv : K.connector 0 = Sum.inl v)
    (hw : K.connector 1 = Sum.inl w) :
    K.HasSimultaneousSupreme := by
  obtain ⟨r, hr⟩ :=
    attachedSelectedPicture_geometric_cut_connector_lift
      A hA B D C family selected e R f T U hShared hRel μ
      K owner hAllowed 0
      (pathA_two_vertex_each_cut owner hTwo 0)
  obtain ⟨x, hx⟩ : ∃ x : Y, CoreEmb x = v := by
    cases r with
    | inl x =>
        refine ⟨x, ?_⟩
        rw [hv] at hr
        exact Sum.inl.inj hr
    | inr p =>
        rw [hv] at hr
        cases hr
  obtain ⟨s, hs⟩ :=
    attachedSelectedPicture_geometric_cut_connector_lift
      A hA B D C family selected e R f T U hShared hRel μ
      K owner hAllowed 1
      (pathA_two_vertex_each_cut owner hTwo 1)
  obtain ⟨y, hy⟩ : ∃ y : Y, CoreEmb y = w := by
    cases s with
    | inl y =>
        refine ⟨y, ?_⟩
        rw [hw] at hs
        exact Sum.inl.inj hs
    | inr p =>
        rw [hw] at hs
        cases hs
  apply attachedSelectedPicture_two_vertex_full_supreme_of_core_connectors
    A hA B D C family selected e R f T U hShared hRel μ
    hq hOld hWitness hLinear hOldStrong hCoreStrong
    K hAccept owner hAllowed hTwo hMinimal target i q hOriginal x y
  · simpa [hx] using hv
  · simpa [hy] using hw

end PathATwoVertexOriginal
end StructuralRamsey.Girth
