import Girth.TrainActualGirthFromLengthTwoSource
import Girth.TrainActualMinimalTwoCutResidualClosure
import Girth.TrainActualTwoCycleOriginalBVertexGlobalSupreme
import Girth.TrainOriginalSelectedMixedSourceClosure
import Girth.TrainActualTwoCycleCoreConnectors
import Girth.TrainTwoCycleOriginalDesignatedOfLinear
import Mathlib.Tactic

set_option autoImplicit false
set_option Elab.async false

/-!
# Path A: exact length-two non-wagon source transfer, with the remaining
lower witness two-wagon obstruction exposed as an explicit hypothesis

The original B-designated target is found from actual source linearity.
Minimal geometric-owner choice forces the *other* geometric owner to
differ from that original B label's standard. At two owner cuts both
original connectors are genuine core vertices/wagons. Vertex/vertex
uses old selected-copy local piece and physical map; mixed uses the
real old selected-copy lower-bridge transfer. The only remaining case
in this file is an explicit no-two-wagon hypothesis. That hypothesis
must later be discharged by the lower-witness order-two obstruction,
not by assuming output girth or re-identifying B labels with owners.

The final result reduces output FullSystemGirthGT to precisely that
original two-wagon prohibition. No appendix or paper markers.
-/

namespace StructuralRamsey.Girth
open StructuralRamsey.RelStructure

universe u v
section OriginalTwoCutNonWagon

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
local notation "CoreEdge" => OldACarrierEdge A R
local notation "OldEdge" => OldACarrierEdge A C.toRelStructure
local notation "Old" => selectedPictureOrderOneData
  A B D C family selected T μ
local notation "Wit" => sharedWitnessOrderOneData U μ
  (sharedOldACarrierCoreEmbedding A C.toRelStructure S R f)
  (Subtype.val : CoreEdge → Set Y)
local notation "CoreEmb" =>
  RelStructure.Attachment.coreEmbedding C.toRelStructure S R f
local notation "CoreWagon" => generatedActualASupportTrain_coreWagonEmbedding
  A hA C.toRelStructure S R f T U
  (fun ν j p q h => Iff.mp (hRel ν j p q) h) hShared μ
local notation "Out" => attachedSelectedPictureOrderOneData
  A hA B D C family selected e R f T U hShared μ
local notation "GeomAllowed" => selectedOutputGeometricOwnerAllowed
  A hA B D C family selected e R f T U hShared μ
local notation "Selected" =>
  {r : DesignatedCopy B D C family // r ∈ selected}

include hRel

/-- Exact original length-two source supremacy except for the
explicit all-wagon obstruction. All displayed connector equalities,
B-labels and owner words are those of the actual source BigCycle. -/
theorem attachedSelectedPicture_two_cycle_supreme_of_no_double_wagon
    {qcut : ℕ} (hqcut : 1 ≤ qcut)
    (hOld : (Old).SupremeCycleBound qcut)
    (hWitness : (Wit).FullSystemGirthGT qcut)
    (hOldStrong : AStrong A C.toRelStructure S)
    (hCoreStrong : ∀ j : I, AStrong A R (copyCarrier (f j)))
    (hLinear : (Out).LinearPretrain)
    (K : (Out).BigCycle 2) (hAccept : K.Acceptable)
    (hOrder : K.twiceOrder ≤ 2 * qcut)
    (owner : Fin 2 → I ⊕ CoreEdge)
    (hAllowed : ∀ k, GeomAllowed (K.label k) (owner k))
    (hMinimal : ∀ other : Fin 2 → I ⊕ CoreEdge,
      (∀ k, GeomAllowed (K.label k) (other k)) →
        cyclicOwnerChanges owner ≤ cyclicOwnerChanges other)
    (hTwo : cyclicOwnerChanges owner = 2)
    (hNoDoubleWagon : ∀ p q : Quotient (U.wagonSetoid μ),
      K.connector (0 : Fin 2) = Sum.inr (CoreWagon p) →
      K.connector (1 : Fin 2) = Sum.inr (CoreWagon q) → False) :
    K.HasSimultaneousSupreme := by
  obtain ⟨target, hTarget⟩ :=
    OrderOneData.BigCycle.two_has_designated_of_linear
      Out K hAccept hLinear
  cases hOriginal : K.label target with
  | inr a =>
      have bad : False := by
        simpa [OrderOneData.designated, hOriginal] using hTarget
      exact bad.elim
  | inl iq =>
      rcases iq with ⟨i, r⟩
      have hSelected : K.label target = Sum.inl (i, r) := hOriginal
      have hOther : (Sum.inl i : I ⊕ CoreEdge) ≠
          owner (cyclicSucc target) := by
        exact (attachedSelectedPicture_two_cycle_original_standard_diff_shadow
          A hA B D C family selected e R f T U hShared μ
          K owner hAllowed hMinimal hTwo target i r hSelected).symm
      rcases attachedSelectedPicture_two_cycle_core_connector_cases
        A hA B D C family selected e R f T U hShared hRel μ
        K owner hAllowed hTwo with hVertex | hMixed | hWagon
      · obtain ⟨x, y, hX, hY⟩ := hVertex
        have hTwice : K.twiceOrder = 4 := by
          simp [OrderOneData.BigCycle.twiceOrder, Fin.sum_univ_two,
            cyclicSucc, connectorKind, twiceOccurrenceWeight, hX, hY]
        have hq : 2 ≤ qcut := by omega
        exact attachedSelectedPicture_two_cycle_original_B_vertex_full_supreme
          A hA B D C family selected e R f T U hShared hRel μ
          hq hOld hWitness hOldStrong hCoreStrong hLinear
          K hAccept owner hAllowed hMinimal hTwo
          target i r hSelected x y hX hY
      · obtain ⟨x, p, hMixed⟩ := hMixed
        exact attachedSelectedPicture_two_cycle_mixed_full_supreme_of_distinct_shadow
          A hA B D C family selected e R f T U hShared hRel μ
          hqcut hOld hWitness K hAccept owner hAllowed hTwo
          target i r hSelected hOther x p hMixed
      · obtain ⟨p, q, hP, hQ⟩ := hWagon
        exact False.elim (hNoDoubleWagon p q hP hQ)

/-- The complete one-level system-girth preservation is now reduced
to the genuinely missing no-two-wagon case, without assuming an
arbitrary original-B-label local piece or fake owner equality. -/
theorem attachedSelectedPicture_fullSystemGirth_of_no_double_wagon
    [Finite UA]
    (qcut : ℕ) (hqcut : 1 ≤ qcut)
    (hLinear : (Out).LinearPretrain)
    (hStrong : ∀ r : RelStructure.Embedding B D, r ∈ family →
      AStrong A D (copyCarrier r))
    (hTwoCopies : ∀ r : Selected, ∃ a b : OldEdge,
      a ≠ b ∧ a.1 ⊆ copyCarrier r.1.embedding ∧
        b.1 ⊆ copyCarrier r.1.embedding)
    (hOldStrong : AStrong A C.toRelStructure S)
    (hCoreStrong : ∀ j : I, AStrong A R (copyCarrier (f j)))
    (hOldSupreme : (Old).SupremeCycleBound qcut)
    (hWitness : (Wit).FullSystemGirthGT qcut)
    (hNoDoubleWagon : ∀ (K : (Out).BigCycle 2),
      K.Acceptable → K.twiceOrder ≤ 2 * qcut →
      ∀ (owner : Fin 2 → I ⊕ CoreEdge),
      (∀ j, GeomAllowed (K.label j) (owner j)) →
      cyclicOwnerChanges owner = 2 →
      ∀ p q : Quotient (U.wagonSetoid μ),
        K.connector (0 : Fin 2) = Sum.inr (CoreWagon p) →
        K.connector (1 : Fin 2) = Sum.inr (CoreWagon q) → False) :
    (Out).FullSystemGirthGT qcut := by
  apply attachedSelectedPicture_fullSystemGirth_of_minimal_two_cut_cases
    A hA B D C family selected e R f T U hShared hRel μ
    qcut hqcut hLinear hStrong hTwoCopies
    hOldStrong hCoreStrong hOldSupreme hWitness
  intro n K hAccept owner hAllowed hMinimal hTwo hOrder
  by_cases hn : n = 2
  · subst n
    exact attachedSelectedPicture_two_cycle_supreme_of_no_double_wagon
      A hA B D C family selected e R f T U hShared hRel μ
      hqcut hOldSupreme hWitness hOldStrong hCoreStrong hLinear
      K hAccept hOrder owner hAllowed hMinimal hTwo
      (hNoDoubleWagon K hAccept hOrder owner hAllowed hTwo)
  · have hThree : 3 ≤ n := by
      have hMin := K.length_ge_two
      omega
    exact attachedSelectedPicture_two_cut_three_le_full_supreme
      A hA B D C family selected e R f T U hShared hRel μ
      hStrong hTwoCopies hOldStrong hCoreStrong
      K hAccept hLinear hThree hOrder
      owner hAllowed hTwo hWitness hOldSupreme

end OriginalTwoCutNonWagon
end StructuralRamsey.Girth
