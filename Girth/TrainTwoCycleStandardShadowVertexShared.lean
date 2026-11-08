import Girth.TrainActualTwoStandardDesignatedBlock
import Girth.TrainSelectedCycleGeometricOwners
import Mathlib.Tactic

set_option autoImplicit false
set_option Elab.async false

/-!
# Path A: exact source-length-two incidence and standard-shadow core geometry

At source length two, each original label is incident with both original
connectors.  This is a literal BigCycle fact; no geometric relabelling.

For an original selected output label (i,q), suppose the OTHER original
label has a geometric standard owner j distinct from i. Each vertex
connector then belongs simultaneously to the actual standards i and j,
hence lies in the genuine attached core and in both lower shared witness
copies. This supplies EXACT membership premises for the lower physical
two-vertex probe; it does not identify the selected B-label with j.

The numerical cutoff lemma records that an n=2 same-kind connector
word has twiceOrder=4, so only the mixed kind can enter at q=1.
All statements are circulation-only and conditional on their physical
geometry. No manuscript or appendix changes.
-/

namespace StructuralRamsey.Girth.OrderOneData

universe v
variable {V E I P : Type v} (D : OrderOneData V E I P)

/-- Both original labels of an exact length-two BigCycle are incident
with both original connectors, in either cyclic orientation. -/
theorem BigCycle.two_all_labels_incident
    (K : D.BigCycle 2) (k at : Fin 2) :
    D.Incident (K.label k) (K.connector at) := by
  fin_cases k <;> fin_cases at
  · exact K.left_incident 0
  · simpa [cyclicSucc] using K.right_incident 1
  · simpa [cyclicSucc] using K.right_incident 0
  · exact K.left_incident 1

/-- Both-vertex or both-wagon original length-two cycles require
cutoff at least two. The q=1 case is necessarily mixed. -/
theorem BigCycle.two_same_kind_cutoff_ge_two
    (K : D.BigCycle 2) (q : ℕ)
    (hSame : connectorKind (K.connector (0 : Fin 2)) =
      connectorKind (K.connector (1 : Fin 2)))
    (hOrder : K.twiceOrder ≤ 2 * q) : 2 ≤ q := by
  have hFour : K.twiceOrder = 4 := by
    cases h0 : connectorKind (K.connector (0 : Fin 2)) <;>
      cases h1 : connectorKind (K.connector (1 : Fin 2)) <;>
      simp_all [BigCycle.twiceOrder, Fin.sum_univ_two,
        cyclicSucc, twiceOccurrenceWeight]
  omega

end StructuralRamsey.Girth.OrderOneData

namespace StructuralRamsey.Girth
open StructuralRamsey.RelStructure

universe u v
section TwoCycleStandardShadow

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
variable (μ : Fin (m + 1))

local notation "S" => activeCarrier A C e.toFunctionEmbedding
local notation "CoreEdge" => OldACarrierEdge A R
local notation "OldEdge" => OldACarrierEdge A C.toRelStructure
local notation "Selected" =>
  {q : DesignatedCopy B D C family // q ∈ selected}
local notation "ActualEdge" => OldACarrierEdge A
  (RelStructure.Attachment.attach C.toRelStructure S R f)
local notation "Vertex" => RelStructure.Attachment.Vertex S (W := Y) (I := I)
local notation "Std" => RelStructure.Attachment.copyEmbedding
  C.toRelStructure S R f
local notation "CoreEmb" => RelStructure.Attachment.coreEmbedding
  C.toRelStructure S R f
local notation "Out" => attachedSelectedPictureOrderOneData
  A hA B D C family selected e R f T U hShared μ
local notation "Wit" => sharedWitnessOrderOneData U μ
  (sharedOldACarrierCoreEmbedding A C.toRelStructure S R f)
  (Subtype.val : CoreEdge → Set Y)
local notation "LabelMap" => attachedSelectedPictureLabel
  A hA B D C family selected e R f
local notation "GeomAllowed" => selectedOutputGeometricOwnerAllowed
  A hA B D C family selected e R f T U hShared μ

/-- A vertex connector of a literal original selected label (i,q),
whose other literal source label has distinct geometric standard owner j,
lies in the TRUE attachment core and BOTH lower shared witness copies.
No assignment of geometric owner i to the first occurrence is assumed. -/
theorem attachedSelectedPicture_two_cycle_standard_shadow_vertex_shared
    (K : (Out).BigCycle 2)
    (owner : Fin 2 → I ⊕ CoreEdge)
    (hAllowed : ∀ k, GeomAllowed (K.label k) (owner k))
    (target : Fin 2) (i : I) (q : Selected)
    (hOriginal : K.label target = Sum.inl (i,q))
    (j : I)
    (hShadow : owner (cyclicSucc target) = Sum.inl j)
    (hDistinct : i ≠ j)
    (at : Fin 2) (x : Vertex)
    (hVertex : K.connector at = Sum.inl x) :
    x ∈ copyCarrier CoreEmb ∧
    x ∈ (Wit).copyCarrier i ∧
    x ∈ (Wit).copyCarrier j := by
  have hOriginalAllowed :
      GeomAllowed (K.label target) (Sum.inl i) := by
    rw [hOriginal]
    apply selectedOutput_literal_owner_geometric
      A hA B D C family selected e R f T U hShared μ
      (Sum.inl (i,q)) (Sum.inl i)
    change ∃ old : Selected ⊕ OldEdge,
      (Sum.inl (i,q) : (I × Selected) ⊕ ActualEdge) =
        LabelMap i old
    exact ⟨Sum.inl q, rfl⟩
  have hStdI : x ∈ copyCarrier (Std i) := by
    change (Out).carrier (K.label target) ⊆ copyCarrier (Std i)
      at hOriginalAllowed
    have hInc := OrderOneData.BigCycle.two_all_labels_incident
      (Out) K target at
    rw [hVertex] at hInc
    change x ∈ (Out).carrier (K.label target) at hInc
    exact hOriginalAllowed hInc
  have hStdJ : x ∈ copyCarrier (Std j) := by
    have hOtherAllowed := hAllowed (cyclicSucc target)
    rw [hShadow] at hOtherAllowed
    change (Out).carrier (K.label (cyclicSucc target)) ⊆
      copyCarrier (Std j) at hOtherAllowed
    have hInc := OrderOneData.BigCycle.two_all_labels_incident
      (Out) K (cyclicSucc target) at
    rw [hVertex] at hInc
    change x ∈ (Out).carrier (K.label (cyclicSucc target)) at hInc
    exact hOtherAllowed hInc
  have hCore : x ∈ copyCarrier CoreEmb :=
    attachment_copy_copy_intersection_subset_core
      C.toRelStructure S R f hDistinct ⟨hStdI, hStdJ⟩
  refine ⟨hCore, ?_, ?_⟩
  · exact activeAttached_mem_sharedWitness_of_standard_core
      A C e.toFunctionEmbedding R f U μ i x hStdI hCore
  · exact activeAttached_mem_sharedWitness_of_standard_core
      A C e.toFunctionEmbedding R f U μ j x hStdJ hCore

end TwoCycleStandardShadow
end StructuralRamsey.Girth
