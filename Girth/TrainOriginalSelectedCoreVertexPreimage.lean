import Girth.TrainActualTwoStandardDesignatedBlock
import Girth.TrainActiveGluingWitness
import Girth.TrainSelectedCycleGeometricOwners
import Mathlib.Tactic

set_option autoImplicit false
set_option Elab.async false

/-!
# Path A: actual original designated B-copy core vertex has its
TRUE old standard preimage and witness copy incidence

The original selected label is literally (i,q), with q in the
prescribed selected family. If one of its output source connectors
is a genuine core vertex CoreEmb x, selected-copy carrier membership
gives a REAL old vertex x0 in q with Std_i x0 = CoreEmb x.
The already checked active-attachment core/standard intersection
lemma then forces x into the lower shared witness gluing copy i.

Unlike a geometric owner identification, this refers to the
ORIGINAL B-label's standard index i. Applying it to both actual
source connectors gives the exact old preimage pair required
by the source-length-two selected-copy probe. No assumption that
the other original source label is contained in this standard.
No appendix or manuscript change.
-/

namespace StructuralRamsey.Girth
open StructuralRamsey.RelStructure

universe u v

section OriginalSelectedCoreVertex

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
variable (μ : Fin (m + 1))

local notation "S" => activeCarrier A C e.toFunctionEmbedding
local notation "Selected" =>
  {q : DesignatedCopy B D C family // q ∈ selected}
local notation "CoreEdge" => OldACarrierEdge A R
local notation "Std" => RelStructure.Attachment.copyEmbedding
  C.toRelStructure S R f
local notation "CoreEmb" => RelStructure.Attachment.coreEmbedding
  C.toRelStructure S R f
local notation "Out" => attachedSelectedPictureOrderOneData
  A hA B D C family selected e R f T U hShared μ
local notation "Wit" => sharedWitnessOrderOneData U μ
  (sharedOldACarrierCoreEmbedding A C.toRelStructure S R f)
  (Subtype.val : CoreEdge → Set Y)

/-- Every TRUE core vertex in the carrier of the original
selected B-label (i,q) comes from an exact old vertex of q
and belongs to the prescribed LOWER gluing copy i. -/
theorem attachedSelectedPicture_original_B_core_vertex_old_preimage
    (i : I) (q : Selected) (x : Y)
    (hx : CoreEmb x ∈ (Out).carrier (Sum.inl (i,q))) :
    ∃ x0 : X,
      x0 ∈ copyCarrier q.1.embedding ∧
      Std i x0 = CoreEmb x ∧
      x ∈ (Wit).copyCarrier i := by
  change CoreEmb x ∈
    ((fun z : X => Std i z) '' copyCarrier q.1.embedding) at hx
  obtain ⟨x0, hxOld, hEq⟩ := hx
  refine ⟨x0, hxOld, hEq, ?_⟩
  have hStd : CoreEmb x ∈ copyCarrier (Std i) :=
    ⟨x0, hEq⟩
  have hCore : CoreEmb x ∈ copyCarrier CoreEmb :=
    ⟨x, rfl⟩
  have hIntersect :
      CoreEmb x ∈ copyCarrier ((CoreEmb).comp (f i)) := by
    rw [← attachment_copy_core_intersection
      C.toRelStructure S R f i]
    exact ⟨hStd, hCore⟩
  obtain ⟨z, hz⟩ := hIntersect
  have hCoreLocal : x ∈ copyCarrier (f i) := by
    refine ⟨z, ?_⟩
    apply CoreEmb.injective
    exact hz
  rw [activeCoreWitness_copyCarrier_eq
    A C e.toFunctionEmbedding R f U μ i]
  exact hCoreLocal

end OriginalSelectedCoreVertex
end StructuralRamsey.Girth
