import Girth.TrainOriginalSelectedMixedSourceClosure
import Girth.TrainActualTwoCycleDesignatedOwnerForced
import Mathlib.Tactic

set_option autoImplicit false
set_option Elab.async false

/-!
# Original mixed two-cycle: remove the independent owner-minimality premise

A source with exactly two original occurrences and exactly two
geometric owner changes has distinct owners at the two positions.
Under the circulation's genuine selected-base A-strongness and
two-physical-A-support-edge hypothesis, the designated B-copy is
geometrically owned by its literal standard i, without minimizing
the owner assignment.

Therefore the different owner of the other occurrence supplies
the actual lower witness shadow required by the physical mixed
vertex/wagon transfer. The previously checked source-level
construction then yields an ORIGINAL globally legal supreme plan.

This lemma is conditional on the genuine lower FullSystemGirthGT
and old SupremeCycleBound; it does not construct a recursive witness,
assume any output girth, or equate B-labels with their owners.
No appendix and no manuscript validation marker promotion.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure
universe u v

section OriginalMixedNonminimal

variable {L : RelLanguage.{u}} {UA VB P X Y I : Type v}
variable (A : RelStructure L UA) (hA : A.Irreducible)
variable (B : RelStructure L VB) (D : RelStructure L P)
variable (C : StructuralRamsey.Partite.System L P X)
variable (family : Set (Embedding B D))
variable (selected : Set (DesignatedCopy B D C family))
variable (e : Embedding A D) (R : RelStructure L Y)
variable (f : I → Embedding
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

local notation "Selected" =>
  {q : DesignatedCopy B D C family // q ∈ selected}
local notation "OldEdge" => OldACarrierEdge A C.toRelStructure
local notation "CoreEdge" => OldACarrierEdge A R
local notation "CoreEmb" => RelStructure.Attachment.coreEmbedding
  C.toRelStructure (activeCarrier A C e.toFunctionEmbedding) R f
local notation "CoreWagon" => generatedActualASupportTrain_coreWagonEmbedding
  A hA C.toRelStructure
  (activeCarrier A C e.toFunctionEmbedding) R f T U
  (fun ν j p q h => (hRel ν j p q).mp h) hShared μ
local notation "Out" => attachedSelectedPictureOrderOneData
  A hA B D C family selected e R f T U hShared μ
local notation "Old" => selectedPictureOrderOneData
  A B D C family selected T μ
local notation "Wit" => sharedWitnessOrderOneData U μ
  (sharedOldACarrierCoreEmbedding A C.toRelStructure
    (activeCarrier A C e.toFunctionEmbedding) R f)
  (Subtype.val : CoreEdge → Set Y)
local notation "GeomAllowed" => selectedOutputGeometricOwnerAllowed
  A hA B D C family selected e R f T U hShared μ

include hRel

/-- Complete ORIGINAL length-two mixed source supremacy from
actual two-owner-cut geometry, without any minimal-owner assumption.
The two-edge hypothesis is about the exact old B-copy carriers,
not about reduced geometric witness standards. -/
theorem attachedSelectedPicture_two_cycle_mixed_full_supreme_of_two_edge_base
    [Finite UA]
    (hBaseStrong : ∀ q : Selected,
      AStrong A D (copyCarrier q.1.base))
    (hTwoEdges : ∀ q : Selected, ∃ r s : OldEdge,
      r ≠ s ∧ r.1 ⊆ copyCarrier q.1.embedding ∧
        s.1 ⊆ copyCarrier q.1.embedding)
    {qcut : ℕ} (hq : 1 ≤ qcut)
    (hOld : (Old).SupremeCycleBound qcut)
    (hWitness : (Wit).FullSystemGirthGT qcut)
    (K : (Out).BigCycle 2) (hAccept : K.Acceptable)
    (owner : Fin 2 → I ⊕ CoreEdge)
    (hAllowed : ∀ j, GeomAllowed (K.label j) (owner j))
    (hTwo : cyclicOwnerChanges owner = 2)
    (target : Fin 2) (i : I) (q : Selected)
    (hOriginal : K.label target = Sum.inl (i, q))
    (x : Y) (p : Quotient (U.wagonSetoid μ))
    (hMixed :
      (K.connector 0 = Sum.inl (CoreEmb x) ∧
        K.connector 1 = Sum.inr (CoreWagon p)) ∨
      (K.connector 0 = Sum.inr (CoreWagon p) ∧
        K.connector 1 = Sum.inl (CoreEmb x))) :
    K.HasSimultaneousSupreme := by
  have hDistinct : (Sum.inl i : I ⊕ CoreEdge) ≠
      owner (cyclicSucc target) :=
    attachedSelectedPicture_two_cycle_original_standard_diff_other_of_two_edges
      A hA B D C family selected e R f T U hShared μ
      hBaseStrong hTwoEdges K owner hAllowed hTwo
      target i q hOriginal
  exact attachedSelectedPicture_two_cycle_mixed_full_supreme_of_distinct_shadow
    A hA B D C family selected e R f T U hShared hRel μ
    hq hOld hWitness K hAccept owner hAllowed hTwo
    target i q hOriginal hDistinct x p hMixed

end OriginalMixedNonminimal
end StructuralRamsey.Girth
