import Girth.TrainOriginalSelectedMixedShortTrace
import Girth.TrainGeometricVertexCutTargetIncidence
import Girth.TrainGeometricWagonCutTargetIncidence
import Girth.TrainMinimalCyclicOwners
import Mathlib.Tactic

set_option autoImplicit false
set_option Elab.async false

/-!
# Path A: the OTHER geometric shadow meets both mixed original connectors

At original source length TWO, exactly two genuine geometric owner
changes means BOTH connector positions are owner cuts. The existing
exact vertex-cut and wagon-cut incidence theorems therefore give BOTH
owners physical incidence in the true lower witness, regardless of
whether either shadow is a standard or a singleton core A-edge.

This module does not equate any ORIGINAL B-label with a chosen owner.
An independent original-label standard can then use the lower
two-label bridge theorem to obtain its own physical short.
Circulation only; no appendix or manuscript modifications.
-/

namespace StructuralRamsey.Girth

universe v
variable {Owner : Type v}

/-- In a genuine cyclic owner word on Fin 2, two owner changes mean
that EACH of its two successor positions really changes owner. -/
theorem cyclicOwner_two_cut_source_two_every_position
    (owner : Fin 2 → Owner)
    (hTwo : cyclicOwnerChanges owner = 2)
    (k : Fin 2) :
    owner k ≠ owner (cyclicSucc k) := by
  have hNe : owner (0 : Fin 2) ≠ owner (1 : Fin 2) := by
    intro hEq
    have hAll : ∀ j : Fin 2,
        owner j = owner (cyclicSucc j) := by
      intro j
      fin_cases j
      · simpa [cyclicSucc] using hEq
      · simpa [cyclicSucc] using hEq.symm
    have hZero := (cyclicOwnerChanges_eq_zero_iff owner).2 hAll
    omega
  fin_cases k
  · simpa [cyclicSucc] using hNe
  · simpa [cyclicSucc] using hNe.symm

/-- Any index of Fin 2 is either the chosen other index or the
successor of the other index. This is the two-position incidence
trick; no source label is reindexed or changed. -/
theorem fin_two_other_is_endpoint_or_successor
    (target pos : Fin 2) :
    cyclicSucc target = pos ∨
      cyclicSucc target = cyclicSucc pos := by
  fin_cases target <;> fin_cases pos <;>
    simp [cyclicSucc]

open StructuralRamsey.RelStructure
universe u
section OriginalMixedShadowGeometry

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
local notation "CoreEdge" => OldACarrierEdge A R
local notation "Selected" =>
  {q : DesignatedCopy B D C family // q ∈ selected}
local notation "Emb" => sharedOldACarrierCoreEmbedding
  A C.toRelStructure S R f
local notation "CoreEmb" => RelStructure.Attachment.coreEmbedding
  C.toRelStructure S R f
local notation "CoreWagon" => generatedActualASupportTrain_coreWagonEmbedding
  A hA C.toRelStructure S R f T U
  (fun ν j p q h => Iff.mp (hRel ν j p q) h) hShared μ
local notation "Out" => attachedSelectedPictureOrderOneData
  A hA B D C family selected e R f T U hShared μ
local notation "Wit" => sharedWitnessOrderOneData U μ
  Emb (Subtype.val : CoreEdge → Set Y)
local notation "GeomAllowed" => selectedOutputGeometricOwnerAllowed
  A hA B D C family selected e R f T U hShared μ

include hRel

/-- Both mixed original connectors give an actual lower Y-vertex
contact and actual lower wagon contact for the OTHER geometric owner,
even when that owner is a singleton core A-edge rather than a
designated standard. This uses the original two genuine owner cuts. -/
theorem attachedSelectedPicture_two_cycle_mixed_shadow_incident
    (K : (Out).BigCycle 2)
    (owner : Fin 2 → I ⊕ CoreEdge)
    (hAllowed : ∀ j, GeomAllowed (K.label j) (owner j))
    (hTwo : cyclicOwnerChanges owner = 2)
    (target : Fin 2) (x : Y) (p : Quotient (U.wagonSetoid μ))
    (hMixed :
      (K.connector 0 = Sum.inl (CoreEmb x) ∧
        K.connector 1 = Sum.inr (CoreWagon p)) ∨
      (K.connector 0 = Sum.inr (CoreWagon p) ∧
        K.connector 1 = Sum.inl (CoreEmb x))) :
    x ∈ (Wit).carrier (owner (cyclicSucc target)) ∧
      (Wit).Meets (owner (cyclicSucc target)) p := by
  have hVertex : ∃ pos : Fin 2,
      K.connector pos = Sum.inl (CoreEmb x) := by
    rcases hMixed with ⟨h0, _h1⟩ | ⟨_h0, h1⟩
    · exact ⟨0, h0⟩
    · exact ⟨1, h1⟩
  have hWagon : ∃ pos : Fin 2,
      K.connector pos = Sum.inr (CoreWagon p) := by
    rcases hMixed with ⟨_h0, h1⟩ | ⟨h0, _h1⟩
    · exact ⟨1, h1⟩
    · exact ⟨0, h0⟩
  obtain ⟨vpos, hV⟩ := hVertex
  obtain ⟨wpos, hW⟩ := hWagon
  have hVcut := cyclicOwner_two_cut_source_two_every_position
    owner hTwo vpos
  have hWcut := cyclicOwner_two_cut_source_two_every_position
    owner hTwo wpos
  have hVInc :=
    attachedSelectedPicture_geometric_vertex_cut_target_incidence
      A hA B D C family selected e R f T U hShared μ
      K owner hAllowed vpos x hV hVcut
  have hWInc :=
    attachedSelectedPicture_geometric_wagon_cut_target_incidence
      A hA B D C family selected e R f T U hShared hRel μ
      K owner hAllowed wpos p hW hWcut
  have hXOther :
      (Wit).Incident (owner (cyclicSucc target)) (Sum.inl x) := by
    rcases fin_two_other_is_endpoint_or_successor target vpos with
      hFirst | hSecond
    · rw [hFirst]
      exact hVInc.1
    · rw [hSecond]
      exact hVInc.2
  have hPOther :
      (Wit).Incident (owner (cyclicSucc target)) (Sum.inr p) := by
    rcases fin_two_other_is_endpoint_or_successor target wpos with
      hFirst | hSecond
    · rw [hFirst]
      exact hWInc.1
    · rw [hSecond]
      exact hWInc.2
  exact ⟨hXOther, hPOther⟩

end OriginalMixedShadowGeometry
end StructuralRamsey.Girth
