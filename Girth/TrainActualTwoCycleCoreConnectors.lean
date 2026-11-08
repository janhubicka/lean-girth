import Girth.TrainActualCutIndexedBigCycle
import Girth.TrainCyclicCutIndexAtSourceTwo
import Mathlib.Tactic

set_option autoImplicit false
set_option Elab.async false

/-!
# Path A: every connector of an original source n=2 / two-cut cycle is physical core

At two geometric cuts in an ORIGINAL length-two source cycle, the
strictly ordered canonical cut-index map is literally the identity.
Thus the checked physical CutConnector equality covers BOTH original
connectors, with genuine core vertex or genuine quotient wagon
preimages. No source label is identified with a geometric owner.

This is a geometric normalization only. It does not assert a local
original selected B-copy piece or output system girth.
-/

namespace StructuralRamsey.Girth
open StructuralRamsey.RelStructure

universe u v
section OriginalTwoCoreConnectors

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
local notation "CoreEmb" =>
  RelStructure.Attachment.coreEmbedding C.toRelStructure S R f
local notation "CoreWagon" => generatedActualASupportTrain_coreWagonEmbedding
  A hA C.toRelStructure S R f T U
  (fun ν j p q h => Iff.mp (hRel ν j p q) h) hShared μ
local notation "Out" => attachedSelectedPictureOrderOneData
  A hA B D C family selected e R f T U hShared μ
local notation "GeomAllowed" => selectedOutputGeometricOwnerAllowed
  A hA B D C family selected e R f T U hShared μ
local notation "CutConnector" => attachedSelectedPicture_cutConnector
  A hA B D C family selected e R f T U hShared hRel μ

include hRel

/-- With two actual cuts, the two original source connectors both
have genuine core witness preimages in the correct connector sort. -/
theorem attachedSelectedPicture_two_cycle_core_connectors
    (K : (Out).BigCycle 2)
    (owner : Fin 2 → I ⊕ CoreEdge)
    (hAllowed : ∀ j, GeomAllowed (K.label j) (owner j))
    (hTwo : cyclicOwnerChanges owner = 2) :
    ∃ (u₀ u₁ : Y ⊕ Quotient (U.wagonSetoid μ)),
      K.connector (0 : Fin 2) = Sum.map CoreEmb CoreWagon u₀ ∧
      K.connector (1 : Fin 2) = Sum.map CoreEmb CoreWagon u₁ := by
  let j₀ : Fin (cyclicOwnerChanges owner) := ⟨0, by omega⟩
  let j₁ : Fin (cyclicOwnerChanges owner) := ⟨1, by omega⟩
  have hIndex₀ : cyclicOwnerCutIndex owner j₀ = (0 : Fin 2) := by
    apply Fin.ext
    simpa [j₀] using
      (cyclicOwnerCutIndex_val_eq_of_source_two owner hTwo j₀)
  have hIndex₁ : cyclicOwnerCutIndex owner j₁ = (1 : Fin 2) := by
    apply Fin.ext
    simpa [j₁] using
      (cyclicOwnerCutIndex_val_eq_of_source_two owner hTwo j₁)
  let u₀ := CutConnector K owner hAllowed j₀
  let u₁ := CutConnector K owner hAllowed j₁
  refine ⟨u₀, u₁, ?_, ?_⟩
  · have h := attachedSelectedPicture_cutConnector_eq
      A hA B D C family selected e R f T U hShared hRel μ
      K owner hAllowed j₀
    rw [hIndex₀] at h
    exact h.symm
  · have h := attachedSelectedPicture_cutConnector_eq
      A hA B D C family selected e R f T U hShared hRel μ
      K owner hAllowed j₁
    rw [hIndex₁] at h
    exact h.symm

/-- Exhaustive physical classification of both ORIGINAL connectors
into vertex/vertex, mixed, or wagon/wagon, without presupposing
that every output vertex/wagon belongs to the core. -/
theorem attachedSelectedPicture_two_cycle_core_connector_cases
    (K : (Out).BigCycle 2)
    (owner : Fin 2 → I ⊕ CoreEdge)
    (hAllowed : ∀ j, GeomAllowed (K.label j) (owner j))
    (hTwo : cyclicOwnerChanges owner = 2) :
    (∃ x y : Y,
      K.connector (0 : Fin 2) = Sum.inl (CoreEmb x) ∧
      K.connector (1 : Fin 2) = Sum.inl (CoreEmb y)) ∨
    (∃ (x : Y) (p : Quotient (U.wagonSetoid μ)),
      (K.connector (0 : Fin 2) = Sum.inl (CoreEmb x) ∧
       K.connector (1 : Fin 2) = Sum.inr (CoreWagon p)) ∨
      (K.connector (0 : Fin 2) = Sum.inr (CoreWagon p) ∧
       K.connector (1 : Fin 2) = Sum.inl (CoreEmb x))) ∨
    (∃ p q : Quotient (U.wagonSetoid μ),
      K.connector (0 : Fin 2) = Sum.inr (CoreWagon p) ∧
      K.connector (1 : Fin 2) = Sum.inr (CoreWagon q)) := by
  obtain ⟨u₀, u₁, h₀, h₁⟩ :=
    attachedSelectedPicture_two_cycle_core_connectors
      A hA B D C family selected e R f T U hShared hRel μ
      K owner hAllowed hTwo
  cases u₀ with
  | inl x =>
      cases u₁ with
      | inl y =>
          exact Or.inl ⟨x, y,
            by simpa only [Sum.map_inl] using h₀,
            by simpa only [Sum.map_inl] using h₁⟩
      | inr p =>
          exact Or.inr (Or.inl ⟨x, p, Or.inl
            ⟨by simpa only [Sum.map_inl] using h₀,
             by simpa only [Sum.map_inr] using h₁⟩⟩)
  | inr p =>
      cases u₁ with
      | inl x =>
          exact Or.inr (Or.inl ⟨x, p, Or.inr
            ⟨by simpa only [Sum.map_inr] using h₀,
             by simpa only [Sum.map_inl] using h₁⟩⟩)
      | inr q =>
          exact Or.inr (Or.inr ⟨p, q,
            by simpa only [Sum.map_inr] using h₀,
            by simpa only [Sum.map_inr] using h₁⟩)

end OriginalTwoCoreConnectors
end StructuralRamsey.Girth
