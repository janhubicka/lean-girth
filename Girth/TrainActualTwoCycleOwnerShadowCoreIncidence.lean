import Girth.TrainSelectedCycleGeometricOwners
import Girth.TrainActualTwoStandardDesignatedBlock
import Girth.TrainActiveGluingWitness
import Girth.TrainSelectedCycleGeometricVertex
import Mathlib.Tactic

set_option autoImplicit false
set_option Elab.async false

/-!
# The other geometric owner of a literal two-cycle meets BOTH core vertices

The original output BigCycle at length two has the same TWO boundary
vertices incident with BOTH original source labels, not merely the one
whose index was chosen as the original designated supreme label.

An admissible geometric owner of the opposite literal output
occurrence is either a genuine standard index j (its entire
physical label carrier is contained in the whole attached standard)
or a genuine physical core A-edge b (the label IS that edge).
In the former case, the actual standard/core intersection gives
membership in the prescribed LOWER witness gluing copy j; in
the latter, exact physical-core carrier transport gives membership
in b itself.

This identifies the exact two lower-core vertex incidences of
the *OTHER* owner needed by the real witness shadow-copy/edge
probe, without postulating a second witness label, equating
original B-copy labels with standard owners, or assuming an
output supreme-cycle bound. No appendix.
-/

namespace StructuralRamsey.Girth
open StructuralRamsey.RelStructure

universe u v
section ActualTwoCycleOtherOwnerShadow

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
variable (μ : Fin (m + 1))

local notation "S" => activeCarrier A C e.toFunctionEmbedding
local notation "CoreEdge" => OldACarrierEdge A R
local notation "CoreEmb" => RelStructure.Attachment.coreEmbedding
  C.toRelStructure S R f
local notation "Std" => RelStructure.Attachment.copyEmbedding
  C.toRelStructure S R f
local notation "CoreActual" => (fun (b : CoreEdge) =>
  actualAPictureEdgeEquiv A hA C.toRelStructure S R f
    (physicalCoreEdge (sharedOldACarrierInclusion
      A C.toRelStructure S) I b))
local notation "Wit" => sharedWitnessOrderOneData U μ
  (sharedOldACarrierCoreEmbedding A C.toRelStructure S R f)
  (Subtype.val : CoreEdge → Set Y)
local notation "Out" => attachedSelectedPictureOrderOneData
  A hA B D C family selected e R f T U hShared μ
local notation "GeomAllowed" => selectedOutputGeometricOwnerAllowed
  A hA B D C family selected e R f T U hShared μ

/-- A literal BigCycle with two positions has EVERY labelled occurrence
incident with each of its TWO original connectors. This is an exact
incidence fact, without an acceptability or girth assumption. -/
theorem OrderOneData.BigCycle.two_all_label_connector_incidence
    {V E Q W : Type v} (G : OrderOneData V E Q W)
    (K : G.BigCycle 2) (k j : Fin 2) :
    G.Incident (K.label k) (K.connector j) := by
  have hk : k = (0 : Fin 2) ∨ k = (1 : Fin 2) := by
    fin_cases k <;> simp
  have hj : j = (0 : Fin 2) ∨ j = (1 : Fin 2) := by
    fin_cases j <;> simp
  rcases hk with hk | hk <;> rcases hj with hj | hj
  · subst k
    subst j
    exact K.left_incident 0
  · subst k
    subst j
    simpa [cyclicSucc] using K.right_incident (1 : Fin 2)
  · subst k
    subst j
    simpa [cyclicSucc] using K.right_incident (0 : Fin 2)
  · subst k
    subst j
    exact K.left_incident 1

/-- For the genuine attached selected output, the ACTUAL chosen
opposite geometric owner, whether a standard or a physical core
edge, contains BOTH lower core boundary vertices of the literal
original source length-two cycle.

No identified original B-label, no selected-copy shadow assumption,
no minimal-owner restriction, and no output FullSystemGirthGT. -/
theorem attachedSelectedPicture_two_cycle_other_owner_core_shadow
    (K : (Out).BigCycle 2)
    (owner : Fin 2 → I ⊕ CoreEdge)
    (hAllowed : ∀ j, GeomAllowed (K.label j) (owner j))
    (target : Fin 2) (x y : Y)
    (hx : K.connector (0 : Fin 2) = Sum.inl (CoreEmb x))
    (hy : K.connector (1 : Fin 2) = Sum.inl (CoreEmb y)) :
    x ∈ (Wit).carrier (owner (cyclicSucc target)) ∧
    y ∈ (Wit).carrier (owner (cyclicSucc target)) := by
  let other := cyclicSucc target
  have hxIn : CoreEmb x ∈ (Out).carrier (K.label other) := by
    have h := OrderOneData.BigCycle.two_all_label_connector_incidence
      (Out) K other (0 : Fin 2)
    rw [hx] at h
    exact h
  have hyIn : CoreEmb y ∈ (Out).carrier (K.label other) := by
    have h := OrderOneData.BigCycle.two_all_label_connector_incidence
      (Out) K other (1 : Fin 2)
    rw [hy] at h
    exact h
  cases ho : owner other with
  | inl j =>
      have hSubset : (Out).carrier (K.label other) ⊆
          copyCarrier (Std j) := by
        have h := hAllowed other
        rw [ho] at h
        exact h
      have hCoreX : CoreEmb x ∈ copyCarrier CoreEmb := ⟨x, rfl⟩
      have hCoreY : CoreEmb y ∈ copyCarrier CoreEmb := ⟨y, rfl⟩
      have lift {v : Y} (hv : CoreEmb v ∈ copyCarrier (Std j)) :
          v ∈ (Wit).copyCarrier j := by
        have hCore : CoreEmb v ∈ copyCarrier CoreEmb := ⟨v, rfl⟩
        have hInt :
            CoreEmb v ∈ copyCarrier ((CoreEmb).comp (f j)) := by
          rw [← attachment_copy_core_intersection
            C.toRelStructure S R f j]
          exact ⟨hv, hCore⟩
        obtain ⟨z, hz⟩ := hInt
        have hMem : v ∈ copyCarrier (f j) := by
          refine ⟨z, ?_⟩
          apply (CoreEmb).injective
          exact hz
        rw [activeCoreWitness_copyCarrier_eq
          A C e.toFunctionEmbedding R f U μ j]
        exact hMem
      exact ⟨lift (hSubset hxIn), lift (hSubset hyIn)⟩
  | inr b =>
      have hLabel : K.label other = Sum.inr (CoreActual b) := by
        have h := hAllowed other
        rw [ho] at h
        exact h
      have hBX : CoreEmb x ∈ (CoreActual b).1 := by
        rw [hLabel] at hxIn
        exact hxIn
      have hBY : CoreEmb y ∈ (CoreActual b).1 := by
        rw [hLabel] at hyIn
        exact hyIn
      rw [actualAPictureEdgeEquiv_core_carrier
        A hA C.toRelStructure S R f b] at hBX hBY
      obtain ⟨x', hxB, hxx⟩ := hBX
      obtain ⟨y', hyB, hyy⟩ := hBY
      have hx' : x' = x := (CoreEmb).injective hxx
      have hy' : y' = y := (CoreEmb).injective hyy
      subst x'
      subst y'
      exact ⟨hxB, hyB⟩

end ActualTwoCycleOtherOwnerShadow
end StructuralRamsey.Girth
