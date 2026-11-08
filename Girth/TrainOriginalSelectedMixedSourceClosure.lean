import Girth.TrainOriginalSelectedMixedShadowGeometry
import Mathlib.Tactic

set_option autoImplicit false
set_option Elab.async false

/-!
# Path A: close original length-two mixed source once minimal shadow differs

This is the actual ORIGINAL two-occurrence mixed source cycle. Literal
source incidence provides the designated B-copy's vertex and wagon
contacts automatically, with no separately assumed witness contacts.
The vertex contact has a real OLD B-copy preimage and lower Y-witness
membership; wagon contact gives a real lower witness wagon.
Both original geometric owner cuts give the OTHER owner's lower
vertex and wagon contacts, irrespective of its standard/core sort.

The only remaining owner premise is exactly the MINIMALITY consequence
that the other geometric owner is not the ORIGINAL selected standard i.
Draft #962 proves that finite minimal-owner fact separately. Given it,
old SupremeCycleBound and real lower FullSystemGirthGT produce a
physical original B-label short and a true GLOBAL simultaneous supreme
replacement of the original two-occurrence cycle.

No whole-cycle pullback, no relabelling of original B by geometric
owners, no support pruning, and no appendix/manuscript changes.
-/

namespace StructuralRamsey.Girth
open StructuralRamsey.RelStructure

universe u v
section OriginalSelectedMixedSource

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
  (fun ν j p q h => (hRel ν j p q).mp h) hShared μ
local notation "Out" => attachedSelectedPictureOrderOneData
  A hA B D C family selected e R f T U hShared μ
local notation "Wit" => sharedWitnessOrderOneData U μ
  Emb (Subtype.val : CoreEdge → Set Y)
local notation "Old" => selectedPictureOrderOneData
  A B D C family selected T μ
local notation "GeomAllowed" => selectedOutputGeometricOwnerAllowed
  A hA B D C family selected e R f T U hShared μ

/-- At exact source length two every original label is incident with
both original connectors; the cyclic orientation is explicitly checked. -/
private theorem original_two_label_all_contacts
    (K : (Out).BigCycle 2) (target pos : Fin 2) :
    (Out).Incident (K.label target) (K.connector pos) := by
  fin_cases target <;> fin_cases pos
  · exact K.left_incident 0
  · simpa [cyclicSucc] using K.right_incident 1
  · simpa [cyclicSucc] using K.right_incident 0
  · exact K.left_incident 1

/-- For an ORIGINAL mixed length-two selected B-source, exactly two
geometric owner cuts and a genuinely different other shadow suffice
for the FULL original global simultaneous supreme replacement.
Both original connector incidences are DERIVED, not hypotheses. -/
theorem attachedSelectedPicture_two_cycle_mixed_full_supreme_of_distinct_shadow
    {qcut : ℕ} (hq : 1 ≤ qcut)
    (hOld : (Old).SupremeCycleBound qcut)
    (hWitness : (Wit).FullSystemGirthGT qcut)
    (K : (Out).BigCycle 2) (hAccept : K.Acceptable)
    (owner : Fin 2 → I ⊕ CoreEdge)
    (hAllowed : ∀ j, GeomAllowed (K.label j) (owner j))
    (hTwo : cyclicOwnerChanges owner = 2)
    (target : Fin 2) (i : I) (q : Selected)
    (hOriginal : K.label target = Sum.inl (i,q))
    (hDifferent : Sum.inl i ≠ owner (cyclicSucc target))
    (x : Y) (p : Quotient (U.wagonSetoid μ))
    (hMixed :
      (K.connector 0 = Sum.inl (CoreEmb x) ∧
        K.connector 1 = Sum.inr (CoreWagon p)) ∨
      (K.connector 0 = Sum.inr (CoreWagon p) ∧
        K.connector 1 = Sum.inl (CoreEmb x))) :
    K.HasSimultaneousSupreme := by
  have hXCopy : CoreEmb x ∈ (Out).copyCarrier (i,q) := by
    rcases hMixed with ⟨h0, _h1⟩ | ⟨_h0, h1⟩
    · have h := original_two_label_all_contacts
        A hA B D C family selected e R f T U hShared μ K target 0
      rw [hOriginal, h0] at h
      exact h
    · have h := original_two_label_all_contacts
        A hA B D C family selected e R f T U hShared μ K target 1
      rw [hOriginal, h1] at h
      exact h
  have hWCopy : (Out).Meets (Sum.inl (i,q)) (CoreWagon p) := by
    rcases hMixed with ⟨_h0, h1⟩ | ⟨h0, _h1⟩
    · have h := original_two_label_all_contacts
        A hA B D C family selected e R f T U hShared μ K target 1
      rw [hOriginal, h1] at h
      exact h
    · have h := original_two_label_all_contacts
        A hA B D C family selected e R f T U hShared μ K target 0
      rw [hOriginal, h0] at h
      exact h
  obtain ⟨x0, hx0, hX, hIx⟩ :=
    attachedSelectedPicture_original_B_core_vertex_preimage_Y
      A hA B D C family selected e R f T U hShared hRel μ
      i q x hXCopy
  obtain ⟨hAx, hAp⟩ :=
    attachedSelectedPicture_two_cycle_mixed_shadow_incident
      A hA B D C family selected e R f T U hShared hRel μ
      K owner hAllowed hTwo target x p hMixed
  exact attachedSelectedPicture_two_cycle_mixed_supreme_of_shadow
    A hA B D C family selected e R f T U hShared hRel μ
    hq hOld hWitness K hAccept target i q hOriginal
    x0 x hx0 hX hIx p hMixed hWCopy
    (owner (cyclicSucc target)) hDifferent hAx hAp

end OriginalSelectedMixedSource
end StructuralRamsey.Girth
