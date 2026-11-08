import Girth.TrainSelectedCycleGeometricOwners
import Mathlib.Tactic

set_option autoImplicit false
set_option Elab.async false

/-!
# Path A: an original selected B-label has a distinct other shadow
in a MINIMAL genuine length-two two-cut owner assignment

The original designated occurrence is literally labelled (i,q).
It is always geometrically eligible to be owned by its ORIGINAL
attached standard i, regardless of which (possibly different)
geometric owner the minimal assignment gives it.

If the OTHER occurrence were also eligible for owner i, a constant
two-occurrence owner assignment would have ZERO cyclic cuts.
Consequently a MINIMAL geometric owner assignment with exactly
TWO changes forces the actual other owner's witness shadow to
differ from Sum.inl i.

This is the needed input to the already checked witness standard-vs-
other shadow physical probe: the shadow may be another designated
gluing standard OR a genuine physical core A-edge, but cannot be
the original standard i. No invented equality between original
source B-label and its chosen geometric owner; no appendix/TeX.
-/

namespace StructuralRamsey.Girth
open StructuralRamsey.RelStructure

universe u v

section ActualMinimalTwoCycleShadow

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

local notation "CoreEdge" => OldACarrierEdge A R
local notation "OldEdge" => OldACarrierEdge A C.toRelStructure
local notation "Selected" =>
  {q : DesignatedCopy B D C family // q ∈ selected}
local notation "ActualEdge" => OldACarrierEdge A
  (RelStructure.Attachment.attach C.toRelStructure
    (activeCarrier A C e.toFunctionEmbedding) R f)
local notation "Out" => attachedSelectedPictureOrderOneData
  A hA B D C family selected e R f T U hShared μ
local notation "LabelMap" => attachedSelectedPictureLabel
  A hA B D C family selected e R f
local notation "GeomAllowed" => selectedOutputGeometricOwnerAllowed
  A hA B D C family selected e R f T U hShared μ

/-- A minimal actual geometric owner word with two cuts cannot
assign the OTHER occurrence the standard of an original literal
designated label (i,q), because the label (i,q) itself is always
eligible for i and the resulting constant assignment would have
zero cuts. -/
theorem attachedSelectedPicture_two_cycle_original_standard_diff_shadow
    (K : (Out).BigCycle 2)
    (owner : Fin 2 → I ⊕ CoreEdge)
    (hAllowed : ∀ k, GeomAllowed (K.label k) (owner k))
    (hMinimal : ∀ other : Fin 2 → I ⊕ CoreEdge,
      (∀ k, GeomAllowed (K.label k) (other k)) →
        cyclicOwnerChanges owner ≤ cyclicOwnerChanges other)
    (hTwo : cyclicOwnerChanges owner = 2)
    (target : Fin 2) (i : I) (q : Selected)
    (hOriginal : K.label target = Sum.inl (i,q)) :
    owner (cyclicSucc target) ≠ Sum.inl i := by
  intro hOther
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
  have hConstAllowed : ∀ k : Fin 2,
      GeomAllowed (K.label k) (Sum.inl i) := by
    intro k
    have hk : k = target ∨ k = cyclicSucc target := by
      fin_cases target <;> fin_cases k <;> simp [cyclicSucc]
    rcases hk with hk | hk
    · rw [hk]
      exact hOriginalAllowed
    · rw [hk]
      have h := hAllowed (cyclicSucc target)
      rw [hOther] at h
      exact h
  have hZero :
      cyclicOwnerChanges (fun _ : Fin 2 => (Sum.inl i : I ⊕ CoreEdge)) = 0 :=
    (cyclicOwnerChanges_eq_zero_iff
      (fun _ : Fin 2 => (Sum.inl i : I ⊕ CoreEdge))).2
      (by intro k; rfl)
  have hLess := hMinimal (fun _ => Sum.inl i) hConstAllowed
  rw [hTwo, hZero] at hLess
  omega

end ActualMinimalTwoCycleShadow
end StructuralRamsey.Girth
