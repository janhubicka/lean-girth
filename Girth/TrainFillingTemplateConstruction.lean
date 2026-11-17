import Girth.TrainFillingCanonicalTemplate
import Girth.TrainFillingInheritedSystemGirth
import Girth.TrainEndpointGeometry

set_option Elab.async false

/-! # Linearity and restored invariants of the canonical filling -/

namespace StructuralRamsey.Girth

universe v

namespace UniformFillingData

variable {V X : Type v} (U : UniformFillingData V X)

/-- The whole constructed filling is linear: equal covers use the local
template, and distinct covers use containment and old edge linearity. -/
theorem generated_linear
    (hLocal : ∀ a b : U.TemplateEdge, a ≠ b → (a.1 ∩ b.1).Subsingleton) :
    ∀ e f : U.toTrainFilling.NewEdge, e ≠ f →
      (e.1 ∩ f.1).Subsingleton :=
  U.toTrainFilling.edgeLinear_of_fibreLinear U.old_linear (U.fibre_linear hLocal)

/-- Construct the filling and its full restored invariants directly from
local template data and the old proper-cut bounds. The old equality cut
is included; neither universal top is an additional girth coordinate. -/
theorem restored_parameters_and_tailSystemGirth
    {I : Type v} {m : ℕ} (T : EdgeTrainLevels U.OldEdge m)
    (copyCarrier : I → Set V) (copyEdges : I → Set U.OldEdge)
    (allowed : Fin (m + 1 + 1) → Set V) (g : Fin m → ℕ)
    (localAllowed : Set X)
    (hLocalParameter : ∀ a b : U.TemplateEdge, a ≠ b →
      a.1 ∩ b.1 ⊆ localAllowed)
    (hPlace : ∀ f : U.OldEdge, U.place f '' localAllowed ⊆
      allowed (0 : Fin (m + 1)).succ)
    (hLocalLinear : ∀ a b : U.TemplateEdge, a ≠ b →
      (a.1 ∩ b.1).Subsingleton)
    (hOldParameters : T.AdjacentParameters (fun e => e.1)
      (fun ν => allowed ν.succ))
    (hOldGirth : ∀ j : Fin m,
      (U.toTrainFilling.oldCutData T copyCarrier copyEdges j.castSucc).FullSystemGirthGT (g j)) :
    (U.toTrainFilling.inheritedTrain T).AdjacentParameters (fun e => e.1) allowed ∧
      ∀ j : Fin m,
        (U.toTrainFilling.inheritedCutData T copyCarrier copyEdges j.castSucc).FullSystemGirthGT (g j) := by
  exact U.toTrainFilling.inheritedTrain_parameters_and_tailSystemGirth
    T copyCarrier copyEdges allowed g
    (U.first_fibre_parameter localAllowed _ hLocalParameter hPlace)
    hOldParameters hOldGirth (U.fibre_linear hLocalLinear)

section RelationalTemplate

open StructuralRamsey.RelStructure
universe u
variable {L : RelLanguage.{u}} {UA : Type v}
variable (A : RelStructure L UA) (R : RelStructure L X) [Nontrivial UA]
variable (N : Set (Set V))
variable (place : {f : Set V // f ∈ N} → (X ↪ V))
variable (hRange : ∀ f, Set.range (place f) = f.1)
variable (hOldLinear : ∀ f g : {f : Set V // f ∈ N},
  f ≠ g → (f.1 ∩ g.1).Subsingleton)
variable (hCovers : ∀ x : X, ∃ a : Embedding A R, x ∈ copyCarrier a)

/-- Reuse the existing relational-to-physical linearity theorem for the
complete local A-support; no designated-edge restriction is made. -/
theorem ofSupportCopies_generated_linear (hLinear : ALinear A R) :
    let U := ofSupportCopies A R N place hRange hOldLinear hCovers
    ∀ e f : U.toTrainFilling.NewEdge, e ≠ f → (e.1 ∩ f.1).Subsingleton := by
  let U := ofSupportCopies A R N place hRange hOldLinear hCovers
  exact U.generated_linear
    (oldACarrier_edges_inter_subsingleton_of_aLinear A R hLinear)

end RelationalTemplate

end UniformFillingData
end StructuralRamsey.Girth
