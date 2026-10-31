import Girth.TrainFillingInheritedParameters
import Girth.TrainFillingWagonImageTransfer

set_option Elab.async false

/-!
# Full filling bounds at the ACTUAL quotient-labelled restored cuts

The generic filling theorem uses old wagon names. The restored train has
its own quotient of the new physical edge labels. Its checked faithful
map into the old quotient commutes with the parent maps, so wagonImage is
literally the generic filled incidence record.

This closes that representation gap for full simultaneous system girth.
No old-edge nonemptiness or quotient surjectivity is needed: unused old
wagon names are harmless, and each long wagon is the parent of an edge.

The simultaneous all-cut endpoint takes only bounds at the supplied old
coordinates, plus the local first-fibre and old adjacent parameters. It
creates no extra top coordinate and leaves every ambient new edge intact.
Constructing the uniform witness and its scattering targets is separate.
-/

namespace StructuralRamsey.Girth.TrainFilling

universe v
variable {V I : Type v} (F : TrainFilling V) {m : ℕ}
variable (T : EdgeTrainLevels F.OldEdge m)
variable (copyCarrier : I → Set V) (copyEdges : I → Set F.OldEdge)

/-- Old incidence record at its actual quotient-wagon cut. -/
def oldCutData (ν : Fin (m + 1)) :
    OrderOneData V F.OldEdge I (Quotient (T.wagonSetoid ν)) :=
  F.oldData copyCarrier copyEdges (Quotient.mk (T.wagonSetoid ν))

/-- Restored incidence record using its OWN quotient wagon labels. -/
def inheritedCutData (ν : Fin (m + 1)) :
    OrderOneData V F.NewEdge I
      (Quotient ((F.inheritedTrain T).wagonSetoid ν.succ)) where
  edgeCarrier := fun e => e.1
  copyCarrier := copyCarrier
  copyEdges := fun i => {e | F.cover e ∈ copyEdges i}
  parent := Quotient.mk ((F.inheritedTrain T).wagonSetoid ν.succ)

/-- The full record, not only its wagon carriers, agrees after the
faithful parent renaming. All physical and designated labels are fixed. -/
theorem inheritedCutData_wagonImage_eq (ν : Fin (m + 1)) :
    (F.inheritedCutData T copyCarrier copyEdges ν).wagonImage
        (F.inheritedWagonEmbedding T ν) =
      F.filledData copyCarrier copyEdges (Quotient.mk (T.wagonSetoid ν)) := rfl

/-- The incidence record's wagon carrier is exactly the restored train's
physical quotient carrier. No wagon is identified by equal vertex sets. -/
theorem inheritedCutData_wagonVertex_iff (ν : Fin (m + 1))
    (p : Quotient ((F.inheritedTrain T).wagonSetoid ν.succ)) (x : V) :
    (F.inheritedCutData T copyCarrier copyEdges ν).WagonVertex p x ↔
      x ∈ (F.inheritedTrain T).wagonClassCarrier (fun e => e.1) ν.succ p := by
  induction p using Quotient.inductionOn with
  | h a =>
      change (∃ e : F.NewEdge, Quotient.mk _ e = Quotient.mk _ a ∧ x ∈ e.1) ↔
        ∃ e : F.NewEdge, (F.inheritedTrain T).rel ν.succ a e ∧ x ∈ e.1
      constructor
      · rintro ⟨e, he, hx⟩
        exact ⟨e, ((F.inheritedTrain T).equivalent _).symm (Quotient.exact he), hx⟩
      · rintro ⟨e, he, hx⟩
        exact ⟨e, Quotient.sound (((F.inheritedTrain T).equivalent _).symm he), hx⟩

/-- Apply the checked generic filling theorem at a real quotient cut,
then reflect its full bound onto the restored quotient-wagon labels. -/
theorem inheritedCutData_fullSystemGirthGT (ν : Fin (m + 1)) {q : ℕ}
    (hOld : (F.oldCutData T copyCarrier copyEdges ν).FullSystemGirthGT q)
    (hEdges : ∀ e f : F.NewEdge, e ≠ f → (e.1 ∩ f.1).Subsingleton) :
    (F.inheritedCutData T copyCarrier copyEdges ν).FullSystemGirthGT q := by
  apply OrderOneData.fullSystemGirth_of_wagonImage
    (F.inheritedCutData T copyCarrier copyEdges ν) (F.inheritedWagonEmbedding T ν)
  rw [F.inheritedCutData_wagonImage_eq]
  exact F.filled_fullSystemGirthGT copyCarrier copyEdges
    (Quotient.mk (T.wagonSetoid ν)) hOld hEdges

/-- The cutoff-two restoration delivers its actual train parameters and
ALL proper inherited system bounds together. Old proper indices are
j.castSucc for j : Fin m, INCLUDING the old equality cut. They become
restored indices j.castSucc.succ. Thus no positive restored tail coordinate
is omitted, and no bound at the old or restored universal top is requested. -/
theorem inheritedTrain_parameters_and_tailSystemGirth
    (allowed : Fin (m + 1 + 1) → Set V) (g : Fin m → ℕ)
    (hFirst : ∀ a b : F.NewEdge, a ≠ b → F.cover a = F.cover b →
      a.1 ∩ b.1 ⊆ allowed (0 : Fin (m + 1)).succ)
    (hOldParameters : T.AdjacentParameters (fun e => e.1)
      (fun ν => allowed ν.succ))
    (hOldGirth : ∀ j : Fin m,
      (F.oldCutData T copyCarrier copyEdges j.castSucc).FullSystemGirthGT (g j))
    (hEdges : ∀ e f : F.NewEdge, e ≠ f → (e.1 ∩ f.1).Subsingleton) :
    (F.inheritedTrain T).AdjacentParameters (fun e => e.1) allowed ∧
      ∀ j : Fin m,
        (F.inheritedCutData T copyCarrier copyEdges j.castSucc).FullSystemGirthGT (g j) := by
  refine ⟨F.inheritedTrain_adjacentParameters T allowed hFirst hOldParameters, ?_⟩
  intro j
  exact F.inheritedCutData_fullSystemGirthGT T copyCarrier copyEdges j.castSucc
    (hOldGirth j) hEdges

end StructuralRamsey.Girth.TrainFilling
