import Girth.TrainSelectedCycleBoundaryIncidence
import Girth.TrainActualCopyLocalCoreIncidence

/-!
# Circulation: genuine two-standard wagon boundary of an actual selected cycle

This closes the standard/standard case of a RETAINED wagon boundary.
The two labels in the actual BigCycle are transported from two distinct
physical standards. Their genuine edge incidences give old support edges
in the SAME generated output wagon. The verified actual cross-standard
quotient theorem then yields one common core wagon ancestor, witnessed
by shared old support edges whose core carriers lie in the two
SPECIFIED witness copies.

In particular, geometric containment alone is not used to infer
label provenance; both labels and the distinct standard indices are
explicit hypotheses. Shared-train reflection and nonempty shared
support remain assumptions. This is not a cyclic witness reduct,
output A2/A3, or a system-girth preservation theorem. No appendix.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v

section SelectedTwoStandardWagon

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
local notation "OldEdge" => OldACarrierEdge A C.toRelStructure
local notation "SharedEdge" => SharedOldACarrierEdge A C.toRelStructure S
local notation "Label" => ({q : DesignatedCopy B D C family // q ∈ selected} ⊕ OldEdge)
local notation "Emb" => sharedOldACarrierCoreEmbedding A C.toRelStructure S R f
local notation "StdEdge" => (fun (i : I) (a : OldEdge) =>
  actualAPictureEdgeEquiv A hA C.toRelStructure S R f
    (physicalStandardEdge
      (sharedOldACarrierInclusion A C.toRelStructure S) Emb i a))
local notation "Train" => generatedActualASupportTrain
  A hA C.toRelStructure S R f T U hShared
local notation "Old" => selectedPictureOrderOneData
  A B D C family selected T μ
local notation "Out" => attachedSelectedPictureOrderOneData
  A hA B D C family selected e R f T U hShared μ
local notation "LabelMap" => attachedSelectedPictureLabel
  A hA B D C family selected e R f

include hRel

/-- At an ACTUAL wagon boundary of the selected output cycle,
two standard-labelled occurrences from distinct standards have
genuine old support edges and shared witness edges of a COMMON
core wagon. Each shared edge is contained in its prescribed Q_i
or Q_j, not merely somewhere in the ambient witness. -/
theorem attachedSelectedPicture_cycle_wagon_two_standard_copy_local
    {n : ℕ} (K : (Out).BigCycle n)
    (k : Fin n) (W : Quotient ((Train).wagonSetoid μ))
    (i j : I) (a b : Label) (hij : i ≠ j)
    (hW : K.connector k = Sum.inr W)
    (ha : K.label k = LabelMap i a)
    (hb : K.label (cyclicSucc k) = LabelMap j b) :
    ∃ (oldA oldB : OldEdge)
      (c : Quotient (U.wagonSetoid μ)) (s t : SharedEdge),
      oldA ∈ (Old).edges a ∧
      oldB ∈ (Old).edges b ∧
      T.rel μ (sharedOldACarrierInclusion A C.toRelStructure S s) oldA ∧
      T.rel μ (sharedOldACarrierInclusion A C.toRelStructure S t) oldB ∧
      Quotient.mk (U.wagonSetoid μ) (Emb i s) = c ∧
      Quotient.mk (U.wagonSetoid μ) (Emb j t) = c ∧
      (Emb i s).1 ⊆ Set.range (f i) ∧
      (Emb j t).1 ⊆ Set.range (f j) := by
  obtain ⟨oldA, oldB, hOldA, hOldB, hParentA, hParentB⟩ :=
    attachedSelectedPicture_cycle_wagon_boundary_source_edges
      A hA B D C family selected e R f T U hShared μ
      K k W i j a b hW ha hb
  have hSame : (Train).rel μ (StdEdge i oldA) (StdEdge j oldB) :=
    Quotient.exact (hParentA.trans hParentB.symm)
  obtain ⟨c, s, t, hsOld, htOld, hsCore, htCore, hsLocal, htLocal⟩ :=
    generatedActualASupportTrain_cross_standard_copy_local_incidence
      A hA C.toRelStructure S R f T U hShared hRel μ
      i j hij oldA oldB hSame
  exact ⟨oldA, oldB, c, s, t,
    hOldA, hOldB, hsOld, htOld, hsCore, htCore, hsLocal, htLocal⟩

end SelectedTwoStandardWagon

end StructuralRamsey.Girth
