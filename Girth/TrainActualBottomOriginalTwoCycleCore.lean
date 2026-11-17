import Girth.TrainActualBottomOwnerCoreSeparation
import Girth.TrainBottomTwoLabelCoreIntersection
import Mathlib.Tactic

set_option autoImplicit false
set_option Elab.async false

/-!
# Original source length two, with two different geometric owners

Distinct geometric owners force the intersection of the TWO ORIGINAL
label carriers into the core. Every designated original B-label has
small-or-whole core boundary (from strong base projection), and every
ambient A-edge has the same boundary property because the attached
core is A-strong. Together with A-linearity, this is exactly an
allowed intersection of the two original bottom support pieces.

The existing bottom two-label lemma yields a globally supreme
ORIGINAL selected B-label immediately, without a shadow witness
supreme plan, any local forest assumption or any A1 hypothesis.
The double-wagon case is excluded by the same two-label lemma.
-/

namespace StructuralRamsey.Girth
open StructuralRamsey.RelStructure

universe u v
section OriginalTwoBottomDistinct

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

local notation "S" => activeCarrier A C e.toFunctionEmbedding
local notation "Actual" => RelStructure.Attachment.attach C.toRelStructure S R f
local notation "ActualEdge" => OldACarrierEdge A Actual
local notation "CoreEdge" => OldACarrierEdge A R
local notation "Selected" => {q : DesignatedCopy B D C family // q ∈ selected}
local notation "Core" => RelStructure.Attachment.coreEmbedding C.toRelStructure S R f
local notation "μBottom" => (⟨0, Nat.zero_lt_succ m⟩ : Fin (m + 1))
local notation "Out" => attachedSelectedPictureOrderOneData
  A hA B D C family selected e R f T U hShared μBottom
local notation "GeomAllowed" => selectedOutputGeometricOwnerAllowed
  A hA B D C family selected e R f T U hShared μBottom

/-- Exact A-strongness of the attached core implies that any ambient
A-edge meeting it in two vertices is wholly inside it. -/
theorem attachedSelectedPicture_bottom_coreEdges_strong_of_oldStrong
    (hOldStrong : AStrong A C.toRelStructure S) :
    ∀ edge : ActualEdge,
      ¬ (edge.1 ∩ copyCarrier Core).Subsingleton →
        edge.1 ⊆ copyCarrier Core := by
  have hStrong : AStrong A Actual (copyCarrier Core) :=
    attachment_core_aStrong C.toRelStructure S R f hA hOldStrong
  intro edge hLarge
  obtain ⟨a, ha⟩ := edge.2
  have hLargeA : ¬ (copyCarrier a ∩ copyCarrier Core).Subsingleton := by
    rw [← ha]
    exact hLarge
  have hSubset := hStrong a hLargeA
  rw [← ha] at hSubset
  exact hSubset

/-- A genuine ORIGINAL two-occurrence output cycle with two
distinct geometric owners has a globally supreme ORIGINAL
designated copy. In particular no acceptable double-wagon cycle
is possible in this configuration. -/
theorem attachedSelectedPicture_bottom_two_cycle_distinct_owner_supreme
    [Nontrivial UA]
    (hPhysical : ALinear A Actual)
    (hOldStrong : AStrong A C.toRelStructure S)
    (hBaseStrong : ∀ q : Selected, AStrong A D (copyCarrier q.1.base))
    (K : (Out).BigCycle 2)
    (owner : Fin 2 → I ⊕ CoreEdge)
    (hAllowed : ∀ j, GeomAllowed (K.label j) (owner j))
    (hDistinct : owner 0 ≠ owner 1) :
    K.HasSimultaneousSupreme := by
  let H := attachedSelectedPicture_bottomForestGeometry
    A hA B D C family selected e R f T U hShared hPhysical
  have hDesignated : ∀ a : (I × Selected) ⊕ ActualEdge,
      (Out).designated a →
        SmallOrWholeEdgeBoundary
          (Set.univ : Set (Set (RelStructure.Attachment.Vertex S (W := Y) (I := I))))
          (copyCarrier Core) ((Out).bottomForestPiece H a) :=
    attachedSelectedPicture_bottom_designated_boundary
      A hA B D C family selected e R f T U hShared H hBaseStrong
  have hCross :
      (Out).carrier (K.label 0) ∩ (Out).carrier (K.label 1) ⊆
        copyCarrier Core :=
    attachedSelectedPicture_bottom_distinctOwners_intersection_core
      A hA B D C family selected e R f T U hShared
      (K.label 0) (K.label 1) (owner 0) (owner 1)
      (hAllowed 0) (hAllowed 1) hDistinct
  exact K.two_bottom_supreme_of_core_separated Out H
    (copyCarrier Core)
    (attachedSelectedPicture_bottom_coreEdges_strong_of_oldStrong
      A hA C e R f hOldStrong)
    hDesignated hCross

end OriginalTwoBottomDistinct
end StructuralRamsey.Girth
