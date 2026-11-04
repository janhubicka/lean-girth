import Girth.TrainTwoConsecutiveShortLiteralLabels
import Girth.TrainCyclicTwoRunOwnerBound
import Girth.TrainSelectedCycleGeometricOwners
import Mathlib.Tactic

/-!
# Path A: real geometric owner transport across a two-short output

The actual two-short output has exactly the old Fin n indexing.
The source cyclic two-run bound is imported from merged Path A #786;
this validation branch is based on main containing that dependency.
The two changed physical edges are carried by the receiving attached
standard i. Assign both replaced occurrences the owner Sum.inl i and
keep the source owner everywhere else. This is an ACTUALLY admissible
geometric owner assignment for the output cycle.

If the two source outer boundaries were owner cuts, the finite
two-occurrence reassignment lemma bounds the output MINIMUM cyclic
owner changes by the old number. This is the first-coordinate part
of the proposed lex descent for non-singleton chosen-long pieces.

It does not assume or assert strict descent of the second coordinate.
Circulation only, no appendix.
-/

namespace StructuralRamsey.Girth
open StructuralRamsey.RelStructure

universe u v
section ActualTwoShortOwnerTransport

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

local notation "S" => activeCarrier A C e.toFunctionEmbedding
local notation "CoreEdge" => OldACarrierEdge A R
local notation "Std" => RelStructure.Attachment.copyEmbedding C.toRelStructure S R f
local notation "CoreActual" => (fun (b : CoreEdge) =>
  actualAPictureEdgeEquiv A hA C.toRelStructure S R f
    (physicalCoreEdge (sharedOldACarrierInclusion A C.toRelStructure S) I b))
local notation "Out" => attachedSelectedPictureOrderOneData
  A hA B D C family selected e R f T U hShared μ
local notation "GeomAllowed" => selectedOutputGeometricOwnerAllowed
  A hA B D C family selected e R f T U hShared μ

/-- Exact indexed two-short label output plus receiving-standard support
makes the two-run reassignment a GEOMETRICALLY admissible owner choice.
No designated label identity or original target copy is needed. -/
theorem attachedSelectedPicture_two_short_owner_allowed
    {n : ℕ} (K H : (Out).BigCycle n)
    (owner : Fin n → I ⊕ CoreEdge)
    (hAllowed : ∀ j, GeomAllowed (K.label j) (owner j))
    (t : Fin n) (i : I) (first second : CoreEdge)
    (hLabels : ∀ j : Fin n,
      H.label j = K.twoConsecutiveShortLabels Out t
        (CoreActual first) (CoreActual second) j)
    (hFirst : (CoreActual first).1 ⊆ copyCarrier (Std i))
    (hSecond : (CoreActual second).1 ⊆ copyCarrier (Std i)) :
    ∀ j : Fin n, GeomAllowed (H.label j)
      (cyclicReplaceTwoOwners owner t (Sum.inl i)) j := by
  classical
  intro j
  by_cases hJt : j = t
  · subst j
    have hLabel :
        H.label t = Sum.inr (CoreActual first) := by
      rw [hLabels t]
      simp [OrderOneData.BigCycle.twoConsecutiveShortLabels]
    have hOwner :
        cyclicReplaceTwoOwners owner t (Sum.inl i) t = Sum.inl i := by
      simp [cyclicReplaceTwoOwners]
    rw [hLabel, hOwner]
    change (CoreActual first).1 ⊆ copyCarrier (Std i)
    exact hFirst
  · by_cases hJNext : j = cyclicSucc t
    · subst j
      have hNe : cyclicSucc t ≠ t :=
        cyclicSucc_ne_self_of_two_le K.length_ge_two t
      have hLabel :
          H.label (cyclicSucc t) = Sum.inr (CoreActual second) := by
        rw [hLabels (cyclicSucc t)]
        simp [OrderOneData.BigCycle.twoConsecutiveShortLabels, hNe]
      have hOwner :
          cyclicReplaceTwoOwners owner t (Sum.inl i)
              (cyclicSucc t) = Sum.inl i := by
        simp [cyclicReplaceTwoOwners]
      rw [hLabel, hOwner]
      change (CoreActual second).1 ⊆ copyCarrier (Std i)
      exact hSecond
    · have hLabel : H.label j = K.label j := by
        rw [hLabels j]
        simp [OrderOneData.BigCycle.twoConsecutiveShortLabels,
          hJt, hJNext]
      have hOwner :
          cyclicReplaceTwoOwners owner t (Sum.inl i) j = owner j := by
        simp [cyclicReplaceTwoOwners, hJt, hJNext]
      rw [hLabel, hOwner]
      exact hAllowed j

/-- Exact two-short physical output and two genuine outer source cuts
supply an ACTUAL minimum geometric owner assignment on the output
with no more cyclic cuts than the original owner word. This is
the FIRST coordinate of the desired lex rank. -/
theorem attachedSelectedPicture_two_short_minimum_cuts_le
    {n : ℕ} (K H : (Out).BigCycle n)
    (hn : 3 ≤ n)
    (owner : Fin n → I ⊕ CoreEdge)
    (hAllowed : ∀ j, GeomAllowed (K.label j) (owner j))
    (t : Fin n) (i : I) (first second : CoreEdge)
    (hLabels : ∀ j : Fin n,
      H.label j = K.twoConsecutiveShortLabels Out t
        (CoreActual first) (CoreActual second) j)
    (hFirst : (CoreActual first).1 ⊆ copyCarrier (Std i))
    (hSecond : (CoreActual second).1 ⊆ copyCarrier (Std i))
    (hLeftCut : owner (trainCyclicPred t) ≠ owner t)
    (hRightCut : owner (cyclicSucc t) ≠
      owner (cyclicSucc (cyclicSucc t))) :
    ∃ minimumOwner : Fin n → I ⊕ CoreEdge,
      (∀ j, GeomAllowed (H.label j) (minimumOwner j)) ∧
      (∀ other : Fin n → I ⊕ CoreEdge,
        (∀ j, GeomAllowed (H.label j) (other j)) →
          cyclicOwnerChanges minimumOwner ≤ cyclicOwnerChanges other) ∧
      cyclicOwnerChanges minimumOwner ≤ cyclicOwnerChanges owner := by
  let candidate := cyclicReplaceTwoOwners owner t (Sum.inl i)
  have hCandidate : ∀ j, GeomAllowed (H.label j) (candidate j) :=
    attachedSelectedPicture_two_short_owner_allowed
      A hA B D C family selected e R f T U hShared μ
      K H owner hAllowed t i first second hLabels hFirst hSecond
  obtain ⟨minimumOwner, hMinAllowed, hMin⟩ :=
    attachedSelectedPicture_cycle_exists_minimal_geometric_owners
      A hA B D C family selected e R f T U hShared μ H
  have hCutBound : cyclicOwnerChanges candidate ≤
      cyclicOwnerChanges owner :=
    cyclicOwnerChanges_replace_two_run_le
      (by omega : 2 ≤ n) owner t (Sum.inl i) hLeftCut hRightCut
  exact ⟨minimumOwner, hMinAllowed, hMin,
    (hMin candidate hCandidate).trans hCutBound⟩

end ActualTwoShortOwnerTransport
end StructuralRamsey.Girth
