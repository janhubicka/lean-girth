import Girth.TrainCyclicOwnerRuns
import Girth.TrainSingleShortReplacement
import Mathlib.Tactic

/-!
# Circulation: no absorbable witness-edge singleton at a minimum segment boundary

A minimum GEOMETRIC source assignment must not leave a singleton
witness-core edge next to a standard that already contains the edge.
Changing only that occurrence to the neighbouring standard removes
one cyclic cut, and cannot create a new cut at the other side: the old
singleton core owner already differed from both neighbours.

We first prove the finite-combinatorial fact with genuine cyclic
indices (including the two-occurrence wrap). Then apply it to the
actual selected-picture cycle, using the verified core-edge singleton
isolation and the minimum-geometric-owner theorem.

No actual witness reduct, transport of A1--A3, or appendix result is
claimed here.
-/

namespace StructuralRamsey.Girth

universe v
variable {Owner : Type v} {n : ℕ}

/-- Cyclic successor is not stationary when there are at least
two occurrence indices. -/
theorem cyclicSucc_ne_self_of_two_le
    (hn : 2 ≤ n) (k : Fin n) : cyclicSucc k ≠ k := by
  intro h
  have hv : (k.val + 1) % n = k.val := by
    have hh := congrArg Fin.val h
    simpa [cyclicSucc] using hh
  by_cases hlt : k.val + 1 < n
  · rw [Nat.mod_eq_of_lt hlt] at hv
    omega
  · have hEq : k.val + 1 = n := by omega
    rw [hEq, Nat.mod_self] at hv
    omega

/-- Replace one cyclic owner while leaving every other position fixed. -/
def cyclicReplaceOwner
    (owner : Fin n → Owner) (k : Fin n) (a : Owner) :
    Fin n → Owner :=
  fun j => if j = k then a else owner j

/-- Absorbing an occurrence into its RIGHT neighbour strictly reduces
the number of cyclic changes, provided the old occurrence differed
from its predecessor too. The proof uses a proper inclusion of the
actual cyclic cut-position Finsets, so it covers n=2. -/
theorem cyclicOwnerChanges_absorb_right
    (hn : 2 ≤ n) (owner : Fin n → Owner)
    (k : Fin n) (a : Owner)
    (hNext : owner (cyclicSucc k) = a)
    (hOld : owner k ≠ a)
    (hPrev : owner (trainCyclicPred k) ≠ owner k) :
    cyclicOwnerChanges (cyclicReplaceOwner owner k a) <
      cyclicOwnerChanges owner := by
  classical
  let changed := cyclicReplaceOwner owner k a
  let newCuts := cyclicOwnerCutPositions changed
  let oldCuts := cyclicOwnerCutPositions owner
  have hSuccNe : cyclicSucc k ≠ k := cyclicSucc_ne_self_of_two_le hn k
  have hChangedK : changed k = a := by
    simp [changed, cyclicReplaceOwner]
  have hChangedSucc : changed (cyclicSucc k) = a := by
    simp [changed, cyclicReplaceOwner, hSuccNe, hNext]
  have hSub : newCuts ⊆ oldCuts := by
    intro j hj
    have hNew := (mem_cyclicOwnerCutPositions_iff changed j).mp hj
    by_cases hjk : j = k
    · subst j
      exact False.elim (hNew (hChangedK.trans hChangedSucc.symm))
    · by_cases hsk : cyclicSucc j = k
      · have hPredJ : j = trainCyclicPred k := by
          have hh := congrArg trainCyclicPred hsk
          rw [trainCyclicPred_cyclicSucc_of_two_le hn j] at hh
          exact hh
        apply (mem_cyclicOwnerCutPositions_iff owner j).mpr
        rw [hsk, hPredJ]
        exact hPrev
      · apply (mem_cyclicOwnerCutPositions_iff owner j).mpr
        simpa [changed, cyclicReplaceOwner, hjk, hsk] using hNew
  have hOldK : k ∈ oldCuts := by
    apply (mem_cyclicOwnerCutPositions_iff owner k).mpr
    rw [hNext]
    exact hOld
  have hNewK : k ∉ newCuts := by
    intro hk
    have h := (mem_cyclicOwnerCutPositions_iff changed k).mp hk
    exact h (hChangedK.trans hChangedSucc.symm)
  have hNe : newCuts ≠ oldCuts := by
    intro heq
    apply hNewK
    rw [heq]
    exact hOldK
  have hProper : newCuts ⊂ oldCuts := lt_of_le_of_ne hSub hNe
  have hCard : newCuts.card < oldCuts.card :=
    Finset.card_lt_card hProper
  calc
    cyclicOwnerChanges (cyclicReplaceOwner owner k a) =
        (cyclicOwnerCutPositions changed).card :=
      (cyclicOwnerCutPositions_card changed).symm
    _ < (cyclicOwnerCutPositions owner).card := hCard
    _ = cyclicOwnerChanges owner := cyclicOwnerCutPositions_card owner

/-- The symmetric one-point move absorbs an occurrence into its
LEFT neighbour. The changed boundary at its predecessor disappears;
the other boundary was already a cut and cannot become a new one.
This proof also includes cyclic wraparound at n=2. -/
theorem cyclicOwnerChanges_absorb_left
    (hn : 2 ≤ n) (owner : Fin n → Owner)
    (k : Fin n) (a : Owner)
    (hPrev : owner (trainCyclicPred k) = a)
    (hOld : owner k ≠ a)
    (hNext : owner k ≠ owner (cyclicSucc k)) :
    cyclicOwnerChanges (cyclicReplaceOwner owner k a) <
      cyclicOwnerChanges owner := by
  classical
  let changed := cyclicReplaceOwner owner k a
  let newCuts := cyclicOwnerCutPositions changed
  let oldCuts := cyclicOwnerCutPositions owner
  have hPredNe : trainCyclicPred k ≠ k := by
    intro hp
    have hh := cyclicSucc_trainCyclicPred_of_two_le hn k
    rw [hp] at hh
    exact (cyclicSucc_ne_self_of_two_le hn k) hh
  have hChangedK : changed k = a := by
    simp [changed, cyclicReplaceOwner]
  have hChangedPred : changed (trainCyclicPred k) = a := by
    simp [changed, cyclicReplaceOwner, hPredNe, hPrev]
  have hSub : newCuts ⊆ oldCuts := by
    intro j hj
    have hNew := (mem_cyclicOwnerCutPositions_iff changed j).mp hj
    by_cases hjk : j = k
    · subst j
      exact (mem_cyclicOwnerCutPositions_iff owner k).mpr hNext
    · by_cases hsk : cyclicSucc j = k
      · have hjPred : j = trainCyclicPred k := by
          have hh := congrArg trainCyclicPred hsk
          rw [trainCyclicPred_cyclicSucc_of_two_le hn j] at hh
          exact hh
        have hHere : changed j = a := by
          rw [hjPred]
          exact hChangedPred
        have hThere : changed (cyclicSucc j) = a := by
          rw [hsk]
          exact hChangedK
        exact False.elim (hNew (hHere.trans hThere.symm))
      · apply (mem_cyclicOwnerCutPositions_iff owner j).mpr
        simpa [changed, cyclicReplaceOwner, hjk, hsk] using hNew
  have hOldPred : trainCyclicPred k ∈ oldCuts := by
    apply (mem_cyclicOwnerCutPositions_iff owner (trainCyclicPred k)).mpr
    rw [cyclicSucc_trainCyclicPred_of_two_le hn k, hPrev]
    exact hOld.symm
  have hNewPred : trainCyclicPred k ∉ newCuts := by
    intro hp
    have hh :=
      (mem_cyclicOwnerCutPositions_iff changed (trainCyclicPred k)).mp hp
    rw [cyclicSucc_trainCyclicPred_of_two_le hn k] at hh
    exact hh (hChangedPred.trans hChangedK.symm)
  have hNe : newCuts ≠ oldCuts := by
    intro heq
    apply hNewPred
    rw [heq]
    exact hOldPred
  have hProper : newCuts ⊂ oldCuts := lt_of_le_of_ne hSub hNe
  have hCard : newCuts.card < oldCuts.card :=
    Finset.card_lt_card hProper
  calc
    cyclicOwnerChanges (cyclicReplaceOwner owner k a) =
        (cyclicOwnerCutPositions changed).card :=
      (cyclicOwnerCutPositions_card changed).symm
    _ < (cyclicOwnerCutPositions owner).card := hCard
    _ = cyclicOwnerChanges owner := cyclicOwnerCutPositions_card owner

section GeometricCoreAbsorption

open StructuralRamsey.RelStructure

universe u w
variable {L : RelLanguage.{u}} {UA VB P X Y I : Type w}
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
local notation "Out" => attachedSelectedPictureOrderOneData
  A hA B D C family selected e R f T U hShared μ
local notation "Std" => RelStructure.Attachment.copyEmbedding C.toRelStructure S R f
local notation "GeomAllowed" => selectedOutputGeometricOwnerAllowed
  A hA B D C family selected e R f T U hShared μ

/-- At the minimum geometric owner assignment, a core-edge singleton
cannot sit immediately before standard i if the whole singleton
edge is contained in i's standard. Otherwise reassigning that one
occurrence removes a cyclic cut. -/
theorem attachedSelectedPicture_minimal_no_absorbable_core_right
    {n : ℕ} (K : (Out).BigCycle n)
    (owner : Fin n → I ⊕ CoreEdge)
    (hAllowed : ∀ k : Fin n, GeomAllowed (K.label k) (owner k))
    (hMinimal : ∀ other : Fin n → I ⊕ CoreEdge,
      (∀ k : Fin n, GeomAllowed (K.label k) (other k)) →
      cyclicOwnerChanges owner ≤ cyclicOwnerChanges other)
    (k : Fin n) (b : CoreEdge) (i : I)
    (hCore : owner k = Sum.inr b)
    (hNext : owner (cyclicSucc k) = Sum.inl i)
    (hInStandard : (Out).carrier (K.label k) ⊆
      copyCarrier (Std i)) : False := by
  classical
  have hOld : owner k ≠ Sum.inl i := by
    rw [hCore]
    intro h
    cases h
  have hPrev : owner (trainCyclicPred k) ≠ owner k := by
    have hIsolated :=
      attachedSelectedPicture_geometric_core_owner_isolated
        A hA B D C family selected e R f T U hShared μ
        K owner hAllowed k b hCore
    intro heq
    apply hIsolated.1
    rw [heq]
    exact hCore
  let alternative :=
    cyclicReplaceOwner owner k (Sum.inl i : I ⊕ CoreEdge)
  have hAltAllowed : ∀ j : Fin n,
      GeomAllowed (K.label j) (alternative j) := by
    intro j
    by_cases hj : j = k
    · subst j
      have hChoice : alternative k = Sum.inl i := by
        simp [alternative, cyclicReplaceOwner]
      rw [hChoice]
      change (Out).carrier (K.label k) ⊆ copyCarrier (Std i)
      exact hInStandard
    · have hSame : alternative j = owner j := by
        simp [alternative, cyclicReplaceOwner, hj]
      rw [hSame]
      exact hAllowed j
  have hDrop := cyclicOwnerChanges_absorb_right
    K.length_ge_two owner k (Sum.inl i : I ⊕ CoreEdge)
    hNext hOld hPrev
  have hMin := hMinimal alternative hAltAllowed
  exact (Nat.not_lt_of_ge hMin) hDrop

/-- Likewise, a minimum geometric owner assignment cannot place
a core-edge singleton immediately AFTER a standard that contains it.
This is the other orientation of the necessary no-improvement condition. -/
theorem attachedSelectedPicture_minimal_no_absorbable_core_left
    {n : ℕ} (K : (Out).BigCycle n)
    (owner : Fin n → I ⊕ CoreEdge)
    (hAllowed : ∀ k : Fin n, GeomAllowed (K.label k) (owner k))
    (hMinimal : ∀ other : Fin n → I ⊕ CoreEdge,
      (∀ k : Fin n, GeomAllowed (K.label k) (other k)) →
      cyclicOwnerChanges owner ≤ cyclicOwnerChanges other)
    (k : Fin n) (b : CoreEdge) (i : I)
    (hCore : owner k = Sum.inr b)
    (hPrev : owner (trainCyclicPred k) = Sum.inl i)
    (hInStandard : (Out).carrier (K.label k) ⊆
      copyCarrier (Std i)) : False := by
  classical
  have hOld : owner k ≠ Sum.inl i := by
    rw [hCore]
    intro h
    cases h
  have hNext : owner k ≠ owner (cyclicSucc k) := by
    have hIsolated :=
      attachedSelectedPicture_geometric_core_owner_isolated
        A hA B D C family selected e R f T U hShared μ
        K owner hAllowed k b hCore
    intro heq
    apply hIsolated.2
    calc
      owner (cyclicSucc k) = owner k := heq.symm
      _ = Sum.inr b := hCore
  let alternative :=
    cyclicReplaceOwner owner k (Sum.inl i : I ⊕ CoreEdge)
  have hAltAllowed : ∀ j : Fin n,
      GeomAllowed (K.label j) (alternative j) := by
    intro j
    by_cases hj : j = k
    · subst j
      have hChoice : alternative k = Sum.inl i := by
        simp [alternative, cyclicReplaceOwner]
      rw [hChoice]
      change (Out).carrier (K.label k) ⊆ copyCarrier (Std i)
      exact hInStandard
    · have hSame : alternative j = owner j := by
        simp [alternative, cyclicReplaceOwner, hj]
      rw [hSame]
      exact hAllowed j
  have hDrop := cyclicOwnerChanges_absorb_left
    K.length_ge_two owner k (Sum.inl i : I ⊕ CoreEdge)
    hPrev hOld hNext
  have hMin := hMinimal alternative hAltAllowed
  exact (Nat.not_lt_of_ge hMin) hDrop

end GeometricCoreAbsorption
end StructuralRamsey.Girth
