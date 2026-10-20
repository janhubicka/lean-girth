import Girth.TrainSelectedCycleGeometricOwners
import Mathlib.Tactic

/-!
# Circulation: identify the one-segment case of a minimum geometric assignment

The geometric owner minimization is already checked. Its zero-change
case still has to mean exactly that all physical output labels lie in
ONE attached standard. We prove the elementary cyclic-connectedness
fact for arbitrary finite owner types: equality along every successor
forces a nonempty finite cyclic word to be constant.

For a genuine selected-picture BigCycle, the minimum GEOMETRIC owner
assignment has zero cuts precisely when every occurrence carrier is
contained in some single standard. The other direction uses an
explicitly admissible constant assignment; the forward direction
excludes core-edge singleton owners by BigCycle adjacent-label
distinctness. In the positive-cut case we obtain an actual cyclic
boundary index with different adjacent owners.

The proof does NOT yet construct the maximal cyclic runs, associate
them with witness labels, or build the legal witness BigCycle. No
appendix input.
-/

namespace StructuralRamsey.Girth

universe v
variable {Owner : Type v}

/-- A nonempty finite cyclic owner word has no changes if and only
if all its positions have one common owner. -/
theorem cyclicOwnerChanges_zero_iff_constant
    {n : ℕ} (hn : 0 < n) (owner : Fin n → Owner) :
    cyclicOwnerChanges owner = 0 ↔
      ∃ a : Owner, ∀ k : Fin n, owner k = a := by
  constructor
  · intro hZero
    have hSuccessor :=
      (cyclicOwnerChanges_eq_zero_iff owner).mp hZero
    let zero : Fin n := ⟨0, hn⟩
    have hFromZero : ∀ k : ℕ, ∀ hk : k < n,
        owner ⟨k, hk⟩ = owner zero := by
      intro k
      induction k with
      | zero =>
          intro hk
          rfl
      | succ k ih =>
          intro hSucc
          have hk : k < n := by omega
          have hs : cyclicSucc (⟨k, hk⟩ : Fin n) =
              ⟨k + 1, hSucc⟩ := by
            apply Fin.ext
            change (k + 1) % n = k + 1
            exact Nat.mod_eq_of_lt hSucc
          calc
            owner ⟨k + 1, hSucc⟩ =
                owner (cyclicSucc ⟨k, hk⟩) := by rw [hs]
            _ = owner ⟨k, hk⟩ := (hSuccessor ⟨k, hk⟩).symm
            _ = owner zero := ih hk
    refine ⟨owner zero, ?_⟩
    intro k
    exact hFromZero k.val k.isLt
  · rintro ⟨a, h⟩
    apply (cyclicOwnerChanges_eq_zero_iff owner).mpr
    intro k
    rw [h k, h (cyclicSucc k)]

/-- Cyclic owner boundaries are concrete positions, with the boundary
after k present exactly when k and its successor have different owners. -/
noncomputable def cyclicOwnerCutPositions
    {n : ℕ} (owner : Fin n → Owner) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter (fun k => owner k ≠ owner (cyclicSucc k))

theorem mem_cyclicOwnerCutPositions_iff
    {n : ℕ} (owner : Fin n → Owner) (k : Fin n) :
    k ∈ cyclicOwnerCutPositions owner ↔
      owner k ≠ owner (cyclicSucc k) := by
  classical
  simp [cyclicOwnerCutPositions]

/-- The number of actual cyclic cut positions is the numerical
minimization parameter, not merely bounded by that parameter. -/
theorem cyclicOwnerCutPositions_card
    {n : ℕ} (owner : Fin n → Owner) :
    (cyclicOwnerCutPositions owner).card =
      cyclicOwnerChanges owner := rfl

/-- Any nonzero cyclic change count provides an actual boundary
at which the word can be cut and its maximal runs enumerated. -/
theorem exists_cyclicOwnerCut_of_pos
    {n : ℕ} (owner : Fin n → Owner)
    (hPos : 0 < cyclicOwnerChanges owner) :
    ∃ k : Fin n, owner k ≠ owner (cyclicSucc k) := by
  by_contra hNot
  have hNoChange : ∀ k : Fin n,
      owner k = owner (cyclicSucc k) := by
    intro k
    by_contra hk
    exact hNot ⟨k, hk⟩
  have hZero := (cyclicOwnerChanges_eq_zero_iff owner).mpr hNoChange
  omega

section SelectedPictureOneRun

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

/-- A MINIMUM geometric assignment on an actual selected-picture BigCycle
has no cyclic boundaries exactly when every physical occurrence carrier
lies in one attached standard. In particular the one-segment alternative
is geometric, not tied to literal source-label provenance. -/
theorem attachedSelectedPicture_minimal_zero_iff_one_standard
    {n : ℕ} (K : (Out).BigCycle n)
    (owner : Fin n → I ⊕ CoreEdge)
    (hAllowed : ∀ k : Fin n, GeomAllowed (K.label k) (owner k))
    (hMinimal : ∀ other : Fin n → I ⊕ CoreEdge,
      (∀ k : Fin n, GeomAllowed (K.label k) (other k)) →
      cyclicOwnerChanges owner ≤ cyclicOwnerChanges other) :
    cyclicOwnerChanges owner = 0 ↔
      ∃ i : I, ∀ k : Fin n,
        (Out).carrier (K.label k) ⊆ copyCarrier (Std i) := by
  constructor
  · intro hZero
    have hn : 0 < n := by
      have hh := K.length_ge_two
      omega
    obtain ⟨a, hConst⟩ :=
      (cyclicOwnerChanges_zero_iff_constant hn owner).mp hZero
    have hNotCore : ∀ b : CoreEdge, a ≠ Sum.inr b := by
      intro b hab
      let k : Fin n := ⟨0, hn⟩
      have hHere : owner k = Sum.inr b := (hConst k).trans hab
      have hSucc : owner (cyclicSucc k) = Sum.inr b :=
        (hConst (cyclicSucc k)).trans hab
      have hIsolated :=
        attachedSelectedPicture_geometric_core_owner_isolated
          A hA B D C family selected e R f T U hShared μ
          K owner hAllowed k b hHere
      exact hIsolated.2 hSucc
    cases ha : a with
    | inl i =>
        refine ⟨i, ?_⟩
        intro k
        have hk := hAllowed k
        rw [hConst k, ha] at hk
        exact hk
    | inr b =>
        exact False.elim (hNotCore b ha)
  · rintro ⟨i, hContain⟩
    have hConstantAllowed : ∀ k : Fin n,
        GeomAllowed (K.label k)
          (Sum.inl i : I ⊕ CoreEdge) := by
      intro k
      exact hContain k
    have hZeroConstant :
        cyclicOwnerChanges
          (fun _ : Fin n => (Sum.inl i : I ⊕ CoreEdge)) = 0 :=
      (cyclicOwnerChanges_eq_zero_iff
        (fun _ : Fin n => (Sum.inl i : I ⊕ CoreEdge))).mpr
        (by intro k; rfl)
    have hBound := hMinimal
      (fun _ : Fin n => (Sum.inl i : I ⊕ CoreEdge))
      hConstantAllowed
    rw [hZeroConstant] at hBound
    exact Nat.eq_zero_of_le_zero hBound

/-- If no attached standard contains every occurrence carrier, every
minimum geometric owner assignment has a genuine cyclic boundary.
That boundary can be chosen as the origin of the next reduction word. -/
theorem attachedSelectedPicture_minimal_has_cut_of_not_one_standard
    {n : ℕ} (K : (Out).BigCycle n)
    (owner : Fin n → I ⊕ CoreEdge)
    (hAllowed : ∀ k : Fin n, GeomAllowed (K.label k) (owner k))
    (hMinimal : ∀ other : Fin n → I ⊕ CoreEdge,
      (∀ k : Fin n, GeomAllowed (K.label k) (other k)) →
      cyclicOwnerChanges owner ≤ cyclicOwnerChanges other)
    (hNotOne : ¬ ∃ i : I, ∀ k : Fin n,
      (Out).carrier (K.label k) ⊆ copyCarrier (Std i)) :
    ∃ k : Fin n, owner k ≠ owner (cyclicSucc k) := by
  have hNotZero : cyclicOwnerChanges owner ≠ 0 := by
    intro h
    exact hNotOne ((attachedSelectedPicture_minimal_zero_iff_one_standard
      A hA B D C family selected e R f T U hShared μ
      K owner hAllowed hMinimal).mp h)
  exact exists_cyclicOwnerCut_of_pos owner (Nat.pos_of_ne_zero hNotZero)

end SelectedPictureOneRun
end StructuralRamsey.Girth
