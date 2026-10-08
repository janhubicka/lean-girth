import Girth.ForestMarkedCarrierContacts
import Girth.ForestObservableEventBound
import Mathlib.Tactic

/-!
# First-birth representatives of marked B-carrier masks

Let H₀ ⊆ H₁ ⊆ ... be a growing family of *actual* old carriers in a
fixed ambient vertex set, and fix finitely many marked vertex labels.
For each intersection mask, retain an old carrier from the FIRST
stage at which that mask occurs.  At every later stage these chosen
carriers form a nested finite core, with at most one carrier per mask,
and preserve all contacts of a prospective attachment confined to the
marked boundary.

Unlike choosing new representatives independently at each stage,
this retains genuine physical carriers and their first-birth stages
coherently. It does not bound their predecessor parameter histories
or certify joins of multiple B-carriers into a forest.
-/

namespace StructuralRamsey.Girth

universe u v
variable {I : Type u} {W : Type v} [Fintype I]

/-- A carrier representing a mask is chosen once, from the least stage
where that mask is realised.  Unrealisable masks have no role. -/
noncomputable def markedCarrierFirstRepresentative
    (H : ℕ → Set (Set W)) (f : I → W) (mask : Finset I) : Set W := by
  classical
  exact if h : ∃ t, MarkedCarrierMaskRealised (H t) f mask then
    Classical.choose (Nat.find_spec h)
  else ∅

theorem markedCarrierFirstRepresentative_spec
    (H : ℕ → Set (Set W)) (f : I → W) (mask : Finset I)
    (h : ∃ t, MarkedCarrierMaskRealised (H t) f mask) :
    markedCarrierFirstRepresentative H f mask ∈ H (Nat.find h) ∧
      markedCarrierMask f (markedCarrierFirstRepresentative H f mask) =
        mask := by
  classical
  simp only [markedCarrierFirstRepresentative, dif_pos h]
  exact Classical.choose_spec (Nat.find_spec h)

/-- At time t, retain the fixed first-birth representative of each mask
which has appeared by t. -/
noncomputable def coherentMarkedCarrierCore
    (H : ℕ → Set (Set W)) (f : I → W) (t : ℕ) :
    Finset (Set W) := by
  classical
  exact (Finset.univ.filter
      (fun mask : Finset I => MarkedCarrierMaskRealised (H t) f mask)).image
      (markedCarrierFirstRepresentative H f)

/-- Every carrier retained in a coherent core is physically present in
that stage's old family. -/
theorem coherentMarkedCarrierCore_subset
    (H : ℕ → Set (Set W)) (hMono : Monotone H)
    (f : I → W) (t : ℕ) :
    ∀ D ∈ coherentMarkedCarrierCore H f t, D ∈ H t := by
  classical
  intro D hD
  obtain ⟨mask, hmask, rfl⟩ := Finset.mem_image.mp hD
  have hAt : MarkedCarrierMaskRealised (H t) f mask :=
    (Finset.mem_filter.mp hmask).2
  have hex : ∃ s, MarkedCarrierMaskRealised (H s) f mask := ⟨t, hAt⟩
  have hFirst := (markedCarrierFirstRepresentative_spec H f mask hex).1
  exact hMono (Nat.find_le hex hAt) hFirst

/-- At each stage the finite core contains an actual representative of
every boundary mask realised by an old carrier at that stage. -/
theorem coherentMarkedCarrierCore_cover
    (H : ℕ → Set (Set W)) (f : I → W) (t : ℕ)
    (D : Set W) (hD : D ∈ H t) :
    ∃ R ∈ coherentMarkedCarrierCore H f t,
      markedCarrierMask f R = markedCarrierMask f D := by
  classical
  let mask := markedCarrierMask f D
  have hAt : MarkedCarrierMaskRealised (H t) f mask :=
    ⟨D, hD, rfl⟩
  refine ⟨markedCarrierFirstRepresentative H f mask, ?_,
    (markedCarrierFirstRepresentative_spec H f mask ⟨t, hAt⟩).2⟩
  apply Finset.mem_image.mpr
  exact ⟨mask,
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hAt⟩, rfl⟩

/-- Chosen physical carriers are never replaced by different carriers
when the history grows. -/
theorem coherentMarkedCarrierCore_mono
    (H : ℕ → Set (Set W)) (hMono : Monotone H)
    (f : I → W) {s t : ℕ} (hst : s ≤ t) :
    coherentMarkedCarrierCore H f s ⊆
      coherentMarkedCarrierCore H f t := by
  classical
  intro R hR
  obtain ⟨mask, hmask, hEq⟩ := Finset.mem_image.mp hR
  obtain ⟨D, hD, hdMask⟩ :
      MarkedCarrierMaskRealised (H s) f mask :=
    (Finset.mem_filter.mp hmask).2
  have hAt : MarkedCarrierMaskRealised (H t) f mask :=
    ⟨D, hMono hst hD, hdMask⟩
  exact Finset.mem_image.mpr
    ⟨mask, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hAt⟩, hEq⟩

/-- The entire coherent core has at most one selected physical carrier per
possible mask, independent of the number of stages and old carriers. -/
theorem coherentMarkedCarrierCore_card_le
    (H : ℕ → Set (Set W)) (f : I → W) (t : ℕ) :
    (coherentMarkedCarrierCore H f t).card ≤
      Fintype.card (Finset I) := by
  classical
  unfold coherentMarkedCarrierCore
  calc
    ((Finset.univ.filter
      (fun mask : Finset I => MarkedCarrierMaskRealised (H t) f mask)).image
        (markedCarrierFirstRepresentative H f)).card ≤
      (Finset.univ.filter
        (fun mask : Finset I => MarkedCarrierMaskRealised (H t) f mask)).card :=
      Finset.card_image_le
    _ ≤ (Finset.univ : Finset (Finset I)).card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    _ = Fintype.card (Finset I) := Finset.card_univ

/-- Exact one-attachment contact tests over the whole old family can be
performed over the same bounded, history-coherent carrier core at every
stage. This includes supported singleton / A-edge overlap predicates. -/
theorem freshCarrier_allContacts_iff_coherentCore
    (H : ℕ → Set (Set W)) (hMono : Monotone H)
    (f : I → W) (S : Set I) (t : ℕ)
    (e : Set W) (Allowed : Set W → Prop)
    (hContact : ∀ D ∈ H t, e ∩ D = (f '' S) ∩ D) :
    (∀ D ∈ H t, Allowed (e ∩ D)) ↔
      ∀ R ∈ coherentMarkedCarrierCore H f t,
        Allowed (e ∩ R) := by
  constructor
  · intro hAll R hR
    exact hAll R (coherentMarkedCarrierCore_subset H hMono f t R hR)
  · intro hCore D hD
    obtain ⟨R, hR, hMask⟩ :=
      coherentMarkedCarrierCore_cover H f t D hD
    have hRFamily : R ∈ H t :=
      coherentMarkedCarrierCore_subset H hMono f t R hR
    have hEq : e ∩ D = e ∩ R :=
      freshCarrier_inter_eq_of_sameMask
        (H t) f S e D R hContact hD hRFamily hMask.symm
    rw [hEq]
    exact hCore R hR

end StructuralRamsey.Girth
