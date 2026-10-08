import Girth.ForestMarkedCarrierContacts
import Mathlib.Data.Nat.Find
import Mathlib.Tactic

/-!
# Coherent first-occurrence certificates for marked B-carrier contacts

For an increasing sequence of old carrier families D₀ ⊆ D₁ ⊆ ... in a
common ambient vertex universe, choose one actual old carrier at the
first stage at which each marked-vertex contact mask is realised.

The selected carrier family is monotone and uniformly finite, and at
every stage it realises *exactly* the same marked contact masks as the
entire old carrier family. This resolves the temporal consistency of
bounded carrier representatives, not their ancestral-parameter depth
or the join-tree compatibility of the old B-copy family.
-/

namespace StructuralRamsey.Girth

universe u v
variable {I : Type u} {W : Type v} [Fintype I]

/-- A marked contact mask is realised by an old carrier by stage N. -/
def EverRealisedCarrierMask
    (family : ℕ → Set (Set W)) (f : I → W)
    (mask : Finset I) (N : ℕ) : Prop :=
  ∃ t : ℕ, t ≤ N ∧ MarkedCarrierMaskRealised (family t) f mask

/-- Retain the first actual carrier witnessing one mask, from its first
occurrence onwards. This uses one chosen representative per mask. -/
noncomputable def firstCarrierMaskWitnessAt
    (family : ℕ → Set (Set W)) (f : I → W)
    (mask : Finset I) (N n : ℕ) : Finset (Set W) := by
  classical
  exact if h : EverRealisedCarrierMask family f mask N then
    if Nat.find h ≤ n then
      {Classical.choose (Nat.find_spec h).2}
    else ∅
  else ∅

/-- Every retained carrier actually exists at its claimed stage. -/
theorem firstCarrierMaskWitnessAt_subset
    (family : ℕ → Set (Set W)) (f : I → W)
    (mask : Finset I) (N n : ℕ)
    (hMono : ∀ a b, a ≤ b → family a ⊆ family b) :
    (↑(firstCarrierMaskWitnessAt family f mask N n) :
      Set (Set W)) ⊆ family n := by
  classical
  intro R hR
  unfold firstCarrierMaskWitnessAt at hR
  split_ifs at hR with hEver hStage
  · have hSpec : MarkedCarrierMaskRealised
        (family (Nat.find hEver)) f mask :=
      (Nat.find_spec hEver).2
    have hOld : Classical.choose hSpec ∈ family (Nat.find hEver) :=
      (Classical.choose_spec hSpec).1
    have hEq : R = Classical.choose hSpec := by
      simpa using hR
    rw [hEq]
    exact hMono _ _ hStage hOld
  · simpa using hR
  · simpa using hR

/-- Witnesses, once selected, are retained at every later stage. -/
theorem firstCarrierMaskWitnessAt_mono
    (family : ℕ → Set (Set W)) (f : I → W)
    (mask : Finset I) (N n n' : ℕ) (hn : n ≤ n') :
    firstCarrierMaskWitnessAt family f mask N n ⊆
      firstCarrierMaskWitnessAt family f mask N n' := by
  classical
  intro R hR
  by_cases hEver : EverRealisedCarrierMask family f mask N
  · by_cases hStage : Nat.find hEver ≤ n
    · have hStage' := hStage.trans hn
      simpa [firstCarrierMaskWitnessAt, hEver, hStage, hStage'] using hR
    · have hFalse : False := by
        simpa [firstCarrierMaskWitnessAt, hEver, hStage] using hR
      exact hFalse.elim
  · have hFalse : False := by
      simpa [firstCarrierMaskWitnessAt, hEver] using hR
    exact hFalse.elim

/-- A single contact mask uses at most one chosen old carrier. -/
theorem firstCarrierMaskWitnessAt_card_le
    (family : ℕ → Set (Set W)) (f : I → W)
    (mask : Finset I) (N n : ℕ) :
    (firstCarrierMaskWitnessAt family f mask N n).card ≤ 1 := by
  classical
  unfold firstCarrierMaskWitnessAt
  split_ifs with hEver hStage <;> simp

/-- The monotone union of actual first-realisation representatives of
every marked-vertex mask. -/
noncomputable def coherentCarrierMaskCore
    (family : ℕ → Set (Set W)) (f : I → W)
    (N n : ℕ) : Finset (Set W) := by
  classical
  exact (Finset.univ : Finset (Finset I)).biUnion
    (fun mask => firstCarrierMaskWitnessAt family f mask N n)

/-- All retained carriers come from the current old family. -/
theorem coherentCarrierMaskCore_subset
    (family : ℕ → Set (Set W)) (f : I → W)
    (N n : ℕ)
    (hMono : ∀ a b, a ≤ b → family a ⊆ family b) :
    (↑(coherentCarrierMaskCore family f N n) : Set (Set W)) ⊆
      family n := by
  classical
  intro R hR
  change R ∈ coherentCarrierMaskCore family f N n at hR
  unfold coherentCarrierMaskCore at hR
  obtain ⟨mask, _, hMask⟩ := Finset.mem_biUnion.mp hR
  exact firstCarrierMaskWitnessAt_subset family f mask N n hMono hMask

/-- The same actual carrier representatives are kept throughout the
history, so no incompatible stagewise choice is made. -/
theorem coherentCarrierMaskCore_mono
    (family : ℕ → Set (Set W)) (f : I → W)
    (N n n' : ℕ) (hn : n ≤ n') :
    coherentCarrierMaskCore family f N n ⊆
      coherentCarrierMaskCore family f N n' := by
  classical
  intro R hR
  change R ∈ coherentCarrierMaskCore family f N n at hR
  change R ∈ coherentCarrierMaskCore family f N n'
  unfold coherentCarrierMaskCore at hR ⊢
  obtain ⟨mask, hMask, hOld⟩ := Finset.mem_biUnion.mp hR
  exact Finset.mem_biUnion.mpr
    ⟨mask, hMask,
      firstCarrierMaskWitnessAt_mono family f mask N n n' hn hOld⟩

/-- The chosen family is uniformly bounded by the number of marked
vertex subsets, independently of the number of old carriers or stages. -/
theorem coherentCarrierMaskCore_card_le
    (family : ℕ → Set (Set W)) (f : I → W)
    (N n : ℕ) :
    (coherentCarrierMaskCore family f N n).card ≤
      Fintype.card (Finset I) := by
  classical
  calc
    (coherentCarrierMaskCore family f N n).card ≤
        ∑ mask ∈ (Finset.univ : Finset (Finset I)),
          (firstCarrierMaskWitnessAt family f mask N n).card := by
      exact Finset.card_biUnion_le
    _ ≤ ∑ _mask ∈ (Finset.univ : Finset (Finset I)), 1 := by
      apply Finset.sum_le_sum
      intro mask _
      exact firstCarrierMaskWitnessAt_card_le family f mask N n
    _ = Fintype.card (Finset I) := by simp

/-- At any stage n ≤ N, the coherent finite core has exactly the same
realised contact masks as the entire old carrier family. -/
theorem coherentCarrierMaskCore_realised_iff
    (family : ℕ → Set (Set W)) (f : I → W)
    (N n : ℕ)
    (hMono : ∀ a b, a ≤ b → family a ⊆ family b)
    (hn : n ≤ N) (mask : Finset I) :
    MarkedCarrierMaskRealised (family n) f mask ↔
      ∃ R ∈ coherentCarrierMaskCore family f N n,
        markedCarrierMask f R = mask := by
  classical
  constructor
  · rintro ⟨D, hD, hDMask⟩
    have hEver : EverRealisedCarrierMask family f mask N :=
      ⟨n, hn, D, hD, hDMask⟩
    have hFirst : Nat.find hEver ≤ n :=
      Nat.find_min' hEver ⟨hn, D, hD, hDMask⟩
    have hSpec : MarkedCarrierMaskRealised
        (family (Nat.find hEver)) f mask :=
      (Nat.find_spec hEver).2
    let R : Set W := Classical.choose hSpec
    have hMask : markedCarrierMask f R = mask :=
      (Classical.choose_spec hSpec).2
    refine ⟨R, ?_, hMask⟩
    change R ∈ coherentCarrierMaskCore family f N n
    unfold coherentCarrierMaskCore
    apply Finset.mem_biUnion.mpr
    refine ⟨mask, Finset.mem_univ _, ?_⟩
    change R ∈ firstCarrierMaskWitnessAt family f mask N n
    simpa [firstCarrierMaskWitnessAt, hEver, hFirst, R]
  · rintro ⟨R, hR, hMask⟩
    exact ⟨R, coherentCarrierMaskCore_subset family f N n hMono hR,
      hMask⟩

end StructuralRamsey.Girth
