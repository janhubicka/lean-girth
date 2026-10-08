import Girth.ForestFiniteCycleCore
import Mathlib.Data.Nat.Find
import Mathlib.Tactic

/-!
# Coherent bounded cycle witnesses along increasing support histories

For a fixed finite batch K of proposed edges and an increasing old support
H₀ ⊆ H₁ ⊆ ..., mark for each J ⊆ K only the *first* stage at which Hₙ ∪ J
has a short Berge cycle. At that stage retain the old edges of one such cycle.

The selected witnesses form a monotone finite core Cₙ ⊆ Hₙ, with
|Cₙ| ≤ g * 2^|K| uniformly in the number of stages, such that every
candidate subfamily has exactly the same girth-g outcome over Cₙ and Hₙ.

This is a coherent geometric witness schedule. It does NOT bound the
ancestral parameter depth of the retained edge births or construct a
carrier-faithful free-successor evaluation.
-/

namespace StructuralRamsey.Girth

universe v

/-- Some stage not later than N produces a short cycle after attaching J. -/
def EverBadBatch {W : Type v}
    (H : ℕ → Set (Set W)) (J : Finset (Set W)) (g N : ℕ) : Prop :=
  ∃ t : ℕ, t ≤ N ∧ HasBergeCycleAtMost (H t ∪ (↑J : Set (Set W))) g

/-- Old cycle witness selected at its first bad stage, available
from that stage onwards and absent at earlier stages. -/
noncomputable def firstBadCycleOldEdgesAt {W : Type v}
    (H : ℕ → Set (Set W)) (J : Finset (Set W))
    (g N n : ℕ) : Finset (Set W) := by
  classical
  exact if h : EverBadBatch H J g N then
    if Nat.find h ≤ n then
      oldShortCycleWitnessEdges (H (Nat.find h)) J g
    else ∅
  else ∅

/-- Every retained witness edge was already present at the stage
where it is used. -/
theorem firstBadCycleOldEdgesAt_subset {W : Type v}
    (H : ℕ → Set (Set W)) (J : Finset (Set W)) (g N n : ℕ)
    (hMono : ∀ a b, a ≤ b → H a ⊆ H b) :
    (↑(firstBadCycleOldEdgesAt H J g N n) : Set (Set W)) ⊆ H n := by
  classical
  intro e he
  unfold firstBadCycleOldEdgesAt at he
  split_ifs at he with hEver hStage
  · have hOld : e ∈ H (Nat.find hEver) :=
      oldShortCycleWitnessEdges_subset (H (Nat.find hEver)) J g he
    exact hMono (Nat.find hEver) n hStage hOld
  · simpa using he
  · simpa using he

/-- Once a first-bad witness is retained, it stays in the core. -/
theorem firstBadCycleOldEdgesAt_mono {W : Type v}
    (H : ℕ → Set (Set W)) (J : Finset (Set W)) (g N n n' : ℕ)
    (hn : n ≤ n') :
    firstBadCycleOldEdgesAt H J g N n ⊆
      firstBadCycleOldEdgesAt H J g N n' := by
  classical
  intro e he
  by_cases hEver : EverBadBatch H J g N
  · by_cases hStage : Nat.find hEver ≤ n
    · have hStage' : Nat.find hEver ≤ n' := hStage.trans hn
      simpa [firstBadCycleOldEdgesAt, hEver, hStage, hStage'] using he
    · have hFalse : False := by
        simpa [firstBadCycleOldEdgesAt, hEver, hStage] using he
      exact hFalse.elim
  · have hFalse : False := by
      simpa [firstBadCycleOldEdgesAt, hEver] using he
    exact hFalse.elim

/-- A first-bad witness uses at most g old edges. -/
theorem firstBadCycleOldEdgesAt_card_le {W : Type v}
    (H : ℕ → Set (Set W)) (J : Finset (Set W)) (g N n : ℕ) :
    (firstBadCycleOldEdgesAt H J g N n).card ≤ g := by
  classical
  unfold firstBadCycleOldEdgesAt
  split_ifs with hEver hStage
  · exact oldShortCycleWitnessEdges_card_le (H (Nat.find hEver)) J g
  · simp
  · simp

/-- The joint coherent core, retaining first-bad witnesses for all
subfamilies of the same finite candidate batch. -/
noncomputable def coherentBatchCycleCore {W : Type v}
    (H : ℕ → Set (Set W)) (K : Finset (Set W))
    (g N n : ℕ) : Finset (Set W) := by
  classical
  exact K.powerset.biUnion (fun J => firstBadCycleOldEdgesAt H J g N n)

/-- Each stage's coherent core is contained in the ambient host. -/
theorem coherentBatchCycleCore_subset {W : Type v}
    (H : ℕ → Set (Set W)) (K : Finset (Set W))
    (g N n : ℕ) (hMono : ∀ a b, a ≤ b → H a ⊆ H b) :
    (↑(coherentBatchCycleCore H K g N n) : Set (Set W)) ⊆ H n := by
  classical
  intro e he
  change e ∈ coherentBatchCycleCore H K g N n at he
  unfold coherentBatchCycleCore at he
  obtain ⟨J, _, heJ⟩ := Finset.mem_biUnion.mp he
  exact firstBadCycleOldEdgesAt_subset H J g N n hMono heJ

/-- The same chosen cycle witnesses are retained monotonically
through the entire increasing history. -/
theorem coherentBatchCycleCore_mono {W : Type v}
    (H : ℕ → Set (Set W)) (K : Finset (Set W))
    (g N n n' : ℕ) (hn : n ≤ n') :
    coherentBatchCycleCore H K g N n ⊆
      coherentBatchCycleCore H K g N n' := by
  classical
  intro e he
  change e ∈ coherentBatchCycleCore H K g N n at he
  change e ∈ coherentBatchCycleCore H K g N n'
  unfold coherentBatchCycleCore at he ⊢
  obtain ⟨J, hJ, heJ⟩ := Finset.mem_biUnion.mp he
  exact Finset.mem_biUnion.mpr
    ⟨J, hJ, firstBadCycleOldEdgesAt_mono H J g N n n' hn heJ⟩

/-- The old-cycle witness core is uniformly bounded independently
of the number N of history steps. -/
theorem coherentBatchCycleCore_card_le {W : Type v}
    (H : ℕ → Set (Set W)) (K : Finset (Set W))
    (g N n : ℕ) :
    (coherentBatchCycleCore H K g N n).card ≤ g * 2 ^ K.card := by
  classical
  calc
    (coherentBatchCycleCore H K g N n).card ≤
        ∑ J ∈ K.powerset,
          (firstBadCycleOldEdgesAt H J g N n).card := by
      exact Finset.card_biUnion_le
    _ ≤ ∑ _J ∈ K.powerset, g := by
      apply Finset.sum_le_sum
      intro J _
      exact firstBadCycleOldEdgesAt_card_le H J g N n
    _ = g * 2 ^ K.card := by
      simp [Finset.card_powerset, mul_comm]

/-- At any stage n ≤ N, a bad subfamily has reached its own first-bad
stage. Hence its chosen entire cycle is visible in the current core. -/
theorem coherentBatchCycleCore_girth_iff {W : Type v}
    (H : ℕ → Set (Set W)) (K J : Finset (Set W))
    (g N n : ℕ)
    (hMono : ∀ a b, a ≤ b → H a ⊆ H b)
    (hn : n ≤ N) (hJK : J ⊆ K) :
    GirthGT (H n ∪ (↑J : Set (Set W))) g ↔
      GirthGT
        ((↑(coherentBatchCycleCore H K g N n) : Set (Set W)) ∪
          (↑J : Set (Set W))) g := by
  classical
  have hCoreSub : (↑(coherentBatchCycleCore H K g N n) :
      Set (Set W)) ⊆ H n :=
    coherentBatchCycleCore_subset H K g N n hMono
  constructor
  · intro hOldGirth
    apply girthGT_of_subset
      (H := (↑(coherentBatchCycleCore H K g N n) : Set (Set W)) ∪
        (↑J : Set (Set W)))
      (K := H n ∪ (↑J : Set (Set W)))
    · intro e he
      rcases he with hCore | hJ
      · exact Or.inl (hCoreSub hCore)
      · exact Or.inr hJ
    · exact hOldGirth
  · intro hCoreGirth hBad
    have hEver : EverBadBatch H J g N := ⟨n, hn, hBad⟩
    have hFirst : Nat.find hEver ≤ n :=
      Nat.find_min' hEver ⟨hn, hBad⟩
    have hFirstBad :
        HasBergeCycleAtMost
          (H (Nat.find hEver) ∪ (↑J : Set (Set W))) g :=
      (Nat.find_spec hEver).2
    obtain ⟨c, hc, hEdges⟩ :=
      oldShortCycleWitnessEdges_covers
        (H (Nat.find hEver)) J g hFirstBad
    have hJIn : J ∈ K.powerset := Finset.mem_powerset.mpr hJK
    have hWitnessSub :
        (↑(oldShortCycleWitnessEdges (H (Nat.find hEver)) J g) :
          Set (Set W)) ⊆
        (↑(coherentBatchCycleCore H K g N n) : Set (Set W)) := by
      intro e he
      change e ∈ coherentBatchCycleCore H K g N n
      unfold coherentBatchCycleCore
      apply Finset.mem_biUnion.mpr
      refine ⟨J, hJIn, ?_⟩
      change e ∈ firstBadCycleOldEdgesAt H J g N n
      simpa [firstBadCycleOldEdgesAt, hEver, hFirst] using he
    have hCovered (i : Fin c.length) :
        c.edge i ∈
          (↑(coherentBatchCycleCore H K g N n) : Set (Set W)) ∪
            (↑J : Set (Set W)) := by
      rcases hEdges i with he | he
      · exact Or.inl (hWitnessSub he)
      · exact Or.inr he
    exact hCoreGirth ⟨c.ofEdgeMem hCovered, hc⟩

end StructuralRamsey.Girth
