import Girth.ForestObservableEventBound
import Mathlib.Tactic

/-!
# Bounded first agreements in a finite family of copy-owner histories

Trace q selected B-copies backwards through an iterated standard-picture
construction. At each generation n, the selected copies have owners
`owner n i`. A parent map identifies where each owner came from at
the next coarser generation. Thus two already coincident owners remain
coincident, while an *interesting owner event* is a first agreement of
two previously distinct owners.

Every such event strictly enlarges the equivalence relation of
same-owner pairs on q indices, so there are at most q² such events,
independently of construction depth. This is a useful genealogical
component of the bounded diary guard, not yet a proof of the entire
support-local parameter normalization or of geometric A/B evaluation.
-/

namespace StructuralRamsey.Girth

universe u

/-- The finite record of pairs of q marked copies which currently have
the same standard-picture owner. -/
noncomputable def ownerCoincidencePairs
    {Owner : Type u}
    (q : ℕ) (owner : Fin q → Owner) :
    Finset (Fin q × Fin q) := by
  classical
  exact (Finset.univ : Finset (Fin q × Fin q)).filter
    (fun ij => owner ij.1 = owner ij.2)

@[simp] theorem mem_ownerCoincidencePairs
    {Owner : Type u}
    (q : ℕ) (owner : Fin q → Owner)
    (ij : Fin q × Fin q) :
    ij ∈ ownerCoincidencePairs q owner ↔
      owner ij.1 = owner ij.2 := by
  classical
  simp [ownerCoincidencePairs]

/-- The equivalence relation of shared owners only grows when each
owner has a consistent parent in the preceding/coarser picture. -/
theorem ownerCoincidencePairs_mono
    (q : ℕ)
    (Owners : ℕ → Type u)
    (owner : (n : ℕ) → Fin q → Owners n)
    (parentOwner : (n : ℕ) → Owners n → Owners (n + 1))
    (hParent : ∀ (n : ℕ) (i : Fin q),
      owner (n + 1) i = parentOwner n (owner n i)) :
    ∀ n : ℕ,
      ownerCoincidencePairs q (owner n) ⊆
        ownerCoincidencePairs q (owner (n + 1)) := by
  intro n ij hij
  rw [mem_ownerCoincidencePairs] at hij ⊢
  rw [hParent n ij.1, hParent n ij.2]
  exact congrArg (parentOwner n) hij

/-- One new owner agreement makes a genuinely strict enlargement
of the finite pair record. -/
theorem ownerCoincidencePairs_strict_of_firstAgree
    (q : ℕ)
    (Owners : ℕ → Type u)
    (owner : (n : ℕ) → Fin q → Owners n)
    (parentOwner : (n : ℕ) → Owners n → Owners (n + 1))
    (hParent : ∀ (n : ℕ) (i : Fin q),
      owner (n + 1) i = parentOwner n (owner n i))
    (n : ℕ) (i j : Fin q)
    (hNew : owner (n + 1) i = owner (n + 1) j)
    (hOld : owner n i ≠ owner n j) :
    ownerCoincidencePairs q (owner n) ⊂
      ownerCoincidencePairs q (owner (n + 1)) := by
  have hSub :=
    ownerCoincidencePairs_mono q Owners owner parentOwner hParent n
  apply Finset.ssubset_iff_subset_ne.mpr
  refine ⟨hSub, ?_⟩
  intro heq
  have hMem :
      (i, j) ∈ ownerCoincidencePairs q (owner (n + 1)) :=
    (mem_ownerCoincidencePairs q (owner (n + 1)) (i, j)).2 hNew
  have hNot :
      (i, j) ∉ ownerCoincidencePairs q (owner n) := by
    simpa using hOld
  apply hNot
  rw [heq]
  exact hMem

/-- Even with arbitrarily deep standard-picture ancestry, no more
than q² steps can be selected as first agreements of old owners.
Other steps can be numerous and still need a neutral-recoding proof. -/
theorem firstOwnerAgreementEvents_bound
    (q N : ℕ)
    (Owners : ℕ → Type u)
    (owner : (n : ℕ) → Fin q → Owners n)
    (parentOwner : (n : ℕ) → Owners n → Owners (n + 1))
    (hParent : ∀ (n : ℕ) (i : Fin q),
      owner (n + 1) i = parentOwner n (owner n i))
    (interesting : ℕ → Prop) [DecidablePred interesting]
    (hNew : ∀ n : ℕ, n < N → interesting n →
      ∃ i j : Fin q,
        owner (n + 1) i = owner (n + 1) j ∧
          owner n i ≠ owner n j) :
    ((Finset.range N).filter interesting).card ≤ q * q := by
  have hMono :=
    ownerCoincidencePairs_mono q Owners owner parentOwner hParent
  have hStrict (n : ℕ) (hn : n < N)
      (hi : interesting n) :
      ownerCoincidencePairs q (owner n) ⊂
        ownerCoincidencePairs q (owner (n + 1)) := by
    obtain ⟨i, j, hNewPair, hOldPair⟩ := hNew n hn hi
    exact ownerCoincidencePairs_strict_of_firstAgree
      q Owners owner parentOwner hParent
      n i j hNewPair hOldPair
  have h :=
    activeRecordSteps_le
      (fun n => ownerCoincidencePairs q (owner n))
      interesting N (fun n _ => hMono n) hStrict
  simpa using h

end StructuralRamsey.Girth
