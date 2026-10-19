import Girth.TrainBigCycleOrderOneExtraction
import Mathlib.Tactic

/-!
# Circulation: minimize cyclic segment owners with nonunique shared-edge provenance

A literal output cycle has finitely many occurrence positions, but
a shared physical edge can admit several legitimate standard-segment
assignments. Choosing a fixed canonical CORE tag before minimizing
could increase the number of segments. We therefore minimize among
ALL occurrence-wise admissible assignments.

The owner type may be infinite. Only the number of cyclic changes,
a natural number bounded by the number of occurrences, is minimized.
This gives a well-defined minimum and an admissible attaining it
without assuming finiteness of the owner family.

For the actual picture step, an owner will be a standard index or
one singleton core-edge label, with membership in the relevant label
or edge carrier forming the admissibility relation. Constructing
those geometric predicates, actual segment blocks, and the legal
witness reduct remains separate. No appendix results are used.
-/

namespace StructuralRamsey.Girth

universe v
variable {Owner : Type v} {n : ℕ}

/-- Number of boundaries in a cyclic owner assignment where the
owner of the next occurrence differs. For two or more blocks, this
is the number of maximal cyclic constant-owner segments. -/
noncomputable def cyclicOwnerChanges (owner : Fin n → Owner) : ℕ := by
  classical
  exact (Finset.univ.filter
    (fun i : Fin n => owner i ≠ owner (cyclicSucc i))).card

/-- Zero changes means the owner is constant along EVERY cyclic
successor edge. This is the one-segment alternative, without a
premature claim that a chosen source is unique. -/
theorem cyclicOwnerChanges_eq_zero_iff
    (owner : Fin n → Owner) :
    cyclicOwnerChanges owner = 0 ↔
      ∀ i : Fin n, owner i = owner (cyclicSucc i) := by
  classical
  constructor
  · intro h i
    have hEmpty :
        (Finset.univ.filter
          (fun j : Fin n => owner j ≠ owner (cyclicSucc j))) = ∅ :=
      Finset.card_eq_zero.mp (by
        simpa [cyclicOwnerChanges] using h)
    by_contra hne
    have hmem : i ∈ Finset.univ.filter
        (fun j : Fin n => owner j ≠ owner (cyclicSucc j)) := by
      simp [hne]
    rw [hEmpty] at hmem
    simpa using hmem
  · intro h
    have hEmpty :
        (Finset.univ.filter
          (fun j : Fin n => owner j ≠ owner (cyclicSucc j))) = ∅ := by
      apply Finset.eq_empty_iff_forall_not_mem.mpr
      intro i hi
      exact (Finset.mem_filter.mp hi).2 (h i)
    change (Finset.univ.filter
      (fun j : Fin n => owner j ≠ owner (cyclicSucc j))).card = 0
    rw [hEmpty]
    rfl

/-- From arbitrary nonempty individual admissibility sets, there
exists a globally admissible assignment with the LEAST POSSIBLE
number of cyclic owner changes. No finite Owner assumption. -/
theorem exists_minimal_cyclic_owner
    (allowed : Fin n → Owner → Prop)
    (hNonempty : ∀ i : Fin n, ∃ owner : Owner, allowed i owner) :
    ∃ choice : Fin n → Owner,
      (∀ i : Fin n, allowed i (choice i)) ∧
      (∀ other : Fin n → Owner,
        (∀ i : Fin n, allowed i (other i)) →
        cyclicOwnerChanges choice ≤ cyclicOwnerChanges other) := by
  classical
  let initial : Fin n → Owner := fun i => Classical.choose (hNonempty i)
  have hInitial : ∀ i : Fin n, allowed i (initial i) := by
    intro i
    exact Classical.choose_spec (hNonempty i)
  let P : ℕ → Prop := fun k =>
    ∃ choice : Fin n → Owner,
      (∀ i : Fin n, allowed i (choice i)) ∧
      cyclicOwnerChanges choice = k
  have hExists : ∃ k : ℕ, P k :=
    ⟨cyclicOwnerChanges initial, initial, hInitial, rfl⟩
  obtain ⟨choice, hAllowed, hCount⟩ := Nat.find_spec hExists
  refine ⟨choice, hAllowed, ?_⟩
  intro other hOther
  have hOtherWitness : P (cyclicOwnerChanges other) :=
    ⟨other, hOther, rfl⟩
  calc
    cyclicOwnerChanges choice = Nat.find hExists := hCount
    _ ≤ cyclicOwnerChanges other :=
      Nat.find_min' hExists hOtherWitness

end StructuralRamsey.Girth
