import Girth.Berge
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Data.Fin.Tuple.Basic

/-! # Runs in a cyclic finite word

A mixed Berge cycle is controlled by the runs of edges lying on one side of
an amalgam.  This file isolates the elementary cyclic-index lemma used by both
singleton and common-edge gluings.
-/

namespace StructuralRamsey.Girth

/-- Our cyclic successor agrees with mathlib's canonical rotation of `Fin n`. -/
theorem cyclicSucc_eq_finRotate {n : ℕ} (i : Fin n) :
    cyclicSucc i = finRotate n i := by
  apply Fin.ext
  simp [cyclicSucc, finRotate_apply, Fin.add_def]

/-- Starting immediately after a change in a cyclic Boolean word, there is a
first later change before returning all the way around the circle.  Thus the
intervening positive-length block is constant. -/
theorem exists_first_cyclic_change
    {n : ℕ} (hn : 2 ≤ n) (side : Fin n → Bool) (before : Fin n)
    (hchange : side before ≠ side (finRotate n before)) :
    ∃ k : ℕ, 0 < k ∧ k < n ∧
      side (finCycle ⟨k, by omega⟩ (finRotate n before)) ≠
        side (finRotate n before) ∧
      ∀ m : ℕ, m < k →
        side (finCycle ⟨m, by omega⟩ (finRotate n before)) =
          side (finRotate n before) := by
  let start : Fin n := finRotate n before
  let p : Fin n → Prop := fun k => side (finCycle k start) ≠ side start
  letI : DecidablePred p := Classical.decPred p
  have hex : ∃ k : Fin n, p k := by
    refine ⟨-1, ?_⟩
    have hback : finCycle (-1 : Fin n) start = before := by
      dsimp [start]
      simp [finCycle_apply, finRotate_apply, add_assoc]
    rw [p, hback]
    exact hchange
  let k : Fin n := Fin.find p hex
  have hkSpec : p k := by
    exact Fin.find_spec hex
  have hkpos : 0 < k.1 := by
    by_contra hk
    have hk0 : k = 0 := Fin.ext (by omega)
    subst k
    simpa [p, start, finCycle_apply] using hkSpec
  refine ⟨k.1, hkpos, k.2, ?_, ?_⟩
  · exact hkSpec
  · intro m hm
    let mf : Fin n := ⟨m, lt_trans hm k.2⟩
    have hmf : mf < k := by
      exact hm
    have hnot : ¬ p mf := Fin.find_min hex hmf
    exact not_ne_iff.mp hnot

end StructuralRamsey.Girth
