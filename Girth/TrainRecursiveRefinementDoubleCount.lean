import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

set_option autoImplicit false
set_option Elab.async false

/-!
# Track 6: elementary double-fibre counting

Candidate, NOT YET KERNEL-VALIDATED at this commit. Do not promote a
manuscript validation mark until a local build and strict axiom audit.
No new axioms, `sorry`, geometry, or global girth assumptions are used.

If every label of a finite function has two distinct preimages, select
two preimages per label. This gives an injection from `Bool × Label`
into the original finite domain, proving `2 * card Label ≤ n`.
The geometric proof that each USED child label has two occurrences
belongs in the follow-up module on genuine labelled Berge cycles.
-/

namespace StructuralRamsey.Girth

universe v

theorem card_double_le_of_two_preimages
    {n : ℕ} {Label : Type v} [Fintype Label]
    (f : Fin n → Label)
    (hTwo : ∀ u : Label, ∃ p : Fin n × Fin n,
      p.1 ≠ p.2 ∧ f p.1 = u ∧ f p.2 = u) :
    2 * Fintype.card Label ≤ n := by
  classical
  let choosePair (u : Label) : Fin n × Fin n := Classical.choose (hTwo u)
  have hPair (u : Label) :
      (choosePair u).1 ≠ (choosePair u).2 ∧
      f (choosePair u).1 = u ∧
      f (choosePair u).2 = u :=
    Classical.choose_spec (hTwo u)
  let picked : Bool × Label → Fin n
    | (false, u) => (choosePair u).1
    | (true, u) => (choosePair u).2
  have hPickedOwner : ∀ b : Bool × Label, f (picked b) = b.2 := by
    intro ⟨flag, u⟩
    cases flag with
    | false => exact (hPair u).2.1
    | true => exact (hPair u).2.2
  have hPickedInj : Function.Injective picked := by
    intro ⟨flag, u⟩ ⟨flag', u'⟩ heq
    have hu : u = u' := by
      calc
        u = f (picked (flag, u)) := (hPickedOwner (flag, u)).symm
        _ = f (picked (flag', u')) := congrArg f heq
        _ = u' := hPickedOwner (flag', u')
    subst u'
    cases flag <;> cases flag'
    · rfl
    · have bad : (choosePair u).1 = (choosePair u).2 := by
        simpa [picked] using heq
      exact ((hPair u).1 bad).elim
    · have bad : (choosePair u).2 = (choosePair u).1 := by
        simpa [picked] using heq
      exact ((hPair u).1 bad.symm).elim
    · rfl
  have bound := Fintype.card_le_of_injective picked hPickedInj
  simpa only [Fintype.card_prod, Fintype.card_bool, Fintype.card_fin] using bound

end StructuralRamsey.Girth

#print axioms StructuralRamsey.Girth.card_double_le_of_two_preimages
