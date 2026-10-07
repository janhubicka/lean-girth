import Girth.ForestObservableProfile
import SuccessorTree.FreeAncestral
import Mathlib.Tactic

/-!
# Rigidity of ancestral parameter spines

This tests the bounded-envelope step proposed for the girth-five
successor-tree proof.  Bounded parameter *arity* by itself gives no
bound on the depth of a parameter-closed spine: for arity one, the
transition on level n > 0 can refer to the ancestor on level n-1.

The numerical theorem proves that a strictly increasing shape-level
map cannot skip a level if every nonroot source level must have
its immediate predecessor level in the image of an earlier level.
The concrete codes below exhibit the parameter-spine pattern inside
the free ancestral syntax.

It does NOT assert a geometric evaluation of girth histories.
-/

namespace StructuralRamsey.Girth

open SuccessorTree.FreeAncestral

/-- Strictly increasing image levels have no gaps if every nonroot level
requires the preceding target level as an already mapped parameter. -/
theorem predecessorParameterSpine_rigid
    (f : ℕ → ℕ)
    (hf : StrictMono f)
    (hroot : f 0 = 0)
    (hprev :
      ∀ i : ℕ, 0 < i →
        ∃ j : ℕ, j < i ∧ f j + 1 = f i) :
    ∀ i : ℕ, f i = i := by
  intro i
  induction i using Nat.strong_induction_on with
  | h i ih =>
    cases i with
    | zero => exact hroot
    | succ k =>
        obtain ⟨j, hj, hstep⟩ := hprev (k + 1) (by omega)
        have hjval : f j = j := ih j (by omega)
        have hkval : f k = k := ih k (by omega)
        have hmono : f k < f (k + 1) :=
          hf (by omega)
        omega

/-- A marked endpoint of source level k therefore cannot be stretched
to a larger target level if the predecessor-parameter constraint
holds along the entire parameter spine. -/
theorem predecessorParameterSpine_endpoint
    (f : ℕ → ℕ)
    (hf : StrictMono f)
    (hroot : f 0 = 0)
    (hprev :
      ∀ i : ℕ, 0 < i →
        ∃ j : ℕ, j < i ∧ f j + 1 = f i)
    (k N : ℕ)
    (hend : f k = N) :
    N = k := by
  rw [← hend]
  exact predecessorParameterSpine_rigid f hf hroot hprev k

/-- An explicit arity-one code with a single parameter pointing to
the level immediately below the base, for every positive base level.
The initial root step necessarily has no parameters. -/
def predecessorSpineCode :
    (n : ℕ) → Code Unit 1 n
  | 0 =>
      { label := ()
        params :=
          { len := ⟨0, by decide⟩
            value := Fin.elim0 } }
  | n + 1 =>
      { label := ()
        params :=
          { len := ⟨1, by decide⟩
            value := fun _ => ⟨n, by omega⟩ } }

/-- The free ancestral history made by iterating these legal codes. -/
def predecessorSpineHistory :
    (n : ℕ) → History Unit 1 n
  | 0 => History.root
  | n + 1 =>
      History.step (predecessorSpineHistory n)
        (predecessorSpineCode n)

@[simp] theorem predecessorSpineCode_root_len :
    (predecessorSpineCode 0).params.len.val = 0 := rfl

@[simp] theorem predecessorSpineCode_succ_len (n : ℕ) :
    (predecessorSpineCode (n + 1)).params.len.val = 1 := rfl

theorem predecessorSpineCode_succ_parameter (n : ℕ)
    (j : Fin (predecessorSpineCode (n + 1)).params.len.val) :
    ((predecessorSpineCode (n + 1)).params.value j).val = n := rfl

/-- Closure of a finite active-level set under predecessor marking
costs at most one extra marked level per active event. -/
def forestDiarySkeleton
    (active meets : Finset ℕ) : Finset ℕ :=
  insert 0 ((active ∪ active.image Nat.pred) ∪ meets)

theorem forestDiarySkeleton_card_le
    (active meets : Finset ℕ) :
    (forestDiarySkeleton active meets).card ≤
      1 + 2 * active.card + meets.card := by
  classical
  unfold forestDiarySkeleton
  have hi :
      (insert 0 ((active ∪ active.image Nat.pred) ∪ meets)).card ≤
        ((active ∪ active.image Nat.pred) ∪ meets).card + 1 :=
    Finset.card_insert_le _ _
  have hu :
      ((active ∪ active.image Nat.pred) ∪ meets).card ≤
        (active ∪ active.image Nat.pred).card + meets.card :=
    Finset.card_union_le _ _
  have hv :
      (active ∪ active.image Nat.pred).card ≤
        active.card + (active.image Nat.pred).card :=
    Finset.card_union_le _ _
  have hw : (active.image Nat.pred).card ≤ active.card :=
    Finset.card_image_le
  omega

/-- If at most q*d active support events and s additional marked
meet/terminal levels are retained, the level skeleton is bounded
independently of the ambient history length. The missing application
condition is that all active-event parameters really refer to these
selected support levels, while all omitted events are neutral. -/
theorem forestDiarySkeleton_bound
    (active meets : Finset ℕ)
    (q d s : ℕ)
    (ha : active.card ≤ q * d)
    (hm : meets.card ≤ s) :
    (forestDiarySkeleton active meets).card ≤
      1 + 2 * (q * d) + s := by
  have hb := forestDiarySkeleton_card_le active meets
  omega

end StructuralRamsey.Girth
