import Girth.ContactRefinementBudgets
import Girth.ContactRecursiveRank

/-! Numerical interface between finite cut functions and the manuscript's
multiplicity induction on lists. The value at the universal top is
never counted. In particular the refined boost's LARGE bottom budget
is removed before the rank of its shorter call is calculated. -/

namespace StructuralRamsey.Girth

/-- List of proper cutoff values, omitting the universal top. -/
def contactCutoffs {m : ℕ} (q : Fin (m+1) → ℕ) : List ℕ :=
  List.ofFn (fun i : Fin m => q i.castSucc)

/-- The shorter vector, including an irrelevant top entry. The minimum
makes the function total also at height zero, where it is never used. -/
def contactTailBounds {m : ℕ} (q : Fin (m+1) → ℕ) :
    Fin (m-1+1) → ℕ :=
  fun i => q ⟨min (i.val+1) m, Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩

theorem contactTailBounds_at {m : ℕ} (q : Fin (m+1) → ℕ)
    (hm : 0 < m) (i : Fin (m-1+1)) :
    contactTailBounds q i = q ⟨i.val+1,by have := i.isLt; omega⟩ := by
  unfold contactTailBounds
  apply congrArg q
  apply Fin.ext
  change min (i.val+1) m = i.val+1
  have hi := i.isLt
  omega

theorem contactTailBounds_succ {h : ℕ} (q : Fin (h+2) → ℕ) :
    contactTailBounds q = (fun i : Fin (h+1) => q i.succ) := by
  funext i
  exact contactTailBounds_at q (by omega) i

theorem contactCutoffs_length {m : ℕ} (q : Fin (m+1) → ℕ) :
    (contactCutoffs q).length = m := List.length_ofFn

theorem contactCutoffs_get {m : ℕ} (q : Fin (m+1) → ℕ)
    (i : ℕ) (hi : i < (contactCutoffs q).length) :
    (contactCutoffs q)[i] = q ⟨i,by rw [contactCutoffs_length] at hi; omega⟩ := by
  exact List.getElem_ofFn (f := fun j : Fin m => q j.castSucc)
    (show i < (List.ofFn (fun j : Fin m => q j.castSucc)).length from hi)

theorem contactCutoffs_cons {h : ℕ} (q : Fin (h+2) → ℕ) :
    contactCutoffs q = q 0 :: contactCutoffs (contactTailBounds q) := by
  rw [contactTailBounds_succ]
  unfold contactCutoffs
  rw [List.ofFn_succ] <;> rfl

/-- All proper bounds lie in the fixed finite rank alphabet and
are nondecreasing. The value at the top is unconstrained. -/
def ContactRankOK (M : ℕ) {m : ℕ} (q : Fin (m+1) → ℕ) : Prop :=
  (∀ i, i.val < m → 2 ≤ q i ∧ q i ≤ M) ∧
  (∀ i j, i.val ≤ j.val → j.val < m → q i ≤ q j)

theorem contactTailBounds_rankOK {m M : ℕ} (q : Fin (m+1) → ℕ)
    (hm : 0 < m) (h : ContactRankOK M q) :
    ContactRankOK M (contactTailBounds q) := by
  constructor
  · intro i hi
    rw [contactTailBounds_at q hm]
    exact h.1 _ (by change i.val+1 < m; omega)
  · intro i j hij hj
    rw [contactTailBounds_at q hm,contactTailBounds_at q hm]
    exact h.2 _ _ (by change i.val+1 ≤ j.val+1; omega)
      (by change j.val+1 < m; omega)

theorem contactTailBounds_rankDecrease_two {h M : ℕ}
    (q : Fin (h+2) → ℕ) (hOK : ContactRankOK M q) (hq : q 0 = 2) :
    TrainCountLex M (contactCutoffs (contactTailBounds q)) (contactCutoffs q) := by
  have hM := (hOK.1 0 (by change (0 : ℕ) < h+1; omega)).2
  rw [contactCutoffs_cons q,hq]
  exact contact_cutoffTwo_rankDecrease M _ (by omega)

universe v
namespace ContactBaseProjection.StripRefinement
variable {V E I X B : Type v} {h : ℕ}
variable {D : ContactHypergraphData V E I} {base : B → Set X}
variable {P : ContactBaseProjection D base} {T : ContactTrainData E (h+1)}
variable {allowed : Fin (h+1) → Set X} {g : ℕ} {b : B}
variable (R : P.StripRefinement T allowed g b)

/-- A proper entry of the shorter refined vector is either an
inserted positive prefix cutoff, or the corresponding old positive
cutoff. There is no occurrence of the original bottom budget here. -/
theorem shorter_refined_at (q : Fin (h+2) → ℕ)
    (i : Fin (R.depth+h-1+1)) (hi : i.val < R.depth+h-1) :
    contactTailBounds (R.boostBounds q) i =
      if i.val+1 < R.depth then g
      else q ⟨i.val+1-R.depth+1,by omega⟩ := by
  have hd := R.depth_pos
  rw [contactTailBounds_at _ (by omega)]
  change R.boostBounds q ⟨i.val+1,by omega⟩ = _
  rw [boostBounds,if_neg (by change i.val+1 ≠ 0; omega)]
  rfl

/-- EXACT list of recursive cutoff requests: d-1 inserted entries,
then the old positive proper vector. The d=1 case has empty prefix. -/
theorem shorter_refined_cutoffs (q : Fin (h+2) → ℕ) :
    contactCutoffs (contactTailBounds (R.boostBounds q)) =
      List.replicate (R.depth-1) g ++ contactCutoffs (contactTailBounds q) := by
  have hd := R.depth_pos
  apply List.ext_getElem
  · rw [contactCutoffs_length,List.length_append,List.length_replicate,contactCutoffs_length]
    omega
  · intro i hL hR
    have hi : i < R.depth+h-1 := by
      rw [contactCutoffs_length] at hL
      exact hL
    rw [contactCutoffs_get]
    have he := R.shorter_refined_at q
      ⟨i,by omega⟩ (by exact hi)
    rw [he]
    change (if i+1 < R.depth then g else q ⟨i+1-R.depth+1,by omega⟩) =
      (List.replicate (R.depth-1) g ++ contactCutoffs (contactTailBounds q))[i]'hR
    by_cases hs : i < R.depth-1
    · rw [if_pos (show i+1 < R.depth by omega)]
      have hrep : i < (List.replicate (R.depth-1) g).length := by
        simpa only [List.length_replicate] using hs
      exact ((List.getElem_append_left hrep).trans (List.getElem_replicate hrep)).symm
    · rw [if_neg (show ¬ i+1 < R.depth by omega)]
      have hrep : (List.replicate (R.depth-1) g).length ≤ i := by
        simpa only [List.length_replicate] using Nat.le_of_not_gt hs
      have ht : i - (List.replicate (R.depth-1) g).length <
          (contactCutoffs (contactTailBounds q)).length := by
        rw [List.length_append] at hR
        omega
      calc
        q ⟨i+1-R.depth+1,by omega⟩ =
          contactTailBounds q ⟨i-(List.replicate (R.depth-1) g).length,
            by rw [contactCutoffs_length] at ht; omega⟩ := by
          rw [contactTailBounds_at _ (by omega)]
          apply congrArg q
          apply Fin.ext
          change i+1-R.depth+1 = i-(List.replicate (R.depth-1) g).length+1
          simp only [List.length_replicate]
          omega
        _ = (contactCutoffs (contactTailBounds q))[i-(List.replicate (R.depth-1) g).length]'ht :=
          (contactCutoffs_get _ _ ht).symm
        _ = _ := (List.getElem_append_right hrep).symm

/-- The lower-rank vector is still nondecreasing in its proper cuts.
This statement deliberately does not assert monotonicity of the
refined BOOST vector with its larger first coordinate. -/
theorem shorter_refined_rankOK (M : ℕ) (q : Fin (h+2) → ℕ)
    (hOK : ContactRankOK M q) (hg : 2 ≤ g) (hgq : g ≤ q 0) :
    ContactRankOK M (contactTailBounds (R.boostBounds q)) := by
  have hd := R.depth_pos
  have hq0 := hOK.1 0 (by change (0 : ℕ) < h+1; omega)
  constructor
  · intro i hi
    rw [R.shorter_refined_at q i hi]
    split
    · exact ⟨hg,hgq.trans hq0.2⟩
    · exact hOK.1 _ (by change i.val+1-R.depth+1 < h+1; omega)
  · intro i j hij hj
    have hi : i.val < R.depth+h-1 := hij.trans_lt hj
    rw [R.shorter_refined_at q i hi,R.shorter_refined_at q j hj]
    by_cases hI : i.val+1 < R.depth
    · rw [if_pos hI]
      by_cases hJ : j.val+1 < R.depth
      · simp only [if_pos hJ, le_refl]
      · rw [if_neg hJ]
        apply hgq.trans
        exact hOK.2 0 _ (by change (0 : ℕ) ≤ j.val+1-R.depth+1; omega)
          (by change j.val+1-R.depth+1 < h+1; omega)
    · have hJ : ¬ j.val+1 < R.depth := by omega
      rw [if_neg hI,if_neg hJ]
      exact hOK.2 _ _
        (by change i.val+1-R.depth+1 ≤ j.val+1-R.depth+1; omega)
        (by change j.val+1-R.depth+1 < h+1; omega)

theorem shorter_refined_rankDecrease (M : ℕ) (q : Fin (h+2) → ℕ)
    (hOK : ContactRankOK M q) (hq : 2 < q 0)
    (hg : g = contactRefinementCutoff (q 0)) :
    TrainCountLex M (contactCutoffs (contactTailBounds (R.boostBounds q)))
      (contactCutoffs q) := by
  rw [R.shorter_refined_cutoffs q,contactCutoffs_cons q]
  have he := congrArg (fun k => List.replicate (R.depth-1) k ++
    contactCutoffs (contactTailBounds q)) hg
  rw [he]
  exact contact_refinement_rankDecrease M (q 0) R.depth _
    hq (hOK.1 0 (by change (0 : ℕ) < h+1; omega)).2

end ContactBaseProjection.StripRefinement
end StructuralRamsey.Girth
