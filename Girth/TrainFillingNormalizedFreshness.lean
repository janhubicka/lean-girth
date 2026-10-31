import Girth.TrainFillingMixedNormalization
import Girth.TrainFreshLocalSupreme

/-!
# Mixed normalization makes supreme-piece freshness automatic

If an existing wagon contains two adjacent vertex connectors, A2 forces
its predecessor and successor to be those connectors. Thus the cycle has
three positions. Mixed normalization makes both occurrences next to that
wagon physical edges, so the remaining occurrence is the ONLY possible
designated occurrence. A long replacement toward a DIFFERENT designated
label therefore cannot use an existing wagon.

This is a source-side statement. It does not use an old projection, an
old globally legal plan, or legality of the new output. The argument
handles both old-short-to-long and old-long lifts at once.
-/
namespace StructuralRamsey.Girth

private theorem length_three_of_third_successor {n : ℕ} (hn : 2 ≤ n)
    (i : Fin n) (h : cyclicSucc (cyclicSucc (cyclicSucc i)) = i) : n = 3 := by
  have hVal (j : Fin n) : (cyclicSucc j).val =
      if j.val + 1 < n then j.val + 1 else 0 := by
    change (j.val + 1) % n = _
    split_ifs with hj
    · exact Nat.mod_eq_of_lt hj
    · have hLast : j.val + 1 = n := by have := j.isLt; omega
      rw [hLast, Nat.mod_self]
  have hv := congrArg Fin.val h
  simp only [hVal] at hv
  have hi := i.isLt
  split_ifs at hv <;> omega

namespace OrderOneData
universe v
variable {V E I P : Type v} (D : OrderOneData V E I P)

/-- In a mixed-normalized cycle, a wagon containing both vertex
boundaries of an occurrence is absent whenever another designated label
occurs. No edge membership, no-pair condition or linearity is needed. -/
theorem BigCycle.wagon_fresh_of_mixedNormalized
    {n : ℕ} (C : D.BigCycle n) (hA2 : C.A2)
    (hNormal : C.MixedNormalized D)
    (k j : Fin n) (hk : D.designated (C.label k))
    (hNe : C.label j ≠ C.label k)
    (x y : V) (p : P)
    (hx : C.connector (trainCyclicPred j) = Sum.inl x)
    (hy : C.connector j = Sum.inl y)
    (hpx : D.WagonVertex p x) (hpy : D.WagonVertex p y) :
    ∀ i : Fin n, C.connector i ≠ Sum.inr p := by
  intro i hi
  have hPJ : trainCyclicPred j ≠ j := by
    intro h
    have hs := cyclicSucc_trainCyclicPred_of_two_le C.length_ge_two j
    rw [h] at hs
    exact (C.ne_cyclicSucc D j) hs.symm
  have hji : j ≠ i := by
    intro h
    have hbad : (Sum.inl y : V ⊕ P) = Sum.inr p :=
      hy.symm.trans (by rw [h]; exact hi)
    cases hbad
  have hLeft := hA2.1 i p hi (trainCyclicPred j) ⟨x, hx, hpx⟩
  have hRight := hA2.1 i p hi j ⟨y, hy, hpy⟩
  rcases hLeft with hLeft | hLeft
  · have hjEq : j = i := by
      have hs := congrArg cyclicSucc hLeft
      simpa only [cyclicSucc_trainCyclicPred_of_two_le C.length_ge_two] using hs
    exact hji hjEq
  · rcases hRight with hRight | hRight
    · have hjSS : j = cyclicSucc (cyclicSucc i) := by
        have hs := congrArg cyclicSucc hLeft
        simpa only [cyclicSucc_trainCyclicPred_of_two_le C.length_ge_two] using hs
      have hSuccJ : cyclicSucc j = i := by
        rw [hRight, cyclicSucc_trainCyclicPred_of_two_le C.length_ge_two]
      have hThird : cyclicSucc (cyclicSucc (cyclicSucc i)) = i := by
        rw [← hjSS]
        exact hSuccJ
      have hn := length_three_of_third_successor C.length_ge_two i hThird
      subst n
      have hCover : k = j ∨ k = i ∨ k = cyclicSucc i := by
        rw [hjSS]
        fin_cases i <;> fin_cases k <;> decide
      rcases hCover with hkj | hki | hks
      · exact hNe (congrArg C.label hkj.symm)
      · apply hNormal k hk
        rw [hki]
        refine ⟨y, p, hpy, Or.inl ⟨?_, hi⟩⟩
        rw [← hRight]
        exact hy
      · apply hNormal k hk
        rw [hks]
        refine ⟨x, p, hpx, Or.inr ⟨?_, ?_⟩⟩
        · rw [trainCyclicPred_cyclicSucc_of_two_le C.length_ge_two]
          exact hi
        · rw [← hLeft]
          exact hx
    · exact hPJ (hLeft.trans hRight.symm)

/-- The whole-source freshness required for a chosen long replacement
follows automatically after mixed normalization. -/
theorem BigCycle.longValid_fresh_of_mixedNormalized
    {n : ℕ} (C : D.BigCycle n) (hA2 : C.A2)
    (hNormal : C.MixedNormalized D)
    (k j : Fin n) (hk : D.designated (C.label k))
    (hNe : C.label j ≠ C.label k) (e f : E) (p : P)
    (hLong : C.LongValid D k j e p f) :
    ∀ i : Fin n, C.connector i ≠ Sum.inr p := by
  obtain ⟨x, y, hx, hy, _he, _hf, _hef, hep, hfp, hxe, hyf, _hPair⟩ := hLong
  exact C.wagon_fresh_of_mixedNormalized D hA2 hNormal k j hk hNe x y p hx hy
    ⟨e, hep, hxe⟩ ⟨f, hfp, hyf⟩

/-- On a mixed-normalized acceptable linear cycle, local supreme pieces
already assemble a globally legal supreme plan. The chosen designated
label and every original position are unchanged. -/
theorem BigCycle.hasSupremeAt_of_mixedNormalized_local
    {n : ℕ} (C : D.BigCycle n) (hAccept : C.Acceptable)
    (hLinear : D.LinearPretrain) (hNormal : C.MixedNormalized D)
    (k : Fin n) (hk : D.designated (C.label k))
    (hLocal : ∀ j : Fin n, C.label j ≠ C.label k →
      D.ShortPiece (C.label k) (C.connector (trainCyclicPred j)) (C.connector j) ∨
      D.LongPiece (C.label k) (C.connector (trainCyclicPred j)) (C.connector j)) :
    C.HasSupremeAt D k := by
  apply C.hasSupremeAt_of_fresh_local_witnesses D hAccept hLinear k hk
  intro j hNe
  rcases hLocal j hNe with hs | hl
  · exact Or.inl hs
  · obtain ⟨x, y, p, e, f, hx, hy, he, hf, hef, hep, hfp, hxe, hyf, hPair⟩ := hl
    have hLong : C.LongValid D k j e p f :=
      ⟨x, y, hx, hy, he, hf, hef, hep, hfp, hxe, hyf, hPair⟩
    exact Or.inr ⟨e, f, p, hLong,
      C.longValid_fresh_of_mixedNormalized D hAccept.2.1 hNormal k j hk hNe e f p hLong⟩
end OrderOneData
end StructuralRamsey.Girth
