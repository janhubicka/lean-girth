import Girth.TrainLongBoundaryCollision

/-!
# Circulation: the new wagon-connector A2 clause after a long insertion

A valid long piece e⁺ W f⁺ has two ORIGINAL vertex boundaries, has no
single ambient edge joining those boundaries, and introduces W as a fresh
wagon. A3 of the original acceptable cycle puts all vertex contacts of W
into a two-position window. Since the two boundaries are distinct
positions both in W, those are the ONLY contacts of W with the original
connector word.

This local result does not need an assumed globally legal replacement cycle,
output-wagon linearity, or an added strong inducedness hypothesis. Together
with the checked connector/label distinctness of #520, it supplies the
new-connector A2 clause needed when assembling long replacements.
-/

namespace StructuralRamsey.Girth.OrderOneData

universe v
variable {V E I P : Type v} (D : OrderOneData V E I P)

/-- The two boundaries of a long piece exhaust the original connector
positions belonging to its fresh wagon. This works even with two source
occurrences; it uses only A3, not a length-three restriction. -/
theorem BigCycle.fresh_wagon_contacts_of_longValid
    {n : ℕ} (C : D.BigCycle n) (hAccept : C.Acceptable)
    (k j : Fin n) (e f : E) (p : P)
    (hLong : C.LongValid D k j e p f)
    (hFresh : ∀ t : Fin n, C.connector t ≠ Sum.inr p) :
    ∀ t : Fin n, C.InWagonAt p t →
      t = trainCyclicPred j ∨ t = j := by
  obtain ⟨x, y, hPrev, hHere, _he, _hf, _hne,
    hep, hfp, hxe, hyf, _hNoPair⟩ := hLong
  have hP : C.InWagonAt p (trainCyclicPred j) :=
    ⟨x, hPrev, e, hep, hxe⟩
  have hJ : C.InWagonAt p j :=
    ⟨y, hHere, f, hfp, hyf⟩
  have hPJ : trainCyclicPred j ≠ j := by
    intro hEq
    have hs := cyclicSucc_trainCyclicPred_of_two_le C.length_ge_two j
    rw [hEq] at hs
    exact (C.ne_cyclicSucc D j) hs.symm
  obtain ⟨t₀, hWindow⟩ := hAccept.2.2 p hFresh
  intro t ht
  have hT := hWindow t ht
  have hP₀ := hWindow (trainCyclicPred j) hP
  have hJ₀ := hWindow j hJ
  rcases hP₀ with hP₀ | hP₀
  · rcases hJ₀ with hJ₀ | hJ₀
    · exact False.elim (hPJ (hP₀.trans hJ₀.symm))
    · rcases hT with hT | hT
      · exact Or.inl (hT.trans hP₀.symm)
      · exact Or.inr (hT.trans hJ₀.symm)
  · rcases hJ₀ with hJ₀ | hJ₀
    · rcases hT with hT | hT
      · exact Or.inr (hT.trans hJ₀.symm)
      · exact Or.inl (hT.trans hP₀.symm)
    · exact False.elim (hPJ (hP₀.trans hJ₀.symm))

/-- Physical pair-edge incidence is symmetric: the same edge witnesses
the reversed pair. -/
private theorem pairEdge_symm (x y : V)
    (h : D.PairEdge x y) : D.PairEdge y x := by
  obtain ⟨e, hx, hy⟩ := h
  exact ⟨e, hy, hx⟩

/-- The two distinct old vertex connectors of a fresh long wagon are
precisely the two long-piece boundary vertices; no ambient edge can
join them. This supplies the EXTRA no-common-edge half of A2 for a
fresh wagon connector, before any global word is constructed. -/
theorem BigCycle.fresh_wagon_no_pair_of_longValid
    {n : ℕ} (C : D.BigCycle n) (hAccept : C.Acceptable)
    (k j : Fin n) (e f : E) (p : P)
    (hLong : C.LongValid D k j e p f)
    (hFresh : ∀ t : Fin n, C.connector t ≠ Sum.inr p)
    (t u : Fin n) (htu : t ≠ u) (x y : V)
    (ht : C.connector t = Sum.inl x)
    (hu : C.connector u = Sum.inl y)
    (htW : C.InWagonAt p t) (huW : C.InWagonAt p u) :
    ¬ D.PairEdge x y := by
  have hT := C.fresh_wagon_contacts_of_longValid
    D hAccept k j e f p hLong hFresh t htW
  have hU := C.fresh_wagon_contacts_of_longValid
    D hAccept k j e f p hLong hFresh u huW
  obtain ⟨x₀, y₀, hPrev, hHere, _he, _hf, _hne,
    _hep, _hfp, _hxe, _hyf, hNoPair⟩ := hLong
  rcases hT with hT | hT
  · rcases hU with hU | hU
    · exact False.elim (htu (hT.trans hU.symm))
    · have hx₀ : x = x₀ := Sum.inl.inj
        (ht.symm.trans (by rw [hT]; exact hPrev))
      have hy₀ : y = y₀ := Sum.inl.inj
        (hu.symm.trans (by rw [hU]; exact hHere))
      rw [hx₀, hy₀]
      exact hNoPair
  · rcases hU with hU | hU
    · have hx₀ : x = y₀ := Sum.inl.inj
        (ht.symm.trans (by rw [hT]; exact hHere))
      have hy₀ : y = x₀ := Sum.inl.inj
        (hu.symm.trans (by rw [hU]; exact hPrev))
      intro hxy
      apply hNoPair
      exact D.pairEdge_symm y₀ x₀ (by simpa [hx₀, hy₀] using hxy)
    · exact False.elim (htu (hT.trans hU.symm))

end StructuralRamsey.Girth.OrderOneData
