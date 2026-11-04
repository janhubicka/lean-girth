import Girth.TrainTwoConsecutiveShortLiteralLabels
import Girth.TrainActualCycleDesignatedRank
import Mathlib.Tactic

/-!
# Path A: exact designated occurrence loss in a two-short replacement

The two-short replacement never introduces a designated label and
changes exactly the two original occurrence labels to physical edges.
The designated-occurrence count therefore never increases. It
decreases STRICTLY if at least one of those two original labels was
designated, independently of the chosen receiving standard.

The proof uses literal Fin-index labels, not an assumed source/target
designated-copy identification. The remaining physical/physical
equal-count case is explicit and is NOT resolved by this lemma.
Circulation only; no appendix or manuscript markers.
-/

namespace StructuralRamsey.Girth

universe v
variable {I E : Type v}

/-- Numeric indicator of an ACTUALLY designated occurrence label. -/
def designatedLabelIndicator : I ⊕ E → ℕ
  | .inl _ => 1
  | .inr _ => 0

/-- Convert the previously checked literal designated-label count
to a sum of its 0/1 occurrence indicators. -/
theorem designatedLabelCount_eq_indicatorSum
    (l : List (I ⊕ E)) :
    designatedLabelCount l = (l.map designatedLabelIndicator).sum := by
  classical
  induction l with
  | nil =>
      simp [designatedLabelCount]
  | cons h t ih =>
      cases h with
      | inl i =>
          have hStep :
              designatedLabelCount (Sum.inl i :: t) =
                designatedLabelCount t + 1 := by
            simp [designatedLabelCount]
          rw [hStep, ih]
          simp [designatedLabelIndicator, Nat.add_comm]
      | inr e =>
          have hStep :
              designatedLabelCount (Sum.inr e :: t) =
                designatedLabelCount t := by
            simp [designatedLabelCount]
          rw [hStep, ih]
          simp [designatedLabelIndicator]

/-- The labeled BigCycle's designated count is the Finset sum of
its position-wise 0/1 indicator; repeated designated names are
correctly counted at their different occurrence positions. -/
theorem designatedLabelCount_ofFn_eq_indicatorFinset
    {n : ℕ} (labels : Fin n → I ⊕ E) :
    designatedLabelCount (List.ofFn labels) =
      ∑ j : Fin n, designatedLabelIndicator (labels j) := by
  calc
    designatedLabelCount (List.ofFn labels) =
        ((List.ofFn labels).map designatedLabelIndicator).sum :=
      designatedLabelCount_eq_indicatorSum _
    _ = (List.ofFn (fun j : Fin n =>
          designatedLabelIndicator (labels j))).sum := by
      rw [List.ofFn_comp' labels designatedLabelIndicator]
    _ = ∑ j : Fin n, designatedLabelIndicator (labels j) := by
      simp only [List.sum_ofFn]

namespace OrderOneData

variable {V P : Type v} (D : OrderOneData V E I P)

/-- Pointwise, the exact two-short label word has no more
designated mass at any occurrence than the original label word. -/
private theorem BigCycle.twoShort_indicator_pointwise_le
    {n : ℕ} (K H : D.BigCycle n)
    (t : Fin n) (first second : E)
    (hLabels : ∀ j : Fin n,
      H.label j = K.twoConsecutiveShortLabels D t first second j)
    (j : Fin n) :
    designatedLabelIndicator (H.label j) ≤
      designatedLabelIndicator (K.label j) := by
  rw [hLabels j]
  by_cases hJt : j = t
  · subst j
    simp [BigCycle.twoConsecutiveShortLabels, designatedLabelIndicator]
  · by_cases hJs : j = cyclicSucc t
    · subst j
      have hNe : cyclicSucc t ≠ t :=
        cyclicSucc_ne_self_of_two_le K.length_ge_two t
      simp [BigCycle.twoConsecutiveShortLabels,
        designatedLabelIndicator, hNe]
    · simp [BigCycle.twoConsecutiveShortLabels, hJt, hJs]

/-- The two-short output never has more designated occurrences than
the source; this holds even when both replaced source labels were
already physical and hence there is no strict loss. -/
theorem BigCycle.twoConsecutiveShort_designatedCount_le
    {n : ℕ} (K H : D.BigCycle n)
    (t : Fin n) (first second : E)
    (hLabels : ∀ j : Fin n,
      H.label j = K.twoConsecutiveShortLabels D t first second j) :
    H.designatedOccurrenceCount D ≤
      K.designatedOccurrenceCount D := by
  change designatedLabelCount (List.ofFn H.label) ≤
    designatedLabelCount (List.ofFn K.label)
  rw [designatedLabelCount_ofFn_eq_indicatorFinset,
    designatedLabelCount_ofFn_eq_indicatorFinset]
  exact Finset.sum_le_sum
    (fun j _ => K.twoShort_indicator_pointwise_le D H t
      first second hLabels j)

/-- A two-short replacement removes at least one genuinely designated
original occurrence exactly when that source position carried a
designated label. Under this explicit hypothesis the count drops
STRICTLY. No target-label provenance assumption is needed. -/
theorem BigCycle.twoConsecutiveShort_designatedCount_lt
    {n : ℕ} (K H : D.BigCycle n)
    (t : Fin n) (first second : E)
    (hLabels : ∀ j : Fin n,
      H.label j = K.twoConsecutiveShortLabels D t first second j)
    (hDesignated : D.designated (K.label t) ∨
      D.designated (K.label (cyclicSucc t))) :
    H.designatedOccurrenceCount D <
      K.designatedOccurrenceCount D := by
  change designatedLabelCount (List.ofFn H.label) <
    designatedLabelCount (List.ofFn K.label)
  rw [designatedLabelCount_ofFn_eq_indicatorFinset,
    designatedLabelCount_ofFn_eq_indicatorFinset]
  have hOldWeight (j : Fin n)
      (hD : D.designated (K.label j)) :
      designatedLabelIndicator (K.label j) = 1 := by
    cases h : K.label j with
    | inl i => simp [designatedLabelIndicator, h]
    | inr e =>
        have hf : False := by
          simpa [OrderOneData.designated, h] using hD
        exact False.elim hf
  have hNewWeightAt :
      designatedLabelIndicator (H.label t) = 0 := by
    rw [hLabels t]
    simp [BigCycle.twoConsecutiveShortLabels,
      designatedLabelIndicator]
  have hNewWeightNext :
      designatedLabelIndicator (H.label (cyclicSucc t)) = 0 := by
    have hNe : cyclicSucc t ≠ t :=
      cyclicSucc_ne_self_of_two_le K.length_ge_two t
    rw [hLabels (cyclicSucc t)]
    simp [BigCycle.twoConsecutiveShortLabels,
      designatedLabelIndicator, hNe]
  apply Finset.sum_lt_sum
    (fun j _ => K.twoShort_indicator_pointwise_le D H t
      first second hLabels j)
  rcases hDesignated with hAt | hNext
  · refine ⟨t, Finset.mem_univ _, ?_⟩
    rw [hNewWeightAt, hOldWeight t hAt]
    omega
  · refine ⟨cyclicSucc t, Finset.mem_univ _, ?_⟩
    rw [hNewWeightNext, hOldWeight (cyclicSucc t) hNext]
    omega

end OrderOneData
end StructuralRamsey.Girth
