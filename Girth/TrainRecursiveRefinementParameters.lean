import Girth.TrainRecursiveRefinementForget

set_option Elab.async false
set_option autoImplicit false

/-!
# Recovering the train parameters after forgetting first refinements

Forgetting inserted first cuts is not an adjacent-cut operation at the
bottom: the physical equality cut is followed by the fine cut `d + 1`.
Two distinct physical edges in that parent have a first common fine
ancestor.  The adjacent parameter at that ancestor bounds their
intersection, so containment of every inserted permitted set in the
original first permitted set recovers the coarse first parameter.

Positive coarse adjacent cuts remain adjacent after the common index
shift.  Their full quotient labels, carriers and parent maps transport
through the exact forgetful equivalences.  No edge is removed and no
two labels are identified because their carriers coincide.

These results derive the coarse parameters from supplied fine parameters.
They need neither child girth nor singleton permitted sets, and do not
construct the recursive local witness that supplies the fine parameters.
-/

namespace StructuralRamsey.Girth.EdgeTrainLevels

universe v
variable {E W : Type v}

/-- Distinct physical edges in one wagon meet in the union of the
permitted sets below that wagon.  The proof descends until their first
common fine ancestor and applies the actual adjacent sibling bound. -/
theorem edgeIntersection_of_firstCommonAncestor
    {h : ℕ} (T : EdgeTrainLevels E h)
    (edge : E → Set W) (fineAllowed : Fin (h + 1) → Set W)
    (hParameters : T.AdjacentParameters edge fineAllowed)
    (ν : Fin (h + 1)) (allowed : Set W)
    (hAllowed : ∀ ρ : Fin (h + 1), 0 < ρ.val → ρ ≤ ν → fineAllowed ρ ⊆ allowed)
    (a b : E) (hne : a ≠ b) (hSame : T.rel ν a b) :
    edge a ∩ edge b ⊆ allowed := by
  have descend : ∀ n : ℕ, ∀ hn : n < h + 1,
      n ≤ ν.val → T.rel ⟨n, hn⟩ a b → edge a ∩ edge b ⊆ allowed := by
    intro n
    induction n with
    | zero =>
        intro hn _ hRel
        exact (hne ((T.bottom a b).mp hRel)).elim
    | succ n ih =>
        intro hn hLe hRel
        have hn' : n < h + 1 := by omega
        by_cases hPrev : T.rel ⟨n, hn'⟩ a b
        · exact ih hn' (by omega) hPrev
        · have hClasses :
              Quotient.mk (T.wagonSetoid ⟨n, hn'⟩) a ≠ Quotient.mk _ b := by
            intro heq
            exact hPrev (Quotient.exact heq)
          have hParent :
              T.wagonParent ⟨n, hn'⟩ ⟨n + 1, hn⟩ (by change n ≤ n + 1; omega)
                  (Quotient.mk _ a) =
                T.wagonParent ⟨n, hn'⟩ ⟨n + 1, hn⟩ (by change n ≤ n + 1; omega)
                  (Quotient.mk _ b) :=
            Quotient.sound hRel
          intro x hx
          exact hAllowed ⟨n + 1, hn⟩ (Nat.zero_lt_succ n) hLe
            (hParameters ⟨n, hn'⟩ ⟨n + 1, hn⟩ (by change n ≤ n + 1; omega)
              rfl hClasses hParent
              ⟨⟨a, (T.equivalent _).refl a, hx.1⟩,
                ⟨b, (T.equivalent _).refl b, hx.2⟩⟩)
  exact descend ν.val ν.isLt (Nat.le_refl _) hSame

/-- Recover every coarse adjacent parameter from the fine train.
All positive fine cuts through `d + 1` are allowed to use smaller sets
inside the original first parameter.  Every retained positive parameter
is likewise allowed to shrink.  Coarse output parameters are proved here,
not supplied as an assumption. -/
theorem forgetFirstCuts_adjacentParameters
    {m d : ℕ} (T : EdgeTrainLevels E (m + d)) (hm : 0 < m)
    (edge : E → Set W) (fineAllowed : Fin (m + d + 1) → Set W)
    (allowed : Fin (m + 1) → Set W)
    (hFine : T.AdjacentParameters edge fineAllowed)
    (hFirst : ∀ ρ : Fin (m + d + 1), 0 < ρ.val → ρ.val ≤ d + 1 →
      fineAllowed ρ ⊆ allowed ⟨1, Nat.succ_lt_succ hm⟩)
    (hRetained : ∀ ν : Fin (m + 1), 0 < ν.val →
      fineAllowed (firstForgetIndex m d ν) ⊆ allowed ν) :
    (T.forgetFirstCuts hm).AdjacentParameters edge allowed := by
  intro μ ν hμν hAdjacent
  by_cases hZero : μ.val = 0
  · have hμ : μ = ⟨0, Nat.zero_lt_succ m⟩ := Fin.ext hZero
    have hν : ν = ⟨1, Nat.succ_lt_succ hm⟩ := by
      apply Fin.ext
      change ν.val = 1
      omega
    subst μ
    subst ν
    intro a b
    induction a using Quotient.inductionOn with
    | h a =>
        induction b using Quotient.inductionOn with
        | h b =>
            intro hDifferent hParent x hx
            have hEdges : a ≠ b := by
              intro heq
              exact hDifferent (congrArg (Quotient.mk _) heq)
            have hFineSame :
                T.rel (firstForgetIndex m d ⟨1, Nat.succ_lt_succ hm⟩) a b :=
              Quotient.exact hParent
            have hBound := T.edgeIntersection_of_firstCommonAncestor
              edge fineAllowed hFine (firstForgetIndex m d ⟨1, Nat.succ_lt_succ hm⟩)
              (allowed ⟨1, Nat.succ_lt_succ hm⟩)
              (by
                intro ρ hPos hLe
                apply hFirst ρ hPos
                change ρ.val ≤ (if (1 : ℕ) = 0 then 0 else 1 + d) at hLe
                simp only [Nat.one_ne_zero, ↓reduceIte] at hLe
                omega)
              a b hEdges hFineSame
            apply hBound
            constructor
            · obtain ⟨c, hac, hxc⟩ := hx.1
              have heq : a = c := ((T.forgetFirstCuts hm).bottom a c).mp hac
              exact heq.symm ▸ hxc
            · obtain ⟨c, hbc, hxc⟩ := hx.2
              have heq : b = c := ((T.forgetFirstCuts hm).bottom b c).mp hbc
              exact heq.symm ▸ hxc
  · have hμPos : 0 < μ.val := Nat.pos_of_ne_zero hZero
    have hνPos : 0 < ν.val := by omega
    have hFineAdjacent :
        (firstForgetIndex m d ν).val = (firstForgetIndex m d μ).val + 1 := by
      simp only [firstForgetIndex, Nat.ne_of_gt hμPos, Nat.ne_of_gt hνPos, ↓reduceIte]
      omega
    intro a b hDifferent hParent x hx
    apply hRetained ν hνPos
    apply hFine (firstForgetIndex m d μ) (firstForgetIndex m d ν)
      (firstForgetIndex_monotone m d hμν) hFineAdjacent
      (show T.forgetFirstCuts_wagonEquiv hm μ a ≠
        T.forgetFirstCuts_wagonEquiv hm μ b from
          fun heq => hDifferent ((T.forgetFirstCuts_wagonEquiv hm μ).injective heq))
    · rw [← T.forgetFirstCuts_wagonParent hm μ ν hμν a,
        ← T.forgetFirstCuts_wagonParent hm μ ν hμν b]
      exact congrArg (T.forgetFirstCuts_wagonEquiv hm ν) hParent
    · rw [← T.forgetFirstCuts_wagonClassCarrier hm edge μ a,
        ← T.forgetFirstCuts_wagonClassCarrier hm edge μ b]
      exact hx

end StructuralRamsey.Girth.EdgeTrainLevels
