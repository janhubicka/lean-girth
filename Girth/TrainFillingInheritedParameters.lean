import Girth.TrainFillingInheritedTrain

/-!
# The restored filling train retains the genuine adjacent parameters

The inserted first cut uses the parameter inside one filling fibre.
Every higher adjacent cut uses the ORIGINAL old adjacent parameter and
the exact inherited wagon carriers. The cover is not injective on edges;
we never use an edge-restriction theorem that would require that.

This constructs the full parameter field of the restored height-(m+1)
train, from the intrinsic fibre parameter and old train parameters.
It does not construct the Ramsey witness X, its finite tagged assembly,
or the scattering component data. No new top cycle bound is an input.
-/

namespace StructuralRamsey.Girth
universe v

namespace EdgeTrainLevels
variable {E V : Type v} {m : ℕ}

/-- Express a quotient sibling parameter on representatives, retaining
both the distinct-child and common-parent conditions. -/
theorem parentBound_iff_representatives (T : EdgeTrainLevels E m)
    (edge : E → Set V) (μ ν : Fin (m + 1)) (hμν : μ ≤ ν) (allowed : Set V) :
    TrainParentIntersectionBound (T.wagonClassCarrier edge μ)
      (T.wagonParent μ ν hμν) allowed ↔
    ∀ a b : E, ¬ T.rel μ a b → T.rel ν a b →
      T.wagonCarrier edge μ a ∩ T.wagonCarrier edge μ b ⊆ allowed := by
  constructor
  · intro h a b hne hp
    apply h (i := Quotient.mk (T.wagonSetoid μ) a)
      (j := Quotient.mk (T.wagonSetoid μ) b)
    · intro heq
      exact hne (Quotient.exact heq)
    · exact Quotient.sound hp
  · intro h a b
    induction a using Quotient.inductionOn with
    | h a =>
      induction b using Quotient.inductionOn with
      | h b =>
        intro hne hp
        exact h a b (fun hab => hne (Quotient.sound hab)) (Quotient.exact hp)
end EdgeTrainLevels

namespace TrainFilling
variable {V : Type v} (F : TrainFilling V) {m : ℕ}

/-- The inserted first parameter plus the old tail parameters give ALL
adjacent parameters on the actual restored train. The allowed sets are
retained literally, shifted by one at old cuts. -/
theorem inheritedTrain_adjacentParameters (T : EdgeTrainLevels F.OldEdge m)
    (allowed : Fin (m + 1 + 1) → Set V)
    (hFirst : ∀ a b : F.NewEdge, a ≠ b → F.cover a = F.cover b →
      a.1 ∩ b.1 ⊆ allowed (0 : Fin (m + 1)).succ)
    (hOld : T.AdjacentParameters (fun e => e.1) (fun ν => allowed ν.succ)) :
    (F.inheritedTrain T).AdjacentParameters (fun e => e.1) allowed := by
  intro μ ν hμν hSucc
  apply ((F.inheritedTrain T).parentBound_iff_representatives
    (fun e => e.1) μ ν hμν (allowed ν)).mpr
  intro a b hne hp x hx
  by_cases hμ : μ.val = 0
  · have hzero : μ = 0 := Fin.ext hμ
    have hone : ν = (0 : Fin (m + 1)).succ := by
      apply Fin.ext
      change ν.val = 0 + 1
      omega
    subst μ
    subst ν
    have hab : a ≠ b := by
      intro hab
      exact hne ((F.inheritedTrain_rel_zero T a b).mpr hab)
    have hcover := (F.inheritedTrain_first_rel T a b).mp hp
    have hx' : x ∈ a.1 ∩ b.1 := by
      simpa only [F.inheritedTrain_bottom_carrier] using hx
    exact hFirst a b hab hcover hx'
  · let α := inheritedOldLevel μ
    let β := inheritedOldLevel ν
    have hα : μ = α.succ := by
      apply Fin.ext
      change μ.val = (μ.val - 1) + 1
      omega
    have hβ : ν = β.succ := by
      apply Fin.ext
      change ν.val = (ν.val - 1) + 1
      omega
    have hαβ : α ≤ β := Nat.sub_le_sub_right hμν 1
    have hStep : β.val = α.val + 1 := by
      change ν.val - 1 = (μ.val - 1) + 1
      omega
    have hOldNe : ¬ T.rel α (F.cover a) (F.cover b) := by
      intro hab
      apply hne
      rw [hα]
      exact (F.inheritedTrain_rel_succ T α a b).mpr hab
    have hOldParent : T.rel β (F.cover a) (F.cover b) := by
      rw [hβ] at hp
      exact (F.inheritedTrain_rel_succ T β a b).mp hp
    have hxOld : x ∈ T.wagonCarrier (fun e => e.1) α (F.cover a) ∩
        T.wagonCarrier (fun e => e.1) α (F.cover b) := by
      rw [hα, F.inheritedTrain_wagonCarrier, F.inheritedTrain_wagonCarrier] at hx
      exact hx
    have hBound := (T.parentBound_iff_representatives
      (fun e => e.1) α β hαβ (allowed β.succ)).mp (hOld α β hαβ hStep)
    rw [hβ]
    exact hBound (F.cover a) (F.cover b) hOldNe hOldParent hxOld

end TrainFilling
end StructuralRamsey.Girth
