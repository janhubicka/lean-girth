import Girth.TrainFillingSystemGirth
import Girth.TrainAllAdjacentParameterPreservation

/-!
# The actual train restored by a filling

Insert equality of filled edges at level zero. At every positive level,
pull the preceding old relation back along the prescribed cover map.
In particular the FIRST wagons are cover fibres, not equality classes of
filled edges. All old levels, including their universal top, are retained
one index higher. The height increases by exactly one.

Coverage proves exact wagon carriers at every inherited level. The map
on wagon labels is injective without a nonemptiness assumption; it is
surjective when the old edges are nonempty. This distinction matters for
empty old edges, whose filling fibres may be empty.

No ambient edge is removed and no cycle bound above the top is requested.
-/

namespace StructuralRamsey.Girth.TrainFilling

universe v
variable {V : Type v} (F : TrainFilling V) {m : ℕ}

/-- The old index immediately below a positive restored index. Its value
at zero is harmless; the restored bottom relation is defined separately. -/
def inheritedOldLevel (ν : Fin (m + 1 + 1)) : Fin (m + 1) :=
  ⟨ν.val - 1, by have := ν.isLt; omega⟩

/-- Equality at zero, followed by the literal pullbacks of ALL old levels. -/
def inheritedTrain (T : EdgeTrainLevels F.OldEdge m) :
    EdgeTrainLevels F.NewEdge (m + 1) where
  rel ν e f := if ν.val = 0 then e = f
    else T.rel (inheritedOldLevel ν) (F.cover e) (F.cover f)
  equivalent := by
    intro ν
    by_cases hν : ν.val = 0
    · simp only [hν, if_pos]
      exact ⟨fun _ => rfl, fun h => h.symm, fun h k => h.trans k⟩
    · simp only [hν, if_neg]
      exact ⟨fun e => (T.equivalent _).refl (F.cover e),
        fun h => (T.equivalent _).symm h,
        fun h k => (T.equivalent _).trans h k⟩
  nested := by
    intro μ ν hμν e f hef
    by_cases hμ : μ.val = 0
    · simp only [hμ, if_pos] at hef
      subst f
      by_cases hν : ν.val = 0
      · simp only [hν, if_pos]
      · simp only [hν, if_neg]
        exact (T.equivalent _).refl _
    · have hν : ν.val ≠ 0 := by
        have hv : μ.val ≤ ν.val := hμν
        omega
      simp only [hμ, if_neg] at hef
      simp only [hν, if_neg]
      exact T.nested _ _ (Nat.sub_le_sub_right hμν 1) _ _ hef
  bottom := by
    intro e f
    simp
  top := by
    intro e f
    have hpos : m + 1 ≠ 0 := by omega
    simp only [hpos, if_neg]
    have htop : inheritedOldLevel (⟨m + 1, Nat.lt_succ_self _⟩ : Fin (m + 1 + 1)) =
        (⟨m, Nat.lt_succ_self m⟩ : Fin (m + 1)) := by
      apply Fin.ext
      simp [inheritedOldLevel]
    rw [htop]
    exact T.top _ _

@[simp] theorem inheritedTrain_rel_zero (T : EdgeTrainLevels F.OldEdge m)
    (e f : F.NewEdge) : (F.inheritedTrain T).rel 0 e f ↔ e = f := by
  simp [inheritedTrain]

@[simp] theorem inheritedTrain_rel_succ (T : EdgeTrainLevels F.OldEdge m)
    (ν : Fin (m + 1)) (e f : F.NewEdge) :
    (F.inheritedTrain T).rel ν.succ e f ↔ T.rel ν (F.cover e) (F.cover f) := by
  have hindex : inheritedOldLevel ν.succ = ν := by
    apply Fin.ext
    simp [inheritedOldLevel]
  simp [inheritedTrain, hindex]

/-- The inserted first partition is precisely the partition into fibres. -/
theorem inheritedTrain_first_rel (T : EdgeTrainLevels F.OldEdge m)
    (e f : F.NewEdge) :
    (F.inheritedTrain T).rel (0 : Fin (m + 1)).succ e f ↔ F.cover e = F.cover f := by
  rw [F.inheritedTrain_rel_succ]
  exact T.bottom _ _

@[simp] theorem inheritedTrain_bottom_carrier (T : EdgeTrainLevels F.OldEdge m)
    (e : F.NewEdge) :
    (F.inheritedTrain T).wagonCarrier (fun a => a.1) 0 e = e.1 := by
  ext x
  change (∃ a, (F.inheritedTrain T).rel 0 e a ∧ x ∈ a.1) ↔ x ∈ e.1
  simp only [F.inheritedTrain_rel_zero]
  constructor
  · rintro ⟨a, h, hx⟩
    subst a
    exact hx
  · intro hx
    exact ⟨e, rfl, hx⟩

/-- All inherited wagon carriers are EXACTLY their old carriers, not just
subsets. The reverse direction uses the full pointwise filling coverage. -/
theorem inheritedTrain_wagonCarrier (T : EdgeTrainLevels F.OldEdge m)
    (ν : Fin (m + 1)) (e : F.NewEdge) :
    (F.inheritedTrain T).wagonCarrier (fun a => a.1) ν.succ e =
      T.wagonCarrier (fun a => a.1) ν (F.cover e) := by
  ext x
  change (∃ a, (F.inheritedTrain T).rel ν.succ e a ∧ x ∈ a.1) ↔
    ∃ b, T.rel ν (F.cover e) b ∧ x ∈ b.1
  simp only [F.inheritedTrain_rel_succ]
  constructor
  · rintro ⟨a, h, hx⟩
    exact ⟨F.cover a, h, F.contained a hx⟩
  · rintro ⟨b, h, hx⟩
    obtain ⟨a, ha, hxa⟩ := F.covering b x hx
    exact ⟨a, by simpa only [ha] using h, hxa⟩

/-- Canonical faithful mapping of restored wagon LABELS to old labels. -/
def inheritedWagonEmbedding (T : EdgeTrainLevels F.OldEdge m) (ν : Fin (m + 1)) :
    Quotient ((F.inheritedTrain T).wagonSetoid ν.succ) ↪ Quotient (T.wagonSetoid ν) := by
  let map : Quotient ((F.inheritedTrain T).wagonSetoid ν.succ) →
      Quotient (T.wagonSetoid ν) := fun q => Quotient.liftOn q
    (fun a => Quotient.mk (T.wagonSetoid ν) (F.cover a))
    (by
      intro a b hab
      exact Quotient.sound ((F.inheritedTrain_rel_succ T ν a b).mp hab))
  refine ⟨map, ?_⟩
  intro a b hab
  induction a using Quotient.inductionOn with
  | h a =>
    induction b using Quotient.inductionOn with
    | h b =>
      have hrel : T.rel ν (F.cover a) (F.cover b) := Quotient.exact hab
      exact Quotient.sound ((F.inheritedTrain_rel_succ T ν a b).mpr hrel)

@[simp] theorem inheritedWagonEmbedding_mk (T : EdgeTrainLevels F.OldEdge m)
    (ν : Fin (m + 1)) (e : F.NewEdge) :
    F.inheritedWagonEmbedding T ν
      (Quotient.mk ((F.inheritedTrain T).wagonSetoid ν.succ) e) =
        Quotient.mk (T.wagonSetoid ν) (F.cover e) := rfl

/-- Exact carrier equality on actual quotient labels. -/
theorem inheritedWagonEmbedding_carrier (T : EdgeTrainLevels F.OldEdge m)
    (ν : Fin (m + 1))
    (a : Quotient ((F.inheritedTrain T).wagonSetoid ν.succ)) :
    (F.inheritedTrain T).wagonClassCarrier (fun e => e.1) ν.succ a =
      T.wagonClassCarrier (fun e => e.1) ν (F.inheritedWagonEmbedding T ν a) := by
  induction a using Quotient.inductionOn with
  | h e => exact F.inheritedTrain_wagonCarrier T ν e

/-- Coverage supplies every old edge as a cover provided it is nonempty. -/
theorem cover_surjective_of_nonempty
    (hNonempty : ∀ f : F.OldEdge, f.1.Nonempty) : Function.Surjective F.cover := by
  intro f
  obtain ⟨x, hx⟩ := hNonempty f
  obtain ⟨e, he, _⟩ := F.covering f x hx
  exact ⟨e, he⟩

/-- Nonempty old edges rule out unused old quotient labels. No such
surjectivity is silently inferred from coverage of an empty old edge. -/
theorem inheritedWagonEmbedding_surjective (T : EdgeTrainLevels F.OldEdge m)
    (hNonempty : ∀ f : F.OldEdge, f.1.Nonempty) (ν : Fin (m + 1)) :
    Function.Surjective (F.inheritedWagonEmbedding T ν) := by
  intro a
  induction a using Quotient.inductionOn with
  | h f =>
    obtain ⟨e, he⟩ := F.cover_surjective_of_nonempty hNonempty f
    refine ⟨Quotient.mk _ e, ?_⟩
    simp only [F.inheritedWagonEmbedding_mk, he]

/-- The actual quotient parent maps commute at every pair of inherited
levels, including the universal top. -/
theorem inheritedWagonEmbedding_parent (T : EdgeTrainLevels F.OldEdge m)
    (μ ν : Fin (m + 1)) (hμν : μ ≤ ν)
    (a : Quotient ((F.inheritedTrain T).wagonSetoid μ.succ)) :
    F.inheritedWagonEmbedding T ν
      ((F.inheritedTrain T).wagonParent μ.succ ν.succ
        (show μ.succ ≤ ν.succ from Nat.succ_le_succ hμν) a) =
    T.wagonParent μ ν hμν (F.inheritedWagonEmbedding T μ a) := by
  induction a using Quotient.inductionOn with
  | h e => rfl

end StructuralRamsey.Girth.TrainFilling
