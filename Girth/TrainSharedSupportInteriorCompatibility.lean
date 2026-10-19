import Girth.TrainEquivalenceRestriction

/-!
# Circulation: only interior shared-wagon compatibility is substantive

For actual train equivalences, the bottom cut is equality and the top
cut is universal. Thus an injective pair of shared-edge embeddings
automatically preserves and reflects the two endpoint cuts. Only the
interior cuts need separate verification.

This is a reduction of the hRel interface, not its discharge for the
circulation picture step. No appendix results are imported.
-/

namespace StructuralRamsey.Girth

universe v
variable {Shared OldEdge CoreEdge I : Type v} {m : ℕ}

/-- Train compatibility at every interior cut extends to the full
nested train, provided both shared-edge maps are injective. -/
theorem sharedSupportTrainRel_of_interior
    (Told : EdgeTrainLevels OldEdge m)
    (Tcore : EdgeTrainLevels CoreEdge m)
    (inOld : Shared ↪ OldEdge)
    (inCore : I → Shared ↪ CoreEdge)
    (hInterior : ∀ κ : Fin (m + 1),
      κ.val ≠ 0 → κ.val ≠ m →
      ∀ (i : I) (s t : Shared),
        Told.rel κ (inOld s) (inOld t) ↔
        Tcore.rel κ (inCore i s) (inCore i t)) :
    ∀ κ : Fin (m + 1), ∀ (i : I) (s t : Shared),
      Told.rel κ (inOld s) (inOld t) ↔
      Tcore.rel κ (inCore i s) (inCore i t) := by
  intro κ i s t
  by_cases hzero : κ.val = 0
  · have hk : κ = ⟨0, Nat.zero_lt_succ m⟩ := Fin.ext hzero
    subst κ
    constructor
    · intro hold
      have hst : s = t :=
        inOld.injective ((Told.bottom (inOld s) (inOld t)).mp hold)
      exact (Tcore.bottom (inCore i s) (inCore i t)).mpr
        (congrArg (inCore i) hst)
    · intro hcore
      have hst : s = t :=
        (inCore i).injective
          ((Tcore.bottom (inCore i s) (inCore i t)).mp hcore)
      exact (Told.bottom (inOld s) (inOld t)).mpr
        (congrArg inOld hst)
  by_cases htop : κ.val = m
  · have hk : κ = ⟨m, Nat.lt_succ_self m⟩ := Fin.ext htop
    subst κ
    constructor
    · intro _
      exact Tcore.top (inCore i s) (inCore i t)
    · intro _
      exact Told.top (inOld s) (inOld t)
  exact hInterior κ hzero htop i s t

end StructuralRamsey.Girth
