import Girth.TrainEquivalenceRestriction

/-!
# Faithful transport of nested wagon equivalences across an edge bijection

The actual A-support pushout program constructs a bijection between
canonical presented support edges and genuine ambient A-copy carriers.
Any train on the presented edges must then move to the physical A-support
family without changing wagon equivalences, parent hierarchy or vertex
carriers of individual labelled wagons.

Here transport is along an EDGE EQUIVALENCE, not by identifying wagon
labels because their vertex carriers happen to be equal.

This module checks the first exact translation: every equivalence cut
is transported with full preservation/reflection, bottom equality and
top universality; every OLD labelled wagon carrier agrees with the
carrier of the corresponding transported wagon label under a
carrier-preserving edge bijection. Global acceptable-cycle properties
are separate and are NOT automatically transported by arbitrary maps
unless all ambient incidence and connector predicates are identified.
-/

namespace StructuralRamsey.Girth

universe v
variable {E F W : Type v}

/-- Transfer all nested train edge-equivalences along a bijection of
actual physical edge labels. -/
def EdgeTrainLevels.transport
    {m : ℕ} (T : EdgeTrainLevels E m)
    (ϕ : E ≃ F) : EdgeTrainLevels F m where
  rel := fun μ x y => T.rel μ (ϕ.symm x) (ϕ.symm y)
  equivalent := by
    intro μ
    let h := T.equivalent μ
    exact ⟨fun x => h.refl (ϕ.symm x),
      fun {x y} hxy => h.symm hxy,
      fun {x y z} hxy hyz => h.trans hxy hyz⟩
  nested := by
    intro μ ν hμν x y hxy
    exact T.nested μ ν hμν (ϕ.symm x) (ϕ.symm y) hxy
  bottom := by
    intro x y
    constructor
    · intro hxy
      apply ϕ.symm.injective
      exact (T.bottom (ϕ.symm x) (ϕ.symm y)).mp hxy
    · intro hxy
      subst y
      exact (T.bottom (ϕ.symm x) (ϕ.symm x)).mpr rfl
  top := fun x y => T.top (ϕ.symm x) (ϕ.symm y)

/-- Equivalence of physical edges at every train level is exactly
equivalence of their old labels. -/
theorem EdgeTrainLevels.transport_rel_iff
    {m : ℕ} (T : EdgeTrainLevels E m)
    (ϕ : E ≃ F) (μ : Fin (m + 1)) (x y : E) :
    (T.transport ϕ).rel μ (ϕ x) (ϕ y) ↔
      T.rel μ x y := by
  change T.rel μ (ϕ.symm (ϕ x)) (ϕ.symm (ϕ y)) ↔ T.rel μ x y
  simp

/-- The transported train still has EXACTLY the original nesting,
bottom equality and top universality, without any quotienting of
distinct edge labels by equal carriers. -/
theorem EdgeTrainLevels.transport_reflect
    {m : ℕ} (T : EdgeTrainLevels E m)
    (ϕ : E ≃ F) (μ : Fin (m + 1)) (x y : F) :
    (T.transport ϕ).rel μ x y ↔
      T.rel μ (ϕ.symm x) (ϕ.symm y) :=
  Iff.rfl

/-- The wagon carrier of a particular edge LABEL is unchanged by a
support-carrier-preserving bijection, for EVERY train level. This
statement respects labels even when two labelled wagons have
identical physical vertex carriers. -/
theorem EdgeTrainLevels.transport_wagonCarrier_eq
    {m : ℕ} (T : EdgeTrainLevels E m)
    (ϕ : E ≃ F)
    (oldCarrier : E → Set W)
    (newCarrier : F → Set W)
    (hCarrier : ∀ e : E, newCarrier (ϕ e) = oldCarrier e)
    (μ : Fin (m + 1)) (a : E) :
    (T.transport ϕ).wagonCarrier newCarrier μ (ϕ a) =
      T.wagonCarrier oldCarrier μ a := by
  ext x
  constructor
  · rintro ⟨b, hab, hxb⟩
    refine ⟨ϕ.symm b, ?_, ?_⟩
    · change T.rel μ (ϕ.symm (ϕ a)) (ϕ.symm b) at hab
      simpa only [ϕ.symm_apply_apply] using hab
    · have hc : newCarrier b = oldCarrier (ϕ.symm b) := by
        simpa only [ϕ.apply_symm_apply] using hCarrier (ϕ.symm b)
      rw [hc] at hxb
      exact hxb
  · rintro ⟨b, hab, hxb⟩
    refine ⟨ϕ b, ?_, ?_⟩
    · change T.rel μ (ϕ.symm (ϕ a)) (ϕ.symm (ϕ b))
      simpa only [ϕ.symm_apply_apply] using hab
    · rw [hCarrier b]
      exact hxb

end StructuralRamsey.Girth
