import Girth.TrainWagonNodeGluing

/-!
# Exact restrictions and contractions of generated wagon classes

The exact wagon restriction lemma has two aspects:
(1) the generated relation on real edges has the
shared/private ancestor normal form;
(2) this normal form restricts exactly to both old standard-picture
and core wagon equivalences. This file checks (2), conditional on
the normal-form criterion (1).

This does NOT validate the global train system-Girth argument.
-/

namespace StructuralRamsey.Girth

universe u v w x y z
variable {E : Type u} {Core : Type v} {Old : Type w}
variable {I : Type x} {CoreEdge : Type y} {OldEdge : Type z}

/-- The generated equivalence restricts exactly to the core wagon classes. -/
theorem normalForm_restrict_core
    (R : E → E → Prop)
    (tag : E → Core ⊕ (I × Old))
    (hTag : ∀ e f, R e f ↔ tag e = tag f)
    (coreEmbed : CoreEdge → E)
    (coreClass : CoreEdge → Core)
    (hCoreTag : ∀ a, tag (coreEmbed a) = Sum.inl (coreClass a))
    (a b : CoreEdge) :
    R (coreEmbed a) (coreEmbed b) ↔
      coreClass a = coreClass b := by
  rw [hTag (coreEmbed a) (coreEmbed b), hCoreTag a, hCoreTag b]
  simp

/-- Reflection for a single standard picture follows from
injectivity of its old-wagon ancestor map. -/
theorem normalForm_restrict_standard
    (R : E → E → Prop)
    (tag : E → Core ⊕ (I × Old))
    (hTag : ∀ e f, R e f ↔ tag e = tag f)
    (glue : I → Old → Option Core)
    (hInjective : ∀ i a b c,
      glue i a = some c → glue i b = some c → a = b)
    (std : I → OldEdge → E)
    (oldClass : OldEdge → Old)
    (hStdTag : ∀ i a,
      tag (std i a) = gluedStandardNode glue i (oldClass a))
    (i : I) (a b : OldEdge) :
    R (std i a) (std i b) ↔ oldClass a = oldClass b := by
  have hInj : Function.Injective (gluedStandardNode glue i) :=
    gluedStandardNode_injective glue hInjective i
  constructor
  · intro hr
    apply hInj
    calc
      gluedStandardNode glue i (oldClass a) = tag (std i a) :=
        (hStdTag i a).symm
      _ = tag (std i b) := (hTag _ _).mp hr
      _ = gluedStandardNode glue i (oldClass b) := hStdTag i b
  · intro heq
    apply (hTag _ _).mpr
    calc
      tag (std i a) = gluedStandardNode glue i (oldClass a) :=
        hStdTag i a
      _ = gluedStandardNode glue i (oldClass b) :=
        congrArg (gluedStandardNode glue i) heq
      _ = tag (std i b) := (hStdTag i b).symm

/-- A wagon contracts to exactly the shared core wagon named by its tag. -/
theorem normalForm_core_contraction
    (R : E → E → Prop)
    (tag : E → Core ⊕ (I × Old))
    (hTag : ∀ e f, R e f ↔ tag e = tag f)
    (coreEmbed : CoreEdge → E)
    (coreClass : CoreEdge → Core)
    (hCoreTag : ∀ a, tag (coreEmbed a) = Sum.inl (coreClass a))
    (e : E) (a : CoreEdge) :
    R e (coreEmbed a) ↔ tag e = Sum.inl (coreClass a) := by
  rw [hTag e (coreEmbed a), hCoreTag a]

/-- Private wagon labels have empty core contractions. -/
theorem normalForm_private_not_core
    (R : E → E → Prop)
    (tag : E → Core ⊕ (I × Old))
    (hTag : ∀ e f, R e f ↔ tag e = tag f)
    (coreEmbed : CoreEdge → E)
    (coreClass : CoreEdge → Core)
    (hCoreTag : ∀ a, tag (coreEmbed a) = Sum.inl (coreClass a))
    (e : E) (i : I) (u : Old)
    (he : tag e = Sum.inr (i, u))
    (a : CoreEdge) : ¬ R e (coreEmbed a) := by
  intro hr
  have h := (normalForm_core_contraction R tag hTag coreEmbed
    coreClass hCoreTag e a).mp hr
  rw [he] at h
  cases h

/-- Different standard copies can share an output wagon only
through a genuinely common core wagon contact. -/
theorem normalForm_cross_standard_core_contact
    (R : E → E → Prop)
    (tag : E → Core ⊕ (I × Old))
    (hTag : ∀ e f, R e f ↔ tag e = tag f)
    (glue : I → Old → Option Core)
    (std : I → OldEdge → E)
    (oldClass : OldEdge → Old)
    (hStdTag : ∀ i a,
      tag (std i a) = gluedStandardNode glue i (oldClass a))
    (i j : I) (hij : i ≠ j)
    (a b : OldEdge)
    (hr : R (std i a) (std j b)) :
    ∃ c : Core,
      glue i (oldClass a) = some c ∧
      glue j (oldClass b) = some c := by
  have ht :
      gluedStandardNode glue i (oldClass a) =
        gluedStandardNode glue j (oldClass b) := by
    calc
      gluedStandardNode glue i (oldClass a) = tag (std i a) :=
        (hStdTag i a).symm
      _ = tag (std j b) := (hTag _ _).mp hr
      _ = gluedStandardNode glue j (oldClass b) := hStdTag j b
  exact gluedStandardNode_shared_of_distinct_indices
    glue i j hij (oldClass a) (oldClass b) ht

end StructuralRamsey.Girth
