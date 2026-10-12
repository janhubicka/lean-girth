import Girth.TrainWagonNodeGluing

/-!
# Exact restrictions of a generated wagon equivalence in normal form

Suppose the actual equivalence of physical edges is equality of their
canonical shared/private wagon-ancestor labels, and the labels on
core and standard-piece edges have the expected value.

Then exact restriction to the core is immediate. Exact restriction to
one standard piece follows from its injective ancestor map, which in
turn follows from reflection of the gluing contact. Furthermore, a
pair of edges from DIFFERENT standard copies can be equivalent only
when both their old wagon ancestors genuinely contact the same core
wagon. These are exactly the easy restriction/contraction consequences
needed by the circulation manuscript's Lemma lem:exact.

The nontrivial remaining step is proving that the actual physical
edge relation really has this tag normal form. That is developed
separately in TrainPhysicalEdgeNormalForm.
-/

namespace StructuralRamsey.Girth

universe u v w x y z
variable {E : Type u} {Core : Type v} {Old : Type w}
variable {I : Type x} {CoreEdge : Type y} {OldEdge : Type z}

/-- Generated equivalence restricts exactly to core wagon equality. -/
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
  rw [hTag, hCoreTag a, hCoreTag b]
  simp

/-- Generated equivalence restricts exactly to old wagon equality
in each standard piece, without requiring that standard wagon to
be wholly private from the core. -/
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
      _ = gluedStandardNode glue i (oldClass b) := congrArg _ heq
      _ = tag (std i b) := (hStdTag i b).symm

/-- A physical edge in the core-contracted wagon has precisely the
core class specified by its shared tag. -/
theorem normalForm_core_contraction
    (R : E → E → Prop)
    (tag : E → Core ⊕ (I × Old))
    (hTag : ∀ e f, R e f ↔ tag e = tag f)
    (coreEmbed : CoreEdge → E)
    (coreClass : CoreEdge → Core)
    (hCoreTag : ∀ a, tag (coreEmbed a) = Sum.inl (coreClass a))
    (e : E) (a : CoreEdge) :
    R e (coreEmbed a) ↔ tag e = Sum.inl (coreClass a) := by
  rw [hTag, hCoreTag a]

/-- Equality across two distinct standard pieces can only arise
through a real shared core wagon, never through two private tags. -/
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
