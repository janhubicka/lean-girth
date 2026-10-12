import Girth.TrainWagonNodeGluing
import Mathlib.Tactic

/-!
# Canonical gluing contacts between old and core wagon ancestors

At a fixed train level, the gluing subsystem associates to an old wagon
either precisely ONE core wagon or none. Defining the optional contact
via classical choice gives the core tag of the shared/private normal form.
The uniqueness and reflection hypotheses are exactly the local facts
needed for injectivity; parent contact preservation then yields the
canonical parent-compatibility equation.

The actual picture step must still prove these hypotheses from its
edge-subsystem embeddings. No theorem here asserts full system-Girth.
-/

namespace StructuralRamsey.Girth

universe u v w
variable {Core : Type u} {Old : Type v} {I : Type w}

/-- A wagon touching a unique core ancestor is glued to that ancestor;
a wagon with no core contact keeps a private label. -/
noncomputable def wagonContactGlue
    (touch : I → Old → Core → Prop) (i : I) (a : Old) :
    Option Core := by
  classical
  exact if h : ∃ c : Core, touch i a c then
    some (Classical.choose h)
  else none

/-- When an old wagon has at most one core contact, its optional
contact label is independent of the classical witness selected. -/
theorem wagonContactGlue_eq_some_iff
    (touch : I → Old → Core → Prop)
    (hUnique : ∀ i a c d,
      touch i a c → touch i a d → c = d)
    (i : I) (a : Old) (c : Core) :
    wagonContactGlue touch i a = some c ↔ touch i a c := by
  classical
  by_cases hExists : ∃ d : Core, touch i a d
  · let d : Core := Classical.choose hExists
    have hd : touch i a d := Classical.choose_spec hExists
    have hEq : wagonContactGlue touch i a = some d := by
      simp [wagonContactGlue, hExists, d]
    constructor
    · intro h
      have hdc : d = c := Option.some.inj (hEq.symm.trans h)
      simpa [hdc] using hd
    · intro hc
      have hdc : d = c := hUnique i a d c hd hc
      calc
        wagonContactGlue touch i a = some d := hEq
        _ = some c := congrArg some hdc
  · constructor
    · intro h
      have hFalse : False := by
        simpa [wagonContactGlue, hExists] using h
      exact hFalse.elim
    · intro hc
      exact (hExists ⟨c, hc⟩).elim

/-- Reflection across a subsystem embedding: distinct old wagon
ancestors do not glue to one and the same core ancestor. -/
theorem wagonContactGlue_injective
    (touch : I → Old → Core → Prop)
    (hUnique : ∀ i a c d,
      touch i a c → touch i a d → c = d)
    (hReflect : ∀ i a b c,
      touch i a c → touch i b c → a = b) :
    ∀ i a b c,
      wagonContactGlue touch i a = some c →
      wagonContactGlue touch i b = some c → a = b := by
  intro i a b c ha hb
  exact hReflect i a b c
    ((wagonContactGlue_eq_some_iff touch hUnique i a c).mp ha)
    ((wagonContactGlue_eq_some_iff touch hUnique i b c).mp hb)

/-- The one-contact and reflection axioms discharge the local
injectivity hypothesis of the tagged ancestor gluing theorem. -/
theorem gluedStandardNode_injective_of_contacts
    (touch : I → Old → Core → Prop)
    (hUnique : ∀ i a c d,
      touch i a c → touch i a d → c = d)
    (hReflect : ∀ i a b c,
      touch i a c → touch i b c → a = b)
    (i : I) :
    Function.Injective (gluedStandardNode (wagonContactGlue touch) i) :=
  gluedStandardNode_injective
    (wagonContactGlue touch)
    (wagonContactGlue_injective touch hUnique hReflect)
    i

/-- Shared parent contact is automatic whenever every touched
child wagon's parent touches the parent of that core wagon. -/
theorem wagonContactGlue_parent
    {CoreChild : Type u} {OldChild : Type v}
    {CoreParent : Type u} {OldParent : Type v}
    (childTouch : I → OldChild → CoreChild → Prop)
    (parentTouch : I → OldParent → CoreParent → Prop)
    (hChildUnique : ∀ i a c d,
      childTouch i a c → childTouch i a d → c = d)
    (hParentUnique : ∀ i a c d,
      parentTouch i a c → parentTouch i a d → c = d)
    (pCore : CoreChild → CoreParent)
    (pOld : OldChild → OldParent)
    (hParentTouch : ∀ i a c,
      childTouch i a c →
      parentTouch i (pOld a) (pCore c))
    (i : I) (a : OldChild) (c : CoreChild)
    (hContact : wagonContactGlue childTouch i a = some c) :
    wagonContactGlue parentTouch i (pOld a) = some (pCore c) := by
  apply (wagonContactGlue_eq_some_iff
    parentTouch hParentUnique i (pOld a) (pCore c)).mpr
  exact hParentTouch i a c
    ((wagonContactGlue_eq_some_iff
      childTouch hChildUnique i a c).mp hContact)

/-- Parent maps of the actual shared/private tagged model commute
with the old standard-picture parent maps under the geometric
contact axioms, including private-to-shared parent transitions. -/
theorem gluedWagonParent_standard_of_contacts
    {CoreChild : Type u} {OldChild : Type v}
    {CoreParent : Type u} {OldParent : Type v}
    (childTouch : I → OldChild → CoreChild → Prop)
    (parentTouch : I → OldParent → CoreParent → Prop)
    (hChildUnique : ∀ i a c d,
      childTouch i a c → childTouch i a d → c = d)
    (hParentUnique : ∀ i a c d,
      parentTouch i a c → parentTouch i a d → c = d)
    (pCore : CoreChild → CoreParent)
    (pOld : OldChild → OldParent)
    (hParentTouch : ∀ i a c,
      childTouch i a c →
      parentTouch i (pOld a) (pCore c))
    (i : I) (a : OldChild) :
    gluedWagonParent
      (wagonContactGlue childTouch)
      (wagonContactGlue parentTouch) pCore pOld
      (gluedStandardNode (wagonContactGlue childTouch) i a) =
    gluedStandardNode (wagonContactGlue parentTouch) i (pOld a) :=
  gluedWagonParent_standard
    (wagonContactGlue childTouch)
    (wagonContactGlue parentTouch)
    pCore pOld
    (fun j b c h =>
      wagonContactGlue_parent childTouch parentTouch
        hChildUnique hParentUnique pCore pOld hParentTouch j b c h)
    i a

end StructuralRamsey.Girth
