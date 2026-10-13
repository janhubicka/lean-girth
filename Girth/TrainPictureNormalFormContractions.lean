import Girth.TrainNormalFormRestriction
import Girth.TrainPictureWagonGenerators

/-!
# Genuine contraction geometry of generated core/private wagon classes

An exact shared/private ancestor normal form already forces the
remaining contraction assertions from circulation Lemma lem:exact:

* a wagon meeting two DIFFERENT full standard pictures must meet an
  actual core edge (provided every core quotient ancestor has an edge
  representative);
* a PRIVATE wagon has all of its physical edges in ONE standard copy;
* two distinct generated wagons cannot have the same nonempty core
  contraction.

The proof uses equality of tagged WAGON ANCESTORS, not equality of
their possibly duplicate VERTEX carriers. This is deliberately
independent of cycle legality and of allowed-part parameters.
-/

namespace StructuralRamsey.Girth

universe v
variable {E Core Old I CoreEdge OldEdge : Type v}

/-- If the same generated wagon meets two distinct standard-copy
indices, it is connected to a real core edge representing the
shared core ancestor. -/
theorem normalForm_cross_standard_has_core_edge
    (R : E → E → Prop)
    (tag : E → Core ⊕ (I × Old))
    (hTag : ∀ e f, R e f ↔ tag e = tag f)
    (glue : I → Old → Option Core)
    (coreEmbed : CoreEdge → E)
    (coreClass : CoreEdge → Core)
    (hCoreTag : ∀ c, tag (coreEmbed c) = Sum.inl (coreClass c))
    (hCoreSurj : Function.Surjective coreClass)
    (std : I → OldEdge → E)
    (oldClass : OldEdge → Old)
    (hStdTag : ∀ i a,
      tag (std i a) = gluedStandardNode glue i (oldClass a))
    (i j : I) (hij : i ≠ j)
    (a b : OldEdge)
    (hSame : R (std i a) (std j b)) :
    ∃ c : CoreEdge,
      R (std i a) (coreEmbed c) ∧
      R (std j b) (coreEmbed c) := by
  obtain ⟨u, hi, hj⟩ :=
    normalForm_cross_standard_core_contact
      R tag hTag glue std oldClass hStdTag i j hij a b hSame
  obtain ⟨c, hc⟩ := hCoreSurj u
  refine ⟨c, ?_, ?_⟩
  · apply (hTag _ _).mpr
    calc
      tag (std i a) = gluedStandardNode glue i (oldClass a) :=
        hStdTag i a
      _ = Sum.inl u := by simp [gluedStandardNode, hi]
      _ = Sum.inl (coreClass c) := by rw [hc]
      _ = tag (coreEmbed c) := (hCoreTag c).symm
  · apply (hTag _ _).mpr
    calc
      tag (std j b) = gluedStandardNode glue j (oldClass b) :=
        hStdTag j b
      _ = Sum.inl u := by simp [gluedStandardNode, hj]
      _ = Sum.inl (coreClass c) := by rw [hc]
      _ = tag (coreEmbed c) := (hCoreTag c).symm

/-- Every physical edge equivalent to a PRIVATE wagon edge lies
in the same indexed full standard picture and old wagon class. -/
theorem normalForm_private_wagon_has_unique_standard_owner
    (R : E → E → Prop)
    (tag : E → Core ⊕ (I × Old))
    (hTag : ∀ e f, R e f ↔ tag e = tag f)
    (coreEmbed : CoreEdge → E)
    (std : I → OldEdge → E)
    (coreClass : CoreEdge → Core)
    (oldClass : OldEdge → Old)
    (glue : I → Old → Option Core)
    (hCoreTag : ∀ c, tag (coreEmbed c) = Sum.inl (coreClass c))
    (hStdTag : ∀ i a,
      tag (std i a) = gluedStandardNode glue i (oldClass a))
    (hCover : ∀ e : E,
      (∃ c, e = coreEmbed c) ∨ ∃ i a, e = std i a)
    (e f : E) (i : I) (a : Old)
    (hPrivate : tag e = Sum.inr (i, a))
    (hef : R e f) :
    ∃ b : OldEdge, f = std i b ∧ oldClass b = a := by
  have hf : tag f = Sum.inr (i, a) :=
    ((hTag _ _).mp hef).symm.trans hPrivate
  exact privatePictureTag_has_standard_owner
    coreEmbed std coreClass oldClass glue tag
    hCoreTag hStdTag hCover f i a hf

/-- Nonempty core contractions are UNIQUE: two generated wagons
meeting the same core wagon are themselves equivalent. -/
theorem normalForm_same_core_contraction_implies_equivalent
    (R : E → E → Prop)
    (tag : E → Core ⊕ (I × Old))
    (hTag : ∀ e f, R e f ↔ tag e = tag f)
    (coreEmbed : CoreEdge → E)
    (coreClass : CoreEdge → Core)
    (hCoreTag : ∀ c, tag (coreEmbed c) = Sum.inl (coreClass c))
    (e f : E) (a b : CoreEdge)
    (hea : R e (coreEmbed a))
    (hfb : R f (coreEmbed b))
    (hab : coreClass a = coreClass b) :
    R e f := by
  apply (hTag _ _).mpr
  calc
    tag e = tag (coreEmbed a) := (hTag _ _).mp hea
    _ = Sum.inl (coreClass a) := hCoreTag a
    _ = Sum.inl (coreClass b) := congrArg Sum.inl hab
    _ = tag (coreEmbed b) := (hCoreTag b).symm
    _ = tag f := ((hTag _ _).mp hfb).symm

end StructuralRamsey.Girth
