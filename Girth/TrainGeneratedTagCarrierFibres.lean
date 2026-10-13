import Girth.TrainGeneratedTagCoreParameter

/-!
# Exact vertex carriers of shared/private generated wagon tags

The actual physical picture train has a normal form by generated
shared/core wagon tags. This lemma verifies the entire vertex-carrier
consequence at one cut, using only:
- every physical edge is core or an indexed standard edge;
- equality of generated equivalence classes is exactly equality of tags;
- core/standard edges have their true physical carrier sets;
- tags of those edges are the specified original wagon ancestors.

The result identifies the set of vertices incident with edges of one
generated wagon class with the union of genuine original core and
old wagon carriers carrying the tag. The labels remain distinct even
when their vertex sets happen to coincide.

This is a pure structural kernel. It does not assume Ramsey, girth,
or carrier-injective wagon labels. Applying its interface to the
actual `physicalPictureGeneratedTrain` at every cut is a next task.
-/

namespace StructuralRamsey.Girth

universe v
variable {W E I OldEdge CoreEdge Old Core : Type v}

/-- A genuine old wagon carrier is the union of ALL its source
support edges, for a fixed indexed standard picture. -/
def taggedOldFiberCarrier
    (oldClass : OldEdge → Old)
    (oldEdgeCarrier : I → OldEdge → Set W)
    (i : I) (u : Old) : Set W :=
  {x | ∃ a : OldEdge, oldClass a = u ∧ x ∈ oldEdgeCarrier i a}

/-- A genuine core wagon carrier is the union of ALL its source
support edges, retaining the old/core wagon label separately. -/
def taggedCoreFiberCarrier
    (coreClass : CoreEdge → Core)
    (coreEdgeCarrier : CoreEdge → Set W)
    (c : Core) : Set W :=
  {x | ∃ b : CoreEdge, coreClass b = c ∧ x ∈ coreEdgeCarrier b}

/-- Exact carrier normal form for the generated physical wagon
equivalence class of any edge a. This does NOT conflate distinct
wagon tags with identical set-valued vertex carriers.

The proof is two elementary directions: every equivalent edge has
a core or standard representation, and every vertex in a tagged
source wagon has a representing edge equivalent to a. -/
theorem generatedTaggedWagonCarrier_iff_physicalClass
    (rel : E → E → Prop)
    (tag : E → Core ⊕ (I × Old))
    (coreEmbed : CoreEdge → E)
    (std : I → OldEdge → E)
    (coreClass : CoreEdge → Core)
    (oldClass : OldEdge → Old)
    (glue : I → Old → Option Core)
    (edgeCarrier : E → Set W)
    (coreEdgeCarrier : CoreEdge → Set W)
    (oldEdgeCarrier : I → OldEdge → Set W)
    (hNormal : ∀ a b : E, rel a b ↔ tag a = tag b)
    (hCover : ∀ e : E,
      (∃ b : CoreEdge, e = coreEmbed b) ∨
      (∃ i : I, ∃ a : OldEdge, e = std i a))
    (hCoreTag : ∀ b : CoreEdge,
      tag (coreEmbed b) = Sum.inl (coreClass b))
    (hStdTag : ∀ i : I, ∀ a : OldEdge,
      tag (std i a) = gluedStandardNode glue i (oldClass a))
    (hCorePhysical : ∀ b : CoreEdge,
      edgeCarrier (coreEmbed b) = coreEdgeCarrier b)
    (hStdPhysical : ∀ (i : I) (a : OldEdge),
      edgeCarrier (std i a) = oldEdgeCarrier i a)
    (a : E) (x : W) :
    x ∈ GeneratedTaggedWagonCarrier
      (taggedOldFiberCarrier oldClass oldEdgeCarrier)
      (taggedCoreFiberCarrier coreClass coreEdgeCarrier)
      glue (tag a) ↔
      ∃ b : E, rel a b ∧ x ∈ edgeCarrier b := by
  constructor
  · intro hx
    rcases hx with ⟨c, hc, hcx⟩ | ⟨i, u, hu, hux⟩
    · rcases hcx with ⟨b, hb, hxb⟩
      refine ⟨coreEmbed b, (hNormal a (coreEmbed b)).mpr ?_, ?_⟩
      · calc
          tag a = Sum.inl c := hc
          _ = Sum.inl (coreClass b) := congrArg Sum.inl hb.symm
          _ = tag (coreEmbed b) := (hCoreTag b).symm
      · rw [hCorePhysical b]
        exact hxb
    · rcases hux with ⟨b, hb, hxb⟩
      refine ⟨std i b, (hNormal a (std i b)).mpr ?_, ?_⟩
      · calc
          tag a = gluedStandardNode glue i u := hu
          _ = gluedStandardNode glue i (oldClass b) :=
            congrArg (gluedStandardNode glue i) hb.symm
          _ = tag (std i b) := (hStdTag i b).symm
      · rw [hStdPhysical i b]
        exact hxb
  · rintro ⟨b, hab, hxb⟩
    have hTag : tag a = tag b := (hNormal a b).mp hab
    rcases hCover b with ⟨c, hc⟩ | ⟨i, d, hd⟩
    · have hxc : x ∈ coreEdgeCarrier c := by
        rw [hc, hCorePhysical c] at hxb
        exact hxb
      apply Or.inl
      refine ⟨coreClass c, ?_, ?_⟩
      · calc
          tag a = tag b := hTag
          _ = tag (coreEmbed c) := congrArg tag hc
          _ = Sum.inl (coreClass c) := hCoreTag c
      · exact ⟨c, rfl, hxc⟩
    · have hxd : x ∈ oldEdgeCarrier i d := by
        rw [hd, hStdPhysical i d] at hxb
        exact hxb
      apply Or.inr
      refine ⟨i, oldClass d, ?_, ?_⟩
      · calc
          tag a = tag b := hTag
          _ = tag (std i d) := congrArg tag hd
          _ = gluedStandardNode glue i (oldClass d) := hStdTag i d
      · exact ⟨d, rfl, hxd⟩

end StructuralRamsey.Girth
