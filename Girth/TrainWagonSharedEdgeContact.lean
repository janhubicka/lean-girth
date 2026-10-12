import Girth.TrainWagonContactGluing

/-!
# Actual shared-edge witnesses for generated wagon contacts

Every core contact in a standard picture must be witnessed by a
physical gluing edge, not merely a vertex or by equal wagon carriers.
At a fixed train cut, old i s and core i s name the respective
old-picture and witness-core ancestors of the same shared edge s.

Preservation and reflection of wagon equality on the glued subsystem
make the resulting old-to-core contact relation functional AND
injective. Since the same edge witnesses the parent-level contact,
parent compatibility is automatic.

These statements reduce the abstract contact axioms from
TrainWagonContactGluing to elementary shared-edge data. The global
picture step must instantiate old and core using genuine embeddings.
-/

namespace StructuralRamsey.Girth

universe u v w x
variable {I : Type u} {Shared : Type v}
variable {Old : Type w} {Core : Type x}

/-- Old and core ancestor labels are in contact precisely if some
physical shared edge has both labels. -/
def wagonSharedEdgeContact
    (old : I → Shared → Old)
    (core : I → Shared → Core)
    (i : I) (a : Old) (c : Core) : Prop :=
  ∃ s : Shared, old i s = a ∧ core i s = c

/-- Preserving equal old wagon labels on shared edges ensures one
old wagon cannot touch two different core wagons. -/
theorem wagonSharedEdgeContact_unique
    (old : I → Shared → Old)
    (core : I → Shared → Core)
    (hPreserve : ∀ i s t,
      old i s = old i t → core i s = core i t)
    (i : I) (a : Old) (c d : Core)
    (hc : wagonSharedEdgeContact old core i a c)
    (hd : wagonSharedEdgeContact old core i a d) :
    c = d := by
  rcases hc with ⟨s, hs, hsc⟩
  rcases hd with ⟨t, ht, htd⟩
  calc
    c = core i s := hsc.symm
    _ = core i t := hPreserve i s t (hs.trans ht.symm)
    _ = d := htd

/-- Reflection of wagon equality on shared edges ensures that
two old wagons touching the same core wagon were already equal. -/
theorem wagonSharedEdgeContact_reflect
    (old : I → Shared → Old)
    (core : I → Shared → Core)
    (hReflect : ∀ i s t,
      core i s = core i t → old i s = old i t)
    (i : I) (a b : Old) (c : Core)
    (ha : wagonSharedEdgeContact old core i a c)
    (hb : wagonSharedEdgeContact old core i b c) :
    a = b := by
  rcases ha with ⟨s, hs, hsc⟩
  rcases hb with ⟨t, ht, htc⟩
  calc
    a = old i s := hs.symm
    _ = old i t := hReflect i s t (hsc.trans htc.symm)
    _ = b := ht

/-- The same physical gluing edge witnesses the parent contact. -/
theorem wagonSharedEdgeContact_parent
    (old : I → Shared → Old)
    (core : I → Shared → Core)
    {OldParent : Type w} {CoreParent : Type x}
    (pOld : Old → OldParent) (pCore : Core → CoreParent)
    (i : I) (a : Old) (c : Core)
    (h : wagonSharedEdgeContact old core i a c) :
    wagonSharedEdgeContact
        (fun j s => pOld (old j s))
        (fun j s => pCore (core j s))
        i (pOld a) (pCore c) := by
  rcases h with ⟨s, hs, hc⟩
  exact ⟨s, congrArg pOld hs, congrArg pCore hc⟩

/-- A genuine shared-edge contact produces an injective tagged
standard-picture ancestor map whenever the gluing embedding
preserves and reflects wagon equivalence. -/
theorem wagonSharedEdgeContact_glue_injective
    (old : I → Shared → Old)
    (core : I → Shared → Core)
    (hPreserve : ∀ i s t,
      old i s = old i t → core i s = core i t)
    (hReflect : ∀ i s t,
      core i s = core i t → old i s = old i t)
    (i : I) :
    Function.Injective
      (gluedStandardNode
        (wagonContactGlue (wagonSharedEdgeContact old core)) i) := by
  apply gluedStandardNode_injective_of_contacts
    (wagonSharedEdgeContact old core)
  · intro j a c d hc hd
    exact wagonSharedEdgeContact_unique old core hPreserve j a c d hc hd
  · intro j a b c ha hb
    exact wagonSharedEdgeContact_reflect old core hReflect j a b c ha hb

/-- Contact with the parent ancestor is witnessed by the same edge.
This allows a private child to have a shared parent. -/
theorem wagonSharedEdgeContact_glue_parent
    (old : I → Shared → Old)
    (core : I → Shared → Core)
    (hPreserve : ∀ i s t,
      old i s = old i t → core i s = core i t)
    {OldParent : Type w} {CoreParent : Type x}
    (pOld : Old → OldParent) (pCore : Core → CoreParent)
    (hParentPreserve : ∀ i s t,
      pOld (old i s) = pOld (old i t) →
      pCore (core i s) = pCore (core i t))
    (i : I) (a : Old) (c : Core)
    (h : wagonContactGlue (wagonSharedEdgeContact old core) i a = some c) :
    wagonContactGlue
        (wagonSharedEdgeContact
          (fun j s => pOld (old j s))
          (fun j s => pCore (core j s)))
        i (pOld a) = some (pCore c) := by
  have hOldUnique : ∀ j b x y,
      wagonSharedEdgeContact old core j b x →
      wagonSharedEdgeContact old core j b y → x = y := by
    intro j b x y hx hy
    exact wagonSharedEdgeContact_unique old core hPreserve j b x y hx hy
  have hParentUnique : ∀ j b x y,
      wagonSharedEdgeContact
          (fun k s => pOld (old k s))
          (fun k s => pCore (core k s)) j b x →
      wagonSharedEdgeContact
          (fun k s => pOld (old k s))
          (fun k s => pCore (core k s)) j b y → x = y := by
    intro j b x y hx hy
    exact wagonSharedEdgeContact_unique
      (fun k s => pOld (old k s))
      (fun k s => pCore (core k s))
      hParentPreserve j b x y hx hy
  apply (wagonContactGlue_eq_some_iff
    (wagonSharedEdgeContact
      (fun j s => pOld (old j s))
      (fun j s => pCore (core j s)))
    hParentUnique i (pOld a) (pCore c)).mpr
  exact wagonSharedEdgeContact_parent old core pOld pCore i a c
    ((wagonContactGlue_eq_some_iff
      (wagonSharedEdgeContact old core)
      hOldUnique i a c).mp h)

end StructuralRamsey.Girth
