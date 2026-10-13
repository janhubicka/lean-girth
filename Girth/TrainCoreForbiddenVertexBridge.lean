import Girth.TrainParameterRestriction
import Girth.TrainWagonNodeGluing

/-!
# Core-vertex owner uniqueness from the order-one witness bridge

The difficult part of the generated picture train's allowed-part
parent parameter occurs at a vertex x in the witness core. A child
of an old standard picture may meet x even when its generated
wagon has no actual H-edge through x.

The witness's order-one bridge supplies a different child v of
the SAME old parent, incident with x, and genuinely contacted
with a core child c incident with x. Outside the allowed parts,
the old sibling-intersection bound forces v to be the original
child u. Thus u itself contacts c. Since the core also satisfies
its forbidden-vertex child-uniqueness bound, all represented
children of one core parent meeting x become the SAME core child.

This is a short, exact owner argument independent of pruning
and of spurious equality of different labelled wagon carriers.
It does NOT claim the order-one witness supplies the bridge:
that geometric A2/system-girth implication is still to be proved.
-/

namespace StructuralRamsey.Girth

universe v
variable {W I Old OldP Core CoreP : Type v}

/-- The usable form of an order-one bridge: from an old child
incident at a core vertex x under a shared core parent p,
find a (possibly different) old child of the SAME parent,
incident at x, whose image contacts an actual core child
also incident at x. -/
def ParentCoreVertexBridge
    (oldCarrier : I → Old → Set W)
    (oldParent : Old → OldP)
    (coreCarrier : Core → Set W)
    (glueChild : I → Old → Option Core)
    (glueParent : I → OldP → Option CoreP)
    (coreVertices : Set W) : Prop :=
  ∀ (i : I) (u : Old) (x : W) (p : CoreP),
    x ∈ coreVertices →
    x ∈ oldCarrier i u →
    glueParent i (oldParent u) = some p →
    ∃ (v : Old) (c : Core),
      oldParent v = oldParent u ∧
      x ∈ oldCarrier i v ∧
      glueChild i v = some c ∧
      x ∈ coreCarrier c

/-- The old parent bound and genuine bridge force the ORIGINAL
old child to contact a core child incident at x. The core
parent is exactly the prescribed parent p, by compatibility
of the gluing maps with the unary train parents. -/
theorem parentCoreBridge_forbidden_oldChild_is_shared
    (oldCarrier : I → Old → Set W)
    (oldParent : Old → OldP)
    (coreCarrier : Core → Set W)
    (coreParent : Core → CoreP)
    (glueChild : I → Old → Option Core)
    (glueParent : I → OldP → Option CoreP)
    (coreVertices allowed : Set W)
    (hOld : ∀ i : I,
      TrainParentIntersectionBound (oldCarrier i) oldParent allowed)
    (hBridge : ParentCoreVertexBridge oldCarrier oldParent
      coreCarrier glueChild glueParent coreVertices)
    (hParent : ∀ i u c,
      glueChild i u = some c →
      glueParent i (oldParent u) = some (coreParent c))
    (i : I) (u : Old) (x : W) (p : CoreP)
    (hxCore : x ∈ coreVertices)
    (hxForbidden : x ∉ allowed)
    (hu : x ∈ oldCarrier i u)
    (hp : glueParent i (oldParent u) = some p) :
    ∃ c : Core,
      glueChild i u = some c ∧
      coreParent c = p ∧
      x ∈ coreCarrier c := by
  obtain ⟨v, c, hvParent, hvx, hvGlue, hcx⟩ :=
    hBridge i u x p hxCore hu hp
  have huv : u = v := by
    by_contra hne
    have hxAllowed : x ∈ allowed :=
      hOld i hne hvParent.symm ⟨hu, hvx⟩
    exact hxForbidden hxAllowed
  have hcGlue : glueChild i u = some c := by
    simpa only [huv] using hvGlue
  have hcp : coreParent c = p :=
    Option.some.inj ((hParent i u c hcGlue).symm.trans hp)
  exact ⟨c, hcGlue, hcp, hcx⟩

/-- Any TWO old-standard children meeting a forbidden core
vertex below a common contacted core parent must both glue
to the SAME genuine core child. Their standard indices may
differ; there is no required common full standard picture. -/
theorem parentCoreBridge_two_oldChildren_same_core
    (oldCarrier : I → Old → Set W)
    (oldParent : Old → OldP)
    (coreCarrier : Core → Set W)
    (coreParent : Core → CoreP)
    (glueChild : I → Old → Option Core)
    (glueParent : I → OldP → Option CoreP)
    (coreVertices allowed : Set W)
    (hOld : ∀ i : I,
      TrainParentIntersectionBound (oldCarrier i) oldParent allowed)
    (hCore :
      TrainParentIntersectionBound coreCarrier coreParent allowed)
    (hBridge : ParentCoreVertexBridge oldCarrier oldParent
      coreCarrier glueChild glueParent coreVertices)
    (hParent : ∀ i u c,
      glueChild i u = some c →
      glueParent i (oldParent u) = some (coreParent c))
    (i j : I) (u v : Old) (x : W) (p : CoreP)
    (hxCore : x ∈ coreVertices)
    (hxForbidden : x ∉ allowed)
    (hu : x ∈ oldCarrier i u)
    (hv : x ∈ oldCarrier j v)
    (hpu : glueParent i (oldParent u) = some p)
    (hpv : glueParent j (oldParent v) = some p) :
    ∃ c : Core,
      glueChild i u = some c ∧
      glueChild j v = some c ∧
      coreParent c = p ∧
      x ∈ coreCarrier c := by
  obtain ⟨c, huc, hcp, hcx⟩ :=
    parentCoreBridge_forbidden_oldChild_is_shared
      oldCarrier oldParent coreCarrier coreParent
      glueChild glueParent coreVertices allowed
      hOld hBridge hParent i u x p hxCore hxForbidden hu hpu
  obtain ⟨d, hvd, hdp, hdx⟩ :=
    parentCoreBridge_forbidden_oldChild_is_shared
      oldCarrier oldParent coreCarrier coreParent
      glueChild glueParent coreVertices allowed
      hOld hBridge hParent j v x p hxCore hxForbidden hv hpv
  have hcd : c = d := by
    by_contra hne
    have hAllowed : x ∈ allowed :=
      hCore hne (hcp.trans hdp.symm) ⟨hcx, hdx⟩
    exact hxForbidden hAllowed
  refine ⟨c, huc, ?_, hcp, hcx⟩
  simpa only [← hcd] using hvd

/-- An incident generated child is either a genuine core child
or the image of a genuine old standard child at a shared core
parent. The vertex x and parent p remain explicit. -/
def ParentCoreIncidentTag
    (oldCarrier : I → Old → Set W)
    (oldParent : Old → OldP)
    (coreCarrier : Core → Set W)
    (coreParent : Core → CoreP)
    (glueChild : I → Old → Option Core)
    (glueParent : I → OldP → Option CoreP)
    (x : W) (p : CoreP)
    (tag : Core ⊕ (I × Old)) : Prop :=
  (∃ c : Core,
      tag = Sum.inl c ∧
      coreParent c = p ∧ x ∈ coreCarrier c)
    ∨
  (∃ i : I, ∃ u : Old,
      tag = gluedStandardNode glueChild i u ∧
      glueParent i (oldParent u) = some p ∧
      x ∈ oldCarrier i u)

/-- Outside the allowed parts, EVERY generated child incident at
a genuine core vertex below a common core parent has a core-child
representative incident at exactly that vertex. -/
theorem parentCoreIncidentTag_has_core_representative
    (oldCarrier : I → Old → Set W)
    (oldParent : Old → OldP)
    (coreCarrier : Core → Set W)
    (coreParent : Core → CoreP)
    (glueChild : I → Old → Option Core)
    (glueParent : I → OldP → Option CoreP)
    (coreVertices allowed : Set W)
    (hOld : ∀ i : I,
      TrainParentIntersectionBound (oldCarrier i) oldParent allowed)
    (hBridge : ParentCoreVertexBridge oldCarrier oldParent
      coreCarrier glueChild glueParent coreVertices)
    (hParent : ∀ i u c,
      glueChild i u = some c →
      glueParent i (oldParent u) = some (coreParent c))
    (x : W) (p : CoreP)
    (hxCore : x ∈ coreVertices)
    (hxForbidden : x ∉ allowed)
    (tag : Core ⊕ (I × Old))
    (hTag : ParentCoreIncidentTag
      oldCarrier oldParent coreCarrier coreParent
      glueChild glueParent x p tag) :
    ∃ c : Core,
      tag = Sum.inl c ∧
      coreParent c = p ∧
      x ∈ coreCarrier c := by
  rcases hTag with ⟨c, htag, hp, hcx⟩ |
    ⟨i, u, htag, hp, hux⟩
  · exact ⟨c, htag, hp, hcx⟩
  · obtain ⟨c, huc, hcp, hcx⟩ :=
      parentCoreBridge_forbidden_oldChild_is_shared
        oldCarrier oldParent coreCarrier coreParent
        glueChild glueParent coreVertices allowed
        hOld hBridge hParent i u x p
        hxCore hxForbidden hux hp
    refine ⟨c, ?_, hcp, hcx⟩
    calc
      tag = gluedStandardNode glueChild i u := htag
      _ = Sum.inl c := by simp [gluedStandardNode, huc]

/-- The forbidden-vertex child-incidence fibre below EACH
generated core parent is a SUBSINGLETON. This is the exact
local-owner consequence of the order-one witness bridge. -/
theorem parentCoreIncidentTag_unique_of_bridge
    (oldCarrier : I → Old → Set W)
    (oldParent : Old → OldP)
    (coreCarrier : Core → Set W)
    (coreParent : Core → CoreP)
    (glueChild : I → Old → Option Core)
    (glueParent : I → OldP → Option CoreP)
    (coreVertices allowed : Set W)
    (hOld : ∀ i : I,
      TrainParentIntersectionBound (oldCarrier i) oldParent allowed)
    (hCore :
      TrainParentIntersectionBound coreCarrier coreParent allowed)
    (hBridge : ParentCoreVertexBridge oldCarrier oldParent
      coreCarrier glueChild glueParent coreVertices)
    (hParent : ∀ i u c,
      glueChild i u = some c →
      glueParent i (oldParent u) = some (coreParent c))
    (x : W) (p : CoreP)
    (hxCore : x ∈ coreVertices)
    (hxForbidden : x ∉ allowed)
    (t s : Core ⊕ (I × Old))
    (ht : ParentCoreIncidentTag
      oldCarrier oldParent coreCarrier coreParent
      glueChild glueParent x p t)
    (hs : ParentCoreIncidentTag
      oldCarrier oldParent coreCarrier coreParent
      glueChild glueParent x p s) :
    t = s := by
  obtain ⟨c, htc, hpc, hxc⟩ :=
    parentCoreIncidentTag_has_core_representative
      oldCarrier oldParent coreCarrier coreParent
      glueChild glueParent coreVertices allowed
      hOld hBridge hParent x p hxCore hxForbidden t ht
  obtain ⟨d, hsd, hpd, hxd⟩ :=
    parentCoreIncidentTag_has_core_representative
      oldCarrier oldParent coreCarrier coreParent
      glueChild glueParent coreVertices allowed
      hOld hBridge hParent x p hxCore hxForbidden s hs
  have hcd : c = d := by
    by_contra hne
    have hxAllowed : x ∈ allowed :=
      hCore hne (hpc.trans hpd.symm) ⟨hxc, hxd⟩
    exact hxForbidden hxAllowed
  calc
    t = Sum.inl c := htc
    _ = Sum.inl d := congrArg Sum.inl hcd
    _ = s := hsd.symm

end StructuralRamsey.Girth
