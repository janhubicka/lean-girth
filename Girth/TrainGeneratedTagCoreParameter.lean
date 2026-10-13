import Girth.TrainCoreForbiddenVertexBridge

/-!
# Generated wagon tags inherit the forbidden-core-vertex owner bound

The geometric proof of the output parent parameter is most transparent
after representing each generated wagon by a shared core ancestor or
an indexed private old ancestor. Its physical carrier is the union
of the actual core and old-child carriers bearing that tag.

For any vertex x in the witness core but outside the allowed parts,
the order-one witness bridge ensures that every child tag incident
with x below a shared core parent is actually a core child tag
incident with x. The core parameter therefore forces uniqueness.

This verifies the ENTIRE shared-parent/core-vertex case of the
generated train parameter argument, subject only to the true
order-one bridge and old/core parameter hypotheses.

Off-core vertices and private parent labels are treated separately.
This module does not construct the witness bridges from system-Girth
A1--A3 or establish the complete generated picture parameter bound.
-/

namespace StructuralRamsey.Girth

universe v
variable {W I Old OldP Core CoreP : Type v}

/-- Full vertex carrier of one generated wagon ancestor tag,
including the core edge carriers and every standard old wagon
whose ancestor is identified with this tag. -/
def GeneratedTaggedWagonCarrier
    (oldCarrier : I → Old → Set W)
    (coreCarrier : Core → Set W)
    (glueChild : I → Old → Option Core)
    (tag : Core ⊕ (I × Old)) : Set W :=
  {x |
    (∃ c : Core, tag = Sum.inl c ∧ x ∈ coreCarrier c) ∨
    (∃ i : I, ∃ u : Old,
      tag = gluedStandardNode glueChild i u ∧
      x ∈ oldCarrier i u)}

/-- A generated child tag incident at a core vertex under a
shared core-parent label satisfies the core-incidence condition
used by the witness bridge proof. -/
theorem generatedTaggedWagon_coreParent_incidence
    (oldCarrier : I → Old → Set W)
    (oldParent : Old → OldP)
    (coreCarrier : Core → Set W)
    (coreParent : Core → CoreP)
    (glueChild : I → Old → Option Core)
    (glueParent : I → OldP → Option CoreP)
    (hCompat : ∀ i u c,
      glueChild i u = some c →
      glueParent i (oldParent u) = some (coreParent c))
    (x : W) (p : CoreP) (tag : Core ⊕ (I × Old))
    (hx : x ∈ GeneratedTaggedWagonCarrier
      oldCarrier coreCarrier glueChild tag)
    (hp : gluedWagonParent glueChild glueParent
      coreParent oldParent tag = Sum.inl p) :
    ParentCoreIncidentTag oldCarrier oldParent
      coreCarrier coreParent glueChild glueParent x p tag := by
  rcases hx with ⟨c, htag, hcx⟩ |
    ⟨i, u, htag, hux⟩
  · left
    have hcp : coreParent c = p := by
      have h := hp
      rw [htag] at h
      exact Sum.inl.inj h
    exact ⟨c, htag, hcp, hcx⟩
  · right
    have hpar :
        gluedStandardNode glueParent i (oldParent u) =
          Sum.inl p := by
      calc
        gluedStandardNode glueParent i (oldParent u) =
          gluedWagonParent glueChild glueParent
            coreParent oldParent (gluedStandardNode glueChild i u) :=
          (gluedWagonParent_standard
            glueChild glueParent coreParent oldParent hCompat i u).symm
        _ = gluedWagonParent glueChild glueParent
              coreParent oldParent tag := congrArg _ htag.symm
        _ = Sum.inl p := hp
    have hContact : glueParent i (oldParent u) = some p :=
      (gluedStandardNode_eq_core_iff
        glueParent i (oldParent u) p).mp hpar
    exact ⟨i, u, htag, hContact, hux⟩

/-- The actual generated child CARRIERS obey the forbidden-vertex
owner bound whenever the shared parent belongs to the core and the
vertex is in the witness core.

This is the central local consequence of the order-one witness bridge,
rather than an assumed injection of all output child labels into
one source parent fibre. -/
theorem generatedTaggedWagon_unique_at_forbidden_coreParent
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
    (hCompat : ∀ i u c,
      glueChild i u = some c →
      glueParent i (oldParent u) = some (coreParent c))
    (x : W) (p : CoreP)
    (hxCore : x ∈ coreVertices) (hxForbidden : x ∉ allowed)
    (a b : Core ⊕ (I × Old))
    (ha : x ∈ GeneratedTaggedWagonCarrier
      oldCarrier coreCarrier glueChild a)
    (hb : x ∈ GeneratedTaggedWagonCarrier
      oldCarrier coreCarrier glueChild b)
    (hpa : gluedWagonParent glueChild glueParent
      coreParent oldParent a = Sum.inl p)
    (hpb : gluedWagonParent glueChild glueParent
      coreParent oldParent b = Sum.inl p) :
    a = b := by
  have hia : ParentCoreIncidentTag oldCarrier oldParent
      coreCarrier coreParent glueChild glueParent x p a :=
    generatedTaggedWagon_coreParent_incidence
      oldCarrier oldParent coreCarrier coreParent
      glueChild glueParent hCompat x p a ha hpa
  have hib : ParentCoreIncidentTag oldCarrier oldParent
      coreCarrier coreParent glueChild glueParent x p b :=
    generatedTaggedWagon_coreParent_incidence
      oldCarrier oldParent coreCarrier coreParent
      glueChild glueParent hCompat x p b hb hpb
  exact parentCoreIncidentTag_unique_of_bridge
    oldCarrier oldParent coreCarrier coreParent
    glueChild glueParent coreVertices allowed
    hOld hCore hBridge hCompat x p
    hxCore hxForbidden a b hia hib

end StructuralRamsey.Girth
