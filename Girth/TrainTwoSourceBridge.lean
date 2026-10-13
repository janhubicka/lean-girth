import Girth.TrainGeneratedTagParentBound

/-!
# A genuine two-source order-one bridge implies the generated train parameter

The order-one lemma in the circulation proof compares two DISTINCT source
labels, not two different generated child tags as such. The sources are
actual standard-picture indices and the witness core. A parent-contact
edge in the core supplies the latter source.

The only problematic apparent exception is when both competing generated
children have old representatives in ONE standard picture. Parent contact
injectivity places those representatives below the same old parent; the
old allowed-part parameter then forces equality at a forbidden vertex.
Consequently this same-source case needs NO witness bridge.

This file makes that argument explicit. Its conclusion remains conditional:
the two-source bridge must still be derived from acceptable order-one
cycles of the actual physical witness, and all the abstract carrier and
parent-contact assumptions must be instantiated in the generated picture.
No system-Girth or final Ramsey assertion is made here.
-/

namespace StructuralRamsey.Girth

universe v
variable {W I Old OldP Core CoreP : Type v}

/-- A source-label version of the order-one bridge.
The first source is a fixed standard copy i with old child u incident
at x and an ancestor contacting core parent p. The SECOND source is
either a real core child below p incident at x, or an old child of a
DIFFERENT standard copy j incident at x with an ancestor contacting p.

Only with such a distinct second source must the witness supply an old
child v of the same parent as u which genuinely contacts a core child
through x. In particular, this does NOT require a bridge when i is the
sole incident source label. -/
def ParentCoreTwoSourceBridge
    (oldCarrier : I → Old → Set W)
    (oldParent : Old → OldP)
    (coreCarrier : Core → Set W)
    (coreParent : Core → CoreP)
    (glueChild : I → Old → Option Core)
    (glueParent : I → OldP → Option CoreP)
    (coreVertices allowed : Set W) : Prop :=
  ∀ (x : W) (p : CoreP) (i : I) (u : Old),
    x ∈ coreVertices →
    x ∉ allowed →
    glueParent i (oldParent u) = some p →
    x ∈ oldCarrier i u →
    ((∃ c : Core, coreParent c = p ∧ x ∈ coreCarrier c) ∨
      (∃ j : I, ∃ v : Old,
        j ≠ i ∧
        glueParent j (oldParent v) = some p ∧
        x ∈ oldCarrier j v)) →
    ∃ (v : Old) (c : Core),
      oldParent v = oldParent u ∧
      x ∈ oldCarrier i v ∧
      glueChild i v = some c ∧
      x ∈ coreCarrier c

/-- Replace the tag-level pairwise bridge by its faithful source-label
version. If the competitor comes from the same old standard copy, old
parent-contact injectivity and the old forbidden-vertex parameter
already contradict the assumption that the generated tags differ. -/
theorem parentCoreCompetingBridge_of_twoSource
    (oldCarrier : I → Old → Set W)
    (oldParent : Old → OldP)
    (coreCarrier : Core → Set W)
    (coreParent : Core → CoreP)
    (glueChild : I → Old → Option Core)
    (glueParent : I → OldP → Option CoreP)
    (coreVertices allowed : Set W)
    (hOld : ∀ i : I,
      TrainParentIntersectionBound (oldCarrier i) oldParent allowed)
    (hParentInjective : ∀ i a b p,
      glueParent i a = some p →
      glueParent i b = some p → a = b)
    (hTwoSource : ParentCoreTwoSourceBridge oldCarrier oldParent
      coreCarrier coreParent glueChild glueParent coreVertices allowed) :
    ParentCoreCompetingBridge oldCarrier oldParent coreCarrier coreParent
      glueChild glueParent coreVertices allowed := by
  intro x p t s hxCore hxForbidden hne _ht hs i u htu hpu hux
  apply hTwoSource x p i u hxCore hxForbidden hpu hux
  rcases hs with ⟨c, _, hcp, hcx⟩ | ⟨j, v, hsv, hpv, hvx⟩
  · exact Or.inl ⟨c, hcp, hcx⟩
  · by_cases hji : j = i
    · subst j
      have hParents : oldParent u = oldParent v :=
        hParentInjective i (oldParent u) (oldParent v) p hpu hpv
      have huv : u = v := by
        by_contra hneOld
        exact hxForbidden (hOld i hneOld hParents ⟨hux, hvx⟩)
      have hts : t = s := by
        calc
          t = gluedStandardNode glueChild i u := htu
          _ = gluedStandardNode glueChild i v :=
            congrArg (gluedStandardNode glueChild i) huv
          _ = s := hsv.symm
      exact False.elim (hne hts)
    · exact Or.inr ⟨j, v, hji, hpv, hvx⟩

/-- Full generated-tag parent intersection bound, using only a
TWO-SOURCE witness bridge. All hypotheses except hTwoSource concern
the previously established old/core parent parameters and actual
picture ownership/contact geometry.

This is a faithful conditional interface for the manuscript's
two-label argument; the derivation of hTwoSource from the actual
witness system-Girth and physical A-support remains open. -/
theorem generatedTaggedWagon_parentIntersectionBound_of_twoSource
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
    (hCoreCarrier : ∀ c : Core, coreCarrier c ⊆ coreVertices)
    (hOffCoreIndex : ∀ i j u v (x : W),
      x ∉ coreVertices →
      x ∈ oldCarrier i u →
      x ∈ oldCarrier j v → i = j)
    (hParentInjective : ∀ i a b p,
      glueParent i a = some p →
      glueParent i b = some p → a = b)
    (hTwoSource : ParentCoreTwoSourceBridge oldCarrier oldParent
      coreCarrier coreParent glueChild glueParent coreVertices allowed)
    (hCompat : ∀ i u c,
      glueChild i u = some c →
      glueParent i (oldParent u) = some (coreParent c)) :
    TrainParentIntersectionBound
      (GeneratedTaggedWagonCarrier oldCarrier coreCarrier glueChild)
      (gluedWagonParent glueChild glueParent coreParent oldParent)
      allowed := by
  exact generatedTaggedWagon_parentIntersectionBound
    oldCarrier oldParent coreCarrier coreParent glueChild glueParent
    coreVertices allowed hOld hCore hCoreCarrier hOffCoreIndex
    hParentInjective
    (parentCoreCompetingBridge_of_twoSource
      oldCarrier oldParent coreCarrier coreParent glueChild glueParent
      coreVertices allowed hOld hParentInjective hTwoSource)
    hCompat

end StructuralRamsey.Girth
