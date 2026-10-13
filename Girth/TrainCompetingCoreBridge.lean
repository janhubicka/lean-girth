import Girth.TrainGeneratedTagCoreParameter

/-!
# Competing-label order-one bridges and core forbidden-child uniqueness

The circulation order-one lemma is PAIRWISE: if two DISTINCT
designated/one-edge labels both contain x and meet a wagon X,
both admit an X-edge through x. It does NOT supply a bridge to a
single isolated label.

Represent that exact quantifier by requiring old-child bridges
only in the presence of a second DISTINCT generated child tag
incident with the same core vertex and same shared core parent.

Outside the allowed parts, the old parameter forces every original
child to equal its bridge child; the core parameter then forbids
the two generated child tags from being distinct. Unlike the
stronger singleton bridge hypothesis used in earlier candidate
#455, this interface can be derived from a real pairwise
two-label witness argument, once actual label/child ownership
is connected to the generated wagon presentation.
-/

namespace StructuralRamsey.Girth

universe v
variable {W I Old OldP Core CoreP : Type v}

/-- The bridge hypothesis applies only when TWO DISTINCT generated
child tags are incident at the same core vertex x below the SAME
shared core parent p. Its conclusion for an old-standard child
is an actual contacted core child, possibly through a different
old child of the same old parent. -/
def ParentCoreCompetingBridge
    (oldCarrier : I → Old → Set W)
    (oldParent : Old → OldP)
    (coreCarrier : Core → Set W)
    (coreParent : Core → CoreP)
    (glueChild : I → Old → Option Core)
    (glueParent : I → OldP → Option CoreP)
    (coreVertices allowed : Set W) : Prop :=
  ∀ (x : W) (p : CoreP)
    (t s : Core ⊕ (I × Old)),
    x ∈ coreVertices →
    x ∉ allowed →
    t ≠ s →
    ParentCoreIncidentTag oldCarrier oldParent
      coreCarrier coreParent glueChild glueParent x p t →
    ParentCoreIncidentTag oldCarrier oldParent
      coreCarrier coreParent glueChild glueParent x p s →
    ∀ (i : I) (u : Old),
      t = gluedStandardNode glueChild i u →
      glueParent i (oldParent u) = some p →
      x ∈ oldCarrier i u →
      ∃ (v : Old) (c : Core),
        oldParent v = oldParent u ∧
        x ∈ oldCarrier i v ∧
        glueChild i v = some c ∧
        x ∈ coreCarrier c

/-- In the presence of a distinct competing child, the old
parameter forces the original old child itself to be core-shared.
Consequently its generated tag has a genuine core-child
representative incident at x and under the correct parent p. -/
theorem competingBridge_forces_core_child
    (oldCarrier : I → Old → Set W)
    (oldParent : Old → OldP)
    (coreCarrier : Core → Set W)
    (coreParent : Core → CoreP)
    (glueChild : I → Old → Option Core)
    (glueParent : I → OldP → Option CoreP)
    (coreVertices allowed : Set W)
    (hOld : ∀ i : I,
      TrainParentIntersectionBound (oldCarrier i) oldParent allowed)
    (hBridge : ParentCoreCompetingBridge
      oldCarrier oldParent coreCarrier coreParent
      glueChild glueParent coreVertices allowed)
    (hParent : ∀ i u c,
      glueChild i u = some c →
      glueParent i (oldParent u) = some (coreParent c))
    (x : W) (p : CoreP)
    (hxCore : x ∈ coreVertices)
    (hxForbidden : x ∉ allowed)
    (t s : Core ⊕ (I × Old))
    (hne : t ≠ s)
    (ht : ParentCoreIncidentTag
      oldCarrier oldParent coreCarrier coreParent
      glueChild glueParent x p t)
    (hs : ParentCoreIncidentTag
      oldCarrier oldParent coreCarrier coreParent
      glueChild glueParent x p s) :
    ∃ c : Core,
      t = Sum.inl c ∧ coreParent c = p ∧
      x ∈ coreCarrier c := by
  rcases ht with ⟨c, htc, hcp, hcx⟩ |
    ⟨i, u, htu, hpu, hux⟩
  · exact ⟨c, htc, hcp, hcx⟩
  · have ht : ParentCoreIncidentTag oldCarrier oldParent
        coreCarrier coreParent glueChild glueParent x p t :=
      Or.inr ⟨i, u, htu, hpu, hux⟩
    obtain ⟨v, c, hvParent, hvx, hvGlue, hcx⟩ :=
      hBridge x p t s hxCore hxForbidden hne ht hs i u htu hpu hux
    have huv : u = v := by
      by_contra hneOld
      have hAllowed : x ∈ allowed :=
        hOld i hneOld hvParent.symm ⟨hux, hvx⟩
      exact hxForbidden hAllowed
    have huc : glueChild i u = some c := by
      simpa only [huv] using hvGlue
    have hcp : coreParent c = p :=
      Option.some.inj ((hParent i u c huc).symm.trans hpu)
    refine ⟨c, ?_, hcp, hcx⟩
    calc
      t = gluedStandardNode glueChild i u := htu
      _ = Sum.inl c := by simp [gluedStandardNode, huc]

/-- The witness's PAIRWISE order-one bridge is sufficient for
unique forbidden-vertex child ownership under a core parent.
No isolated-child bridge is assumed or used. -/
theorem competingBridge_coreIncidentTags_unique
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
    (hBridge : ParentCoreCompetingBridge
      oldCarrier oldParent coreCarrier coreParent
      glueChild glueParent coreVertices allowed)
    (hParent : ∀ i u c,
      glueChild i u = some c →
      glueParent i (oldParent u) = some (coreParent c))
    (x : W) (p : CoreP)
    (hxCore : x ∈ coreVertices)
    (hxForbidden : x ∉ allowed)
    (t s : Core ⊕ (I × Old))
    (ht : ParentCoreIncidentTag oldCarrier oldParent
      coreCarrier coreParent glueChild glueParent x p t)
    (hs : ParentCoreIncidentTag oldCarrier oldParent
      coreCarrier coreParent glueChild glueParent x p s) :
    t = s := by
  by_contra hne
  obtain ⟨c, htc, hpc, hxc⟩ :=
    competingBridge_forces_core_child
      oldCarrier oldParent coreCarrier coreParent
      glueChild glueParent coreVertices allowed
      hOld hBridge hParent x p hxCore hxForbidden
      t s hne ht hs
  obtain ⟨d, hsd, hpd, hxd⟩ :=
    competingBridge_forces_core_child
      oldCarrier oldParent coreCarrier coreParent
      glueChild glueParent coreVertices allowed
      hOld hBridge hParent x p hxCore hxForbidden
      s t hne.symm hs ht
  have hcd : c = d := by
    by_contra hcne
    have hAllowed : x ∈ allowed :=
      hCore hcne (hpc.trans hpd.symm) ⟨hxc, hxd⟩
    exact hxForbidden hAllowed
  exact hne (htc.trans ((congrArg Sum.inl hcd).trans hsd.symm))

/-- Apply pairwise competition only AFTER two generated child
tags are incident with a forbidden core vertex under the same
core parent. This is precisely the form required by the paper. -/
theorem generatedTaggedWagon_coreParent_unique_of_pairwiseBridge
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
    (hBridge : ParentCoreCompetingBridge
      oldCarrier oldParent coreCarrier coreParent
      glueChild glueParent coreVertices allowed)
    (hParent : ∀ i u c,
      glueChild i u = some c →
      glueParent i (oldParent u) = some (coreParent c))
    (x : W) (p : CoreP)
    (hxCore : x ∈ coreVertices)
    (hxForbidden : x ∉ allowed)
    (t s : Core ⊕ (I × Old))
    (ht : x ∈ GeneratedTaggedWagonCarrier
      oldCarrier coreCarrier glueChild t)
    (hs : x ∈ GeneratedTaggedWagonCarrier
      oldCarrier coreCarrier glueChild s)
    (hpt : gluedWagonParent glueChild glueParent
      coreParent oldParent t = Sum.inl p)
    (hps : gluedWagonParent glueChild glueParent
      coreParent oldParent s = Sum.inl p) :
    t = s := by
  have hit : ParentCoreIncidentTag oldCarrier oldParent
      coreCarrier coreParent glueChild glueParent x p t :=
    generatedTaggedWagon_coreParent_incidence
      oldCarrier oldParent coreCarrier coreParent
      glueChild glueParent hParent x p t ht hpt
  have his : ParentCoreIncidentTag oldCarrier oldParent
      coreCarrier coreParent glueChild glueParent x p s :=
    generatedTaggedWagon_coreParent_incidence
      oldCarrier oldParent coreCarrier coreParent
      glueChild glueParent hParent x p s hs hps
  exact competingBridge_coreIncidentTags_unique
    oldCarrier oldParent coreCarrier coreParent
    glueChild glueParent coreVertices allowed
    hOld hCore hBridge hParent
    x p hxCore hxForbidden t s hit his

end StructuralRamsey.Girth
