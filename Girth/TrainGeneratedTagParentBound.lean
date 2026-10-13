import Girth.TrainGeneratedTagCoreParameter

/-!
# Full generated-wagon parent parameter from the witness bridge

Given genuine core/standard wagon incidence and tagged gluing,
the generated child carriers satisfy the SAME forbidden-vertex
sibling-intersection parameter as the old/core trains, provided:

* old/core sibling child carriers obey that parameter;
* core edges lie in the core vertex carrier;
* incident standard edges outside the core have one standard index;
* shared parent contacts reflect old parent labels within each copy;
* unary child/parent gluing maps commute;
* the witness gives an order-one bridge for each old child at a
  forbidden core vertex under a shared parent.

This splits into precisely three elementary cases:
(1) private generated parent: old standard parameter;
(2) shared parent at off-core vertex: unique standard owner,
    parent-contact reflection, then old standard parameter;
(3) shared parent at core vertex: the witness bridge and core
    forbidden-child uniqueness (TrainGeneratedTagCoreParameter).

The difficult geometric assumption is the ORDER-ONE WITNESS BRIDGE.
The proof does not infer it from A1--A3/system-Girth and makes no
claim about the global recursive Ramsey witness.
-/

namespace StructuralRamsey.Girth

universe v
variable {W I Old OldP Core CoreP : Type v}

/-- At a vertex outside the witness core, every generated wagon
with that vertex in its complete carrier is represented by
an incident edge of one actual old standard wagon. -/
theorem generatedTag_offCore_has_oldOwner
    (oldCarrier : I → Old → Set W)
    (coreCarrier : Core → Set W)
    (glueChild : I → Old → Option Core)
    (coreVertices : Set W)
    (hCoreCarrier : ∀ c : Core, coreCarrier c ⊆ coreVertices)
    (x : W) (hxOutside : x ∉ coreVertices)
    (tag : Core ⊕ (I × Old))
    (hx : x ∈ GeneratedTaggedWagonCarrier
      oldCarrier coreCarrier glueChild tag) :
    ∃ i : I, ∃ u : Old,
      tag = gluedStandardNode glueChild i u ∧
      x ∈ oldCarrier i u := by
  rcases hx with ⟨c, _, hcx⟩ | ⟨i, u, htag, hux⟩
  · exact False.elim (hxOutside (hCoreCarrier c hcx))
  · exact ⟨i, u, htag, hux⟩

/-- If a standard old child represents a generated child below a
shared core parent p, its OLD parent genuinely contacts p. -/
theorem generatedTag_sharedParent_oldContact
    (oldParent : Old → OldP)
    (coreParent : Core → CoreP)
    (glueChild : I → Old → Option Core)
    (glueParent : I → OldP → Option CoreP)
    (hCompat : ∀ i u c,
      glueChild i u = some c →
      glueParent i (oldParent u) = some (coreParent c))
    (i : I) (u : Old) (p : CoreP)
    (tag : Core ⊕ (I × Old))
    (htag : tag = gluedStandardNode glueChild i u)
    (hp : gluedWagonParent glueChild glueParent
      coreParent oldParent tag = Sum.inl p) :
    glueParent i (oldParent u) = some p := by
  have hpar :
      gluedStandardNode glueParent i (oldParent u) =
        Sum.inl p := by
    calc
      gluedStandardNode glueParent i (oldParent u) =
        gluedWagonParent glueChild glueParent
          coreParent oldParent (gluedStandardNode glueChild i u) :=
        (gluedWagonParent_standard
          glueChild glueParent coreParent oldParent
          hCompat i u).symm
      _ = gluedWagonParent glueChild glueParent
            coreParent oldParent tag := congrArg _ htag.symm
      _ = Sum.inl p := hp
  exact (gluedStandardNode_eq_core_iff
    glueParent i (oldParent u) p).mp hpar

/-- A forbidden off-core vertex has at most one generated child
below any shared parent: both child carriers must belong to one
standard copy; parent-contact reflection locates one OLD parent,
and the old sibling parameter forces one old child. -/
theorem generatedTag_forbidden_offCore_sharedParent_unique
    (oldCarrier : I → Old → Set W)
    (oldParent : Old → OldP)
    (coreCarrier : Core → Set W)
    (coreParent : Core → CoreP)
    (glueChild : I → Old → Option Core)
    (glueParent : I → OldP → Option CoreP)
    (coreVertices allowed : Set W)
    (hOld : ∀ i : I,
      TrainParentIntersectionBound (oldCarrier i) oldParent allowed)
    (hCoreCarrier : ∀ c : Core, coreCarrier c ⊆ coreVertices)
    (hOffCoreIndex : ∀ i j u v (x : W),
      x ∉ coreVertices →
      x ∈ oldCarrier i u →
      x ∈ oldCarrier j v → i = j)
    (hParentInjective : ∀ i a b p,
      glueParent i a = some p →
      glueParent i b = some p → a = b)
    (hCompat : ∀ i u c,
      glueChild i u = some c →
      glueParent i (oldParent u) = some (coreParent c))
    (x : W) (p : CoreP)
    (hxOutside : x ∉ coreVertices)
    (hxForbidden : x ∉ allowed)
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
  obtain ⟨i, u, hau, hux⟩ :=
    generatedTag_offCore_has_oldOwner
      oldCarrier coreCarrier glueChild coreVertices
      hCoreCarrier x hxOutside a ha
  obtain ⟨j, v, hbv, hvx⟩ :=
    generatedTag_offCore_has_oldOwner
      oldCarrier coreCarrier glueChild coreVertices
      hCoreCarrier x hxOutside b hb
  have hij : i = j :=
    hOffCoreIndex i j u v x hxOutside hux hvx
  subst j
  have hpu : glueParent i (oldParent u) = some p :=
    generatedTag_sharedParent_oldContact oldParent coreParent
      glueChild glueParent hCompat i u p a hau hpa
  have hpv : glueParent i (oldParent v) = some p :=
    generatedTag_sharedParent_oldContact oldParent coreParent
      glueChild glueParent hCompat i v p b hbv hpb
  have hParentEq : oldParent u = oldParent v :=
    hParentInjective i (oldParent u) (oldParent v) p hpu hpv
  have huv : u = v := by
    by_contra hne
    have hxAllowed : x ∈ allowed :=
      hOld i hne hParentEq ⟨hux, hvx⟩
    exact hxForbidden hxAllowed
  calc
    a = gluedStandardNode glueChild i u := hau
    _ = gluedStandardNode glueChild i v :=
      congrArg (gluedStandardNode glueChild i) huv
    _ = b := hbv.symm

/-- If a generated parent has a PRIVATE tag (i,p), every child
incident at a vertex below that parent belongs to the SAME
standard copy i and has old parent p. -/
theorem generatedTag_privateParent_has_oldOwner
    (oldCarrier : I → Old → Set W)
    (oldParent : Old → OldP)
    (coreCarrier : Core → Set W)
    (coreParent : Core → CoreP)
    (glueChild : I → Old → Option Core)
    (glueParent : I → OldP → Option CoreP)
    (hCompat : ∀ i u c,
      glueChild i u = some c →
      glueParent i (oldParent u) = some (coreParent c))
    (x : W) (i : I) (p : OldP)
    (tag : Core ⊕ (I × Old))
    (hx : x ∈ GeneratedTaggedWagonCarrier
      oldCarrier coreCarrier glueChild tag)
    (hp : gluedWagonParent glueChild glueParent
      coreParent oldParent tag = Sum.inr (i, p)) :
    ∃ u : Old,
      tag = gluedStandardNode glueChild i u ∧
      oldParent u = p ∧
      x ∈ oldCarrier i u := by
  rcases hx with ⟨c, htag, hcx⟩ |
    ⟨j, u, htag, hux⟩
  · have hBad :
        (Sum.inl (coreParent c) :
          CoreP ⊕ (I × OldP)) = Sum.inr (i, p) := by
      simpa only [htag, gluedWagonParent] using hp
    cases hBad
  · have hpar :
        gluedStandardNode glueParent j (oldParent u) =
          Sum.inr (i, p) := by
      calc
        gluedStandardNode glueParent j (oldParent u) =
          gluedWagonParent glueChild glueParent
            coreParent oldParent (gluedStandardNode glueChild j u) :=
          (gluedWagonParent_standard
            glueChild glueParent coreParent oldParent hCompat j u).symm
        _ = gluedWagonParent glueChild glueParent
              coreParent oldParent tag := congrArg _ htag.symm
        _ = Sum.inr (i, p) := hp
    cases hg : glueParent j (oldParent u) with
    | none =>
        have hs :
            (Sum.inr (j, oldParent u) :
              CoreP ⊕ (I × OldP)) = Sum.inr (i, p) := by
          simpa only [gluedStandardNode, hg] using hpar
        have hpairs : (j, oldParent u) = (i, p) :=
          Sum.inr.inj hs
        have hji : j = i := congrArg Prod.fst hpairs
        have hOldp : oldParent u = p := congrArg Prod.snd hpairs
        refine ⟨u, ?_, hOldp, ?_⟩
        · simpa only [hji] using htag
        · simpa only [hji] using hux
    | some c =>
        have hBad :
            (Sum.inl c : CoreP ⊕ (I × OldP)) =
              Sum.inr (i, p) := by
          simpa only [gluedStandardNode, hg] using hpar
        cases hBad

/-- Every forbidden vertex has at most one generated child
below any PRIVATE parent, by the old standard parameter bound. -/
theorem generatedTag_forbidden_privateParent_unique
    (oldCarrier : I → Old → Set W)
    (oldParent : Old → OldP)
    (coreCarrier : Core → Set W)
    (coreParent : Core → CoreP)
    (glueChild : I → Old → Option Core)
    (glueParent : I → OldP → Option CoreP)
    (allowed : Set W)
    (hOld : ∀ i : I,
      TrainParentIntersectionBound (oldCarrier i) oldParent allowed)
    (hCompat : ∀ i u c,
      glueChild i u = some c →
      glueParent i (oldParent u) = some (coreParent c))
    (x : W) (i : I) (p : OldP)
    (hxForbidden : x ∉ allowed)
    (a b : Core ⊕ (I × Old))
    (ha : x ∈ GeneratedTaggedWagonCarrier
      oldCarrier coreCarrier glueChild a)
    (hb : x ∈ GeneratedTaggedWagonCarrier
      oldCarrier coreCarrier glueChild b)
    (hpa : gluedWagonParent glueChild glueParent
      coreParent oldParent a = Sum.inr (i, p))
    (hpb : gluedWagonParent glueChild glueParent
      coreParent oldParent b = Sum.inr (i, p)) :
    a = b := by
  obtain ⟨u, hau, hpu, hux⟩ :=
    generatedTag_privateParent_has_oldOwner
      oldCarrier oldParent coreCarrier coreParent
      glueChild glueParent hCompat x i p a ha hpa
  obtain ⟨v, hbv, hpv, hvx⟩ :=
    generatedTag_privateParent_has_oldOwner
      oldCarrier oldParent coreCarrier coreParent
      glueChild glueParent hCompat x i p b hb hpb
  have huv : u = v := by
    by_contra hne
    have hxAllowed : x ∈ allowed :=
      hOld i hne (hpu.trans hpv.symm) ⟨hux, hvx⟩
    exact hxForbidden hxAllowed
  calc
    a = gluedStandardNode glueChild i u := hau
    _ = gluedStandardNode glueChild i v :=
      congrArg (gluedStandardNode glueChild i) huv
    _ = b := hbv.symm

/-- COMPLETE generated tagged wagon parent-intersection parameter
under the genuine witness bridge and physical ownership hypotheses.

The core/shared-parent branch is discharged by the bridge, the
off-core/shared-parent branch by unique standard ownership and
parent reflection, and private parents by the old parameters.

This remains a CONDITIONAL train parameter lemma: the actual witness
must supply ParentCoreVertexBridge from order-one system girth,
and the concrete physical picture must supply the stated ownership
and partial-injection properties at every relevant level. -/
theorem generatedTaggedWagon_parentIntersectionBound
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
    (hBridge : ParentCoreVertexBridge oldCarrier oldParent
      coreCarrier glueChild glueParent coreVertices)
    (hCompat : ∀ i u c,
      glueChild i u = some c →
      glueParent i (oldParent u) = some (coreParent c)) :
    TrainParentIntersectionBound
      (GeneratedTaggedWagonCarrier
        oldCarrier coreCarrier glueChild)
      (gluedWagonParent glueChild glueParent coreParent oldParent)
      allowed := by
  intro a b hab hParent x hx
  by_contra hxForbidden
  cases hpa :
      gluedWagonParent glueChild glueParent
        coreParent oldParent a with
  | inl p =>
      have hpb :
          gluedWagonParent glueChild glueParent
            coreParent oldParent b = Sum.inl p :=
        hpa.symm.trans hParent
      have hEq : a = b := by
        by_cases hxCore : x ∈ coreVertices
        · exact generatedTaggedWagon_unique_at_forbidden_coreParent
            oldCarrier oldParent coreCarrier coreParent
            glueChild glueParent coreVertices allowed
            hOld hCore hBridge hCompat x p hxCore hxForbidden
            a b hx.1 hx.2 hpa hpb
        · exact generatedTag_forbidden_offCore_sharedParent_unique
            oldCarrier oldParent coreCarrier coreParent
            glueChild glueParent coreVertices allowed
            hOld hCoreCarrier hOffCoreIndex
            hParentInjective hCompat
            x p hxCore hxForbidden
            a b hx.1 hx.2 hpa hpb
      exact hab hEq
  | inr z =>
      rcases z with ⟨i, p⟩
      have hpb :
          gluedWagonParent glueChild glueParent
            coreParent oldParent b = Sum.inr (i, p) :=
        hpa.symm.trans hParent
      have hEq : a = b :=
        generatedTag_forbidden_privateParent_unique
          oldCarrier oldParent coreCarrier coreParent
          glueChild glueParent allowed
          hOld hCompat x i p hxForbidden
          a b hx.1 hx.2 hpa hpb
      exact hab hEq

end StructuralRamsey.Girth
