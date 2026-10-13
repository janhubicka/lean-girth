import Girth.TrainGeneratedTagCoreParameter
import Girth.TrainSharedEdgeQuotients

/-!
# Generated wagon carriers respect the unary parent map

Every generated child wagon is a union of genuine old/core source
wagon carriers. If source child carriers lie in their source parent
carriers, the generated child carrier lies in its generated parent
carrier. This is a set-theoretic fact about *labelled* nodes; no
injectivity of vertex carriers, system-girth, or Ramsey assertion
is used.

The separate source-parent compatibility is essential: a private
child tag may have a shared parent.
-/

namespace StructuralRamsey.Girth

universe v
variable {W I Old OldP Core CoreP : Type v}

/-- The unary glued parent sends every actually generated node to
an actually generated parent node, including private children
whose parent becomes shared. -/
theorem generatedWagonNodes_parent_closed
    (childGlue : I → Old → Option Core)
    (parentGlue : I → OldP → Option CoreP)
    (oldParent : Old → OldP)
    (coreParent : Core → CoreP)
    (hCompat : ∀ i u c,
      childGlue i u = some c →
      parentGlue i (oldParent u) = some (coreParent c))
    (tag : Core ⊕ (I × Old))
    (hTag : tag ∈ generatedWagonNodes childGlue) :
    gluedWagonParent childGlue parentGlue coreParent oldParent tag ∈
      generatedWagonNodes parentGlue := by
  rcases hTag with hCore | hOld
  · rcases hCore with ⟨c, rfl⟩
    rw [gluedWagonParent_core]
    exact gluedCoreNode_generated parentGlue (coreParent c)
  · rcases Set.mem_iUnion.mp hOld with ⟨i, hi⟩
    rcases hi with ⟨u, rfl⟩
    rw [gluedWagonParent_standard
      childGlue parentGlue coreParent oldParent hCompat i u]
    exact gluedStandardNode_generated parentGlue i (oldParent u)

/-- Physical support of a generated child wagon is contained
in the physical support of its generated unary parent, provided
the corresponding old/core source carriers are nested.

This explicitly uses the label parent map, rather than inferring
parenthood from inclusion or equality of vertex-carrier sets. -/
theorem generatedTaggedWagonCarrier_parent_subset
    (childOld : I → Old → Set W)
    (parentOld : I → OldP → Set W)
    (childCore : Core → Set W)
    (parentCore : CoreP → Set W)
    (childGlue : I → Old → Option Core)
    (parentGlue : I → OldP → Option CoreP)
    (oldParent : Old → OldP)
    (coreParent : Core → CoreP)
    (hCompat : ∀ i u c,
      childGlue i u = some c →
      parentGlue i (oldParent u) = some (coreParent c))
    (hOld : ∀ i u, childOld i u ⊆ parentOld i (oldParent u))
    (hCore : ∀ c, childCore c ⊆ parentCore (coreParent c))
    (tag : Core ⊕ (I × Old)) :
    GeneratedTaggedWagonCarrier childOld childCore childGlue tag ⊆
      GeneratedTaggedWagonCarrier parentOld parentCore parentGlue
        (gluedWagonParent childGlue parentGlue
          coreParent oldParent tag) := by
  intro x hx
  rcases hx with ⟨c, htag, hxc⟩ | ⟨i, u, htag, hxu⟩
  · left
    refine ⟨coreParent c, ?_, hCore c hxc⟩
    rw [htag]
    rfl
  · right
    refine ⟨i, oldParent u, ?_, hOld i u hxu⟩
    calc
      gluedWagonParent childGlue parentGlue coreParent oldParent tag =
          gluedWagonParent childGlue parentGlue coreParent oldParent
            (gluedStandardNode childGlue i u) :=
        congrArg (gluedWagonParent childGlue parentGlue
          coreParent oldParent) htag
      _ = gluedStandardNode parentGlue i (oldParent u) :=
        gluedWagonParent_standard
          childGlue parentGlue coreParent oldParent hCompat i u


/-- At any two nested cuts of a REAL edge train, the complete
vertex carrier of an old/core quotient child wagon is contained in
that of its canonical quotient parent.  There is no need to choose
a representative, and no injectivity claim for carrier sets. -/
theorem EdgeTrainLevels.wagonClassCarrier_parent_subset
    {m : ℕ} {E : Type v}
    (T : EdgeTrainLevels E m)
    (edge : E → Set W)
    (μ ν : Fin (m + 1)) (hμν : μ ≤ ν)
    (u : Quotient (T.wagonSetoid μ)) :
    T.wagonClassCarrier edge μ u ⊆
      T.wagonClassCarrier edge ν (T.wagonParent μ ν hμν u) := by
  induction u using Quotient.inductionOn with
  | h a =>
    change T.wagonCarrier edge μ a ⊆ T.wagonCarrier edge ν a
    rintro x ⟨b, hab, hbx⟩
    exact ⟨b, T.nested μ ν hμν a b hab, hbx⟩

end StructuralRamsey.Girth
