import Girth.TrainPhysicalPictureEdgePushout
import Girth.TrainNormalFormRestriction
import Girth.TrainWagonSharedEdgeContact

/-!
# Exact old-wagon restriction in the concrete physical edge pushout

The one-cut generated-equivalence theorem on actual physical edge
presentations needs only preservation of old class equality on shared
edges. However, exact REFLECTION of old wagon classes requires more:
the shared-subsystem train embedding must also reflect core class
equality. Without reflection, two distinct old wagons can be merged
through the core at that horizontal cut.

Under both preservation and reflection, the concrete physical edge
pushout has EXACTLY the old equivalence relation on every full
standard picture. The proof uses actual shared gluing edges, unique
contact and the checked generated-tag normal form; no pruning or
assumption of carrier-equality-based wagon identification.

This is a one-horizontal-cut restriction theorem, NOT proof of the
whole multilevel system-Girth A1--A3.
-/

namespace StructuralRamsey.Girth

universe v
variable {I Shared OldEdge CoreEdge Old Core : Type v}

/-- The generated physical wagon equivalence of two edges in a
single old standard picture is equivalent to equality of their
OLD wagon classes, assuming preservation and REFLECTION on the
actual gluing subsystem. -/
theorem physicalPictureGenerated_restrict_standard
    (inOld : Shared ↪ OldEdge)
    (inCore : I → Shared ↪ CoreEdge)
    (coreClass : CoreEdge → Core)
    (oldClass : OldEdge → Old)
    (hPreserve : ∀ i s t,
      oldClass (inOld s) = oldClass (inOld t) →
        coreClass (inCore i s) = coreClass (inCore i t))
    (hReflect : ∀ i s t,
      coreClass (inCore i s) = coreClass (inCore i t) →
        oldClass (inOld s) = oldClass (inOld t))
    (i : I) (a b : OldEdge) :
    TrainEdgeGenerated
      (PictureWagonStep
        (physicalCoreEdge inOld I)
        (physicalStandardEdge inOld inCore)
        coreClass oldClass)
      (physicalStandardEdge inOld inCore i a)
      (physicalStandardEdge inOld inCore i b) ↔
    oldClass a = oldClass b := by
  let oldShared : I → Shared → Old :=
    fun _ s => oldClass (inOld s)
  let coreShared : I → Shared → Core :=
    fun j s => coreClass (inCore j s)
  let touch := wagonSharedEdgeContact oldShared coreShared
  let glue := wagonContactGlue touch
  let tag := physicalPictureWagonTag inOld coreClass oldClass glue
  let R : PhysicalPictureEdge inOld I CoreEdge →
      PhysicalPictureEdge inOld I CoreEdge → Prop :=
    TrainEdgeGenerated
      (PictureWagonStep
        (physicalCoreEdge inOld I)
        (physicalStandardEdge inOld inCore)
        coreClass oldClass)
  have hTag : ∀ e f, R e f ↔ tag e = tag f := by
    exact physicalPictureGenerated_iff_tag
      inOld inCore coreClass oldClass hPreserve
  have hUnique : ∀ j x c d,
      touch j x c → touch j x d → c = d := by
    intro j x c d hc hd
    exact wagonSharedEdgeContact_unique oldShared coreShared
      hPreserve j x c d hc hd
  have hReflectContact : ∀ j x y c,
      touch j x c → touch j y c → x = y := by
    intro j x y c hx hy
    exact wagonSharedEdgeContact_reflect oldShared coreShared
      hReflect j x y c hx hy
  have hInj : ∀ j x y c,
      glue j x = some c →
      glue j y = some c → x = y :=
    wagonContactGlue_injective touch hUnique hReflectContact
  have hSharedTag : ∀ j s,
      glue j (oldClass (inOld s)) =
        some (coreClass (inCore j s)) := by
    intro j s
    apply (wagonContactGlue_eq_some_iff
      touch hUnique j (oldClass (inOld s))
      (coreClass (inCore j s))).mpr
    exact ⟨s, rfl, rfl⟩
  have hStdTag : ∀ j a,
      tag (physicalStandardEdge inOld inCore j a) =
        gluedStandardNode glue j (oldClass a) :=
    physicalStandardEdge_tag inOld inCore
      coreClass oldClass glue hSharedTag
  exact normalForm_restrict_standard
    R tag hTag glue hInj
    (physicalStandardEdge inOld inCore) oldClass
    hStdTag i a b

end StructuralRamsey.Girth
