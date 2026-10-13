import Girth.TrainTwoSourceBridge
import Girth.TrainActiveVertexSupport

/-!
# Top-parent bridges from pointwise support of the gluing vertices

The manuscript formerly called the bridge at the universal parent
automatic. Nonempty contact of each standard picture with the core
is INSUFFICIENT: it could occur elsewhere than the vertex x.

The correct sufficient local hypothesis is a genuine shared old
child through every core vertex at which a standard old child is
incident. At the universal top parent all old children have the
same parent, hence the shared child is necessarily a sibling.
This yields the TWO-SOURCE witness bridge (even the stronger
singleton version) without order-one system-Girth.

TrainActiveVertexSupport.lean checks the crucial physical
pointwise gluing-edge coverage for the true active subsystem.
The remaining identification of these shared support edges with
the actual train child tags is not claimed here.
-/

namespace StructuralRamsey.Girth

universe v
variable {W I Old OldP Core CoreP : Type v}

/-- Universal old parent and a shared child through every relevant
core vertex give the complete top-level two-source bridge. No
pairwise cycle argument is needed. The stronger point-coverage
hypothesis is explicitly separate from a merely nonempty shared
edge somewhere in each standard picture. -/
theorem topParent_twoSourceBridge_of_vertexCoverage
    (oldCarrier : I → Old → Set W)
    (oldParent : Old → OldP)
    (coreCarrier : Core → Set W)
    (coreParent : Core → CoreP)
    (glueChild : I → Old → Option Core)
    (glueParent : I → OldP → Option CoreP)
    (coreVertices allowed : Set W)
    (hUniversal : ∀ u v : Old, oldParent u = oldParent v)
    (hPointCovered : ∀ (i : I) (u : Old) (x : W),
      x ∈ coreVertices →
      x ∈ oldCarrier i u →
      ∃ (v : Old) (c : Core),
        x ∈ oldCarrier i v ∧
        glueChild i v = some c ∧
        x ∈ coreCarrier c) :
    ParentCoreTwoSourceBridge
      oldCarrier oldParent coreCarrier coreParent
      glueChild glueParent coreVertices allowed := by
  intro x p i u hxCore _hxForbidden _hParent hxOld _hSecond
  obtain ⟨v, c, hxv, hGlue, hCore⟩ :=
    hPointCovered i u x hxCore hxOld
  exact ⟨v, c, hUniversal v u, hxv, hGlue, hCore⟩

end StructuralRamsey.Girth
