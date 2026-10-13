import Girth.TrainGeneratedTagCarrierFibres
import Girth.TrainPhysicalPictureGeneratedTrain

/-!
# Exact tagged wagon carriers in the physical generated picture train

At one cut, the physical pushout already has a verified normal form:
two real core/private support edges are equivalent exactly when their
shared/private wagon tags agree. Its vertex carrier is therefore
precisely the union of the corresponding core/standard source wagon
carriers. This combines the checked normal form with the independent
generic carrier-fibre theorem; there is NO equality-of-vertex-sets
identification between distinct wagon labels.

The source edge carrier maps remain parameters, constrained only to
agree with physical core and standard support edges. An application
to the actual relational A-support hypergraph follows via the checked
pushout edge bijection and carrier-preserving train transport.
-/

namespace StructuralRamsey.Girth

universe v
variable {W I Shared OldEdge CoreEdge : Type v}

/-- Every generated physical wagon has exactly the union of the
old/core source wagon carriers whose ancestors glue to its tag.
All train quotient classes are actual equality classes of source
physical edges. No abstract axiom on generated vertex carriers is
postulated. -/
theorem physicalPictureGeneratedTrain_wagonCarrier_eq_tagged
    {m : ℕ}
    (Told : EdgeTrainLevels OldEdge m)
    (Tcore : EdgeTrainLevels CoreEdge m)
    (μ : Fin (m + 1))
    (inOld : Shared ↪ OldEdge)
    (inCore : I → Shared ↪ CoreEdge)
    (hShared : ∀ i : I, Nonempty Shared)
    (hPreserve : ∀ i s t,
      Told.rel μ (inOld s) (inOld t) →
        Tcore.rel μ (inCore i s) (inCore i t))
    (oldEdgeCarrier : I → OldEdge → Set W)
    (coreEdgeCarrier : CoreEdge → Set W)
    (physicalEdgeCarrier : PhysicalPictureEdge inOld I CoreEdge → Set W)
    (hCorePhysical : ∀ b : CoreEdge,
      physicalEdgeCarrier (physicalCoreEdge inOld I b) =
        coreEdgeCarrier b)
    (hStdPhysical : ∀ (i : I) (a : OldEdge),
      physicalEdgeCarrier (physicalStandardEdge inOld inCore i a) =
        oldEdgeCarrier i a)
    (a : PhysicalPictureEdge inOld I CoreEdge) (x : W) :
    let oldClass : OldEdge →
        Quotient (Told.wagonSetoid μ) :=
      fun e => Quotient.mk (Told.wagonSetoid μ) e
    let coreClass : CoreEdge →
        Quotient (Tcore.wagonSetoid μ) :=
      fun e => Quotient.mk (Tcore.wagonSetoid μ) e
    let glue := wagonContactGlue
      (wagonSharedEdgeContact
        (fun (_ : I) s => oldClass (inOld s))
        (fun i s => coreClass (inCore i s)))
    x ∈ (physicalPictureGeneratedTrain
        Told Tcore inOld inCore hShared).wagonCarrier
      physicalEdgeCarrier μ a ↔
      x ∈ GeneratedTaggedWagonCarrier
        (taggedOldFiberCarrier oldClass oldEdgeCarrier)
        (taggedCoreFiberCarrier coreClass coreEdgeCarrier)
        glue (physicalPictureWagonTag
          inOld coreClass oldClass glue a) := by
  dsimp
  let oldClass : OldEdge → Quotient (Told.wagonSetoid μ) :=
    fun e => Quotient.mk (Told.wagonSetoid μ) e
  let coreClass : CoreEdge → Quotient (Tcore.wagonSetoid μ) :=
    fun e => Quotient.mk (Tcore.wagonSetoid μ) e
  let oldShared : I → Shared → Quotient (Told.wagonSetoid μ) :=
    fun _ s => oldClass (inOld s)
  let coreShared : I → Shared → Quotient (Tcore.wagonSetoid μ) :=
    fun i s => coreClass (inCore i s)
  let glue := wagonContactGlue
    (wagonSharedEdgeContact oldShared coreShared)
  let tag := physicalPictureWagonTag inOld coreClass oldClass glue

  have hPreserveClass : ∀ i s t,
      oldClass (inOld s) = oldClass (inOld t) →
        coreClass (inCore i s) = coreClass (inCore i t) := by
    intro i s t h
    exact Quotient.sound (hPreserve i s t (Quotient.exact h))
  have hUnique : ∀ i u c d,
      wagonSharedEdgeContact oldShared coreShared i u c →
      wagonSharedEdgeContact oldShared coreShared i u d →
      c = d := by
    intro i u c d hc hd
    exact wagonSharedEdgeContact_unique
      oldShared coreShared hPreserveClass i u c d hc hd
  have hSharedContact : ∀ i s,
      glue i (oldClass (inOld s)) =
        some (coreClass (inCore i s)) := by
    intro i s
    apply (wagonContactGlue_eq_some_iff
      (wagonSharedEdgeContact oldShared coreShared) hUnique
      i (oldClass (inOld s)) (coreClass (inCore i s))).mpr
    exact ⟨s, rfl, rfl⟩

  have hNormal : ∀ e f,
      (physicalPictureGeneratedTrain
        Told Tcore inOld inCore hShared).rel μ e f ↔
      tag e = tag f := by
    intro e f
    exact physicalPictureGenerated_iff_tag
      inOld inCore coreClass oldClass hPreserveClass e f

  have hCoreTag : ∀ b,
      tag (physicalCoreEdge inOld I b) =
        Sum.inl (coreClass b) := by
    intro b
    exact physicalCoreEdge_tag inOld coreClass oldClass glue b
  have hStdTag : ∀ i b,
      tag (physicalStandardEdge inOld inCore i b) =
        gluedStandardNode glue i (oldClass b) := by
    intro i b
    exact physicalStandardEdge_tag
      inOld inCore coreClass oldClass glue hSharedContact i b
  exact (generatedTaggedWagonCarrier_iff_physicalClass
    ((physicalPictureGeneratedTrain
      Told Tcore inOld inCore hShared).rel μ)
    tag (physicalCoreEdge inOld I)
    (physicalStandardEdge inOld inCore)
    coreClass oldClass glue
    physicalEdgeCarrier coreEdgeCarrier oldEdgeCarrier
    hNormal (physicalPictureEdge_covered inOld inCore)
    hCoreTag hStdTag hCorePhysical hStdPhysical a x).symm

end StructuralRamsey.Girth
