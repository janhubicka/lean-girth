import Girth.TrainSharedEdgeQuotients

/-!
# A shared physical support edge supplies child-wagon owners on both sides

The parent-parameter proof requires more than a physical A-edge through
the contact vertex: it needs this edge in an old CHILD wagon and an
actual core CHILD wagon, with the old child touching the core child.

For genuine shared support edges, these are the QUOTIENT train ancestor
classes of the same physical edge. Preservation and reflection of the
shared-subsystem train relation make their core contact functional.
No selection of an arbitrary vertex-owner wagon is needed.

This is the precise quotient-level bridge to combine with pointwise
active-carrier coverage. Its conclusion is conditional on the
old/core edge image equality, supplied for actual attachments by
sharedOldACarrierCoreMap_image, and the train-embedding relation
reflection. It does NOT prove existence of the local Ramsey witness,
nor the actual two-source order-one girth bridge.
-/

namespace StructuralRamsey.Girth

universe v
variable {E W I Shared OldEdge CoreEdge : Type v}

/-- A genuine physical edge is contained in its own labelled
equivalence-class wagon carrier, without identifying different
wagon LABELS that happen to have identical physical carriers. -/
theorem EdgeTrainLevels.mem_wagonClassCarrier_of_mem_edge
    {m : ℕ} (T : EdgeTrainLevels E m)
    (edge : E → Set W) (μ : Fin (m + 1))
    (a : E) (x : W) (hx : x ∈ edge a) :
    x ∈ T.wagonClassCarrier edge μ
      (Quotient.mk (T.wagonSetoid μ) a) := by
  change x ∈ T.wagonCarrier edge μ a
  exact ⟨a, (T.equivalent μ).refl a, hx⟩

/-- At any fixed child cut, a genuine shared old support edge and
its actual core image determine contacting OLD and CORE wagon
quotient labels, both incident with the same physical vertex.

The only geometric premise is equality of the actual PHYSICAL
edge carriers. The only train premise is preservation/reflection
of shared-subsystem equivalence at this cut. -/
theorem sharedPhysicalEdge_contactingChildQuotients
    {m : ℕ}
    (Told : EdgeTrainLevels OldEdge m)
    (Tcore : EdgeTrainLevels CoreEdge m)
    (μ : Fin (m + 1))
    (oldEmbed : I → Shared ↪ OldEdge)
    (coreEmbed : I → Shared ↪ CoreEdge)
    (hRel : ∀ i s t,
      Told.rel μ (oldEmbed i s) (oldEmbed i t) ↔
        Tcore.rel μ (coreEmbed i s) (coreEmbed i t))
    (oldEdgeCarrier : I → OldEdge → Set W)
    (coreEdgeCarrier : CoreEdge → Set W)
    (i : I) (s : Shared) (x : W)
    (hxOld : x ∈ oldEdgeCarrier i (oldEmbed i s))
    (hPhysical : oldEdgeCarrier i (oldEmbed i s) =
      coreEdgeCarrier (coreEmbed i s)) :
    ∃ (u : Quotient (Told.wagonSetoid μ))
      (c : Quotient (Tcore.wagonSetoid μ)),
      x ∈ Told.wagonClassCarrier (oldEdgeCarrier i) μ u ∧
      wagonContactGlue
          (wagonSharedEdgeContact
            (oldSharedWagonLabel Told μ oldEmbed)
            (oldSharedWagonLabel Tcore μ coreEmbed))
          i u = some c ∧
      x ∈ Tcore.wagonClassCarrier coreEdgeCarrier μ c := by
  let u := oldSharedWagonLabel Told μ oldEmbed i s
  let c := oldSharedWagonLabel Tcore μ coreEmbed i s
  have hUnique : ∀ j a b d,
      wagonSharedEdgeContact
        (oldSharedWagonLabel Told μ oldEmbed)
        (oldSharedWagonLabel Tcore μ coreEmbed)
        j a b →
      wagonSharedEdgeContact
        (oldSharedWagonLabel Told μ oldEmbed)
        (oldSharedWagonLabel Tcore μ coreEmbed)
        j a d → b = d := by
    intro j a b d hb hd
    exact wagonSharedEdgeContact_unique
      (oldSharedWagonLabel Told μ oldEmbed)
      (oldSharedWagonLabel Tcore μ coreEmbed)
      (fun k s t h =>
        (sharedWagonLabel_eq_iff
          Told Tcore μ oldEmbed coreEmbed hRel k s t).mp h)
      j a b d hb hd
  have hContact :
      wagonContactGlue
        (wagonSharedEdgeContact
          (oldSharedWagonLabel Told μ oldEmbed)
          (oldSharedWagonLabel Tcore μ coreEmbed))
        i u = some c := by
    apply (wagonContactGlue_eq_some_iff
      (wagonSharedEdgeContact
        (oldSharedWagonLabel Told μ oldEmbed)
        (oldSharedWagonLabel Tcore μ coreEmbed))
      hUnique i u c).mpr
    exact ⟨s, rfl, rfl⟩
  have hxCore : x ∈ coreEdgeCarrier (coreEmbed i s) := by
    rw [← hPhysical]
    exact hxOld
  exact ⟨u, c,
    Told.mem_wagonClassCarrier_of_mem_edge
      (oldEdgeCarrier i) μ (oldEmbed i s) x hxOld,
    hContact,
    Tcore.mem_wagonClassCarrier_of_mem_edge
      coreEdgeCarrier μ (coreEmbed i s) x hxCore⟩

end StructuralRamsey.Girth
