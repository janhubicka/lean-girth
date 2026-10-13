import Girth.TrainTopParentBridge
import Girth.TrainSharedPhysicalChildOwner

/-!
# Universal top-parent bridges from genuine shared quotient children

This composes three *already verified* ingredients:
(1) a physical vertex of an old wagon carrier is on an actual old edge;
(2) pointwise coverage by a genuinely shared edge yields contacting
    old/core quotient CHILD wagons at that vertex;
(3) their old PARENTS agree at the universal top cut.

The result derives the faithful two-SOURCE bridge for the universal
parent, without invoking an unavailable next system-girth coordinate.

Pointwise shared-edge coverage is a real geometric hypothesis:
it is valid for the true active gluing carrier, as shown in the
actual attachment bridge modules, but FALSE for an arbitrary gluing
subsystem containing isolated shared vertices. This file still
does not identify the quotient model with every generated attached
wagon tag; exact actual-attachment instantiation remains separate.
Interior-level bridges still need the order-one cycle argument.
-/

namespace StructuralRamsey.Girth

universe v
variable {W I Shared OldEdge CoreEdge : Type v}

/-- Membership of a labelled wagon carrier has a representative
genuine physical edge through the vertex. No carrier equality is
used to identify two wagon labels. -/
theorem EdgeTrainLevels.exists_incident_edge_of_wagonClassCarrier
    {m : ℕ} (T : EdgeTrainLevels OldEdge m)
    (edge : OldEdge → Set W)
    (μ : Fin (m + 1))
    (u : Quotient (T.wagonSetoid μ))
    (x : W)
    (hx : x ∈ T.wagonClassCarrier edge μ u) :
    ∃ e : OldEdge, x ∈ edge e := by
  induction u using Quotient.inductionOn with
  | h a =>
    change x ∈ T.wagonCarrier edge μ a at hx
    rcases hx with ⟨b, _hab, hxb⟩
    exact ⟨b, hxb⟩

/-- Every child quotient maps to the unique universal top parent.
The equality is about quotient WAGON LABELS, not their vertex sets. -/
theorem EdgeTrainLevels.wagonParent_top_eq
    {m : ℕ} (T : EdgeTrainLevels OldEdge m)
    (μ : Fin (m + 1))
    (hμtop : μ ≤ (⟨m, Nat.lt_succ_self m⟩ : Fin (m + 1)))
    (u v : Quotient (T.wagonSetoid μ)) :
    T.wagonParent μ ⟨m, Nat.lt_succ_self m⟩ hμtop u =
      T.wagonParent μ ⟨m, Nat.lt_succ_self m⟩ hμtop v := by
  induction u using Quotient.inductionOn with
  | h a =>
    induction v using Quotient.inductionOn with
    | h b =>
      change
        (Quotient.mk (T.wagonSetoid ⟨m, Nat.lt_succ_self m⟩) a) =
          Quotient.mk (T.wagonSetoid ⟨m, Nat.lt_succ_self m⟩) b
      exact Quotient.sound (T.top a b)

/-- At the top parent, the shared-edge quotient contact, together
with pointwise physical shared-edge coverage, supplies the entire
two-source bridge. The old/core quotient child carriers and both
their parent maps are the actual EdgeTrainLevels quotient data.

The conclusion assumes the true shared-edge train embedding at the
child level (preservation AND reflection) and physical carrier equality.
It does not require or pretend to prove the non-top witness bridge. -/
theorem topParent_twoSourceBridge_of_sharedQuotientCoverage
    {m : ℕ}
    (Told : EdgeTrainLevels OldEdge m)
    (Tcore : EdgeTrainLevels CoreEdge m)
    (μ : Fin (m + 1))
    (hμtop : μ ≤ (⟨m, Nat.lt_succ_self m⟩ : Fin (m + 1)))
    (oldEmbed : I → Shared ↪ OldEdge)
    (coreEmbed : I → Shared ↪ CoreEdge)
    (hRel : ∀ i s t,
      Told.rel μ (oldEmbed i s) (oldEmbed i t) ↔
        Tcore.rel μ (coreEmbed i s) (coreEmbed i t))
    (oldEdgeCarrier : I → OldEdge → Set W)
    (coreEdgeCarrier : CoreEdge → Set W)
    (hPhysical : ∀ i s,
      oldEdgeCarrier i (oldEmbed i s) =
        coreEdgeCarrier (coreEmbed i s))
    (coreVertices allowed : Set W)
    (hPointCoveredEdge : ∀ (i : I) (e : OldEdge) (x : W),
      x ∈ coreVertices →
      x ∈ oldEdgeCarrier i e →
      ∃ s : Shared, x ∈ oldEdgeCarrier i (oldEmbed i s)) :
    ParentCoreTwoSourceBridge
      (fun i => Told.wagonClassCarrier (oldEdgeCarrier i) μ)
      (Told.wagonParent μ ⟨m, Nat.lt_succ_self m⟩ hμtop)
      (Tcore.wagonClassCarrier coreEdgeCarrier μ)
      (Tcore.wagonParent μ ⟨m, Nat.lt_succ_self m⟩ hμtop)
      (wagonContactGlue (wagonSharedEdgeContact
        (oldSharedWagonLabel Told μ oldEmbed)
        (oldSharedWagonLabel Tcore μ coreEmbed)))
      (wagonContactGlue (wagonSharedEdgeContact
        (oldSharedWagonLabel Told ⟨m, Nat.lt_succ_self m⟩ oldEmbed)
        (oldSharedWagonLabel Tcore ⟨m, Nat.lt_succ_self m⟩ coreEmbed)))
      coreVertices allowed := by
  apply topParent_twoSourceBridge_of_vertexCoverage
  · intro u v
    exact Told.wagonParent_top_eq μ hμtop u v
  · intro i u x hxCore hxOld
    obtain ⟨e, hxe⟩ :=
      Told.exists_incident_edge_of_wagonClassCarrier
        (oldEdgeCarrier i) μ u x hxOld
    obtain ⟨s, hxs⟩ :=
      hPointCoveredEdge i e x hxCore hxe
    exact sharedPhysicalEdge_contactingChildQuotients
      Told Tcore μ oldEmbed coreEmbed hRel
      oldEdgeCarrier coreEdgeCarrier i s x hxs (hPhysical i s)

end StructuralRamsey.Girth
