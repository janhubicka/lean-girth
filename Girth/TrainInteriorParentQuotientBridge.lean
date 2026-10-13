import Girth.TrainOrderOneBridge
import Girth.TrainTwoSourceBridge
import Girth.TrainSharedPhysicalChildOwner

/-!
# Interior two-source bridges on actual wagon quotients

The order-one witness is built from actual CORE edges and the images of
actual SHARED edges. A parent contact is witnessed by a shared edge, not
by an intersection of vertex carriers. The order-one argument supplies a
shared edge through the contact vertex in the required core parent;
reflection on the shared subsystem puts it in the required OLD parent.

This derives ParentCoreTwoSourceBridge from the exact order-one fragment,
pointwise shared-edge coverage and the genuine train embeddings. The
order-one bound is still a witness hypothesis; no local Ramsey existence
or higher-order system-girth preservation is asserted.
-/

namespace StructuralRamsey.Girth

universe v
variable {W I Shared OldEdge CoreEdge : Type v}

/-- Keep the edge representative's quotient label when extracting a
vertex from a wagon carrier. Carrier equality never identifies labels. -/
theorem EdgeTrainLevels.exists_incident_representative
    {m : ℕ} (T : EdgeTrainLevels OldEdge m)
    (edge : OldEdge → Set W) (μ : Fin (m + 1))
    (u : Quotient (T.wagonSetoid μ)) (x : W)
    (hx : x ∈ T.wagonClassCarrier edge μ u) :
    ∃ e : OldEdge, Quotient.mk (T.wagonSetoid μ) e = u ∧ x ∈ edge e := by
  induction u using Quotient.inductionOn with
  | h a =>
    change x ∈ T.wagonCarrier edge μ a at hx
    rcases hx with ⟨e, hae, hxe⟩
    exact ⟨e, (Quotient.sound hae).symm, hxe⟩

/-- Unfold a quotient contact to its actual shared-edge witness. -/
theorem sharedWagonQuotient_contact_iff
    {m : ℕ} (Told : EdgeTrainLevels OldEdge m)
    (Tcore : EdgeTrainLevels CoreEdge m) (κ : Fin (m + 1))
    (oldEmbed : I → Shared ↪ OldEdge) (coreEmbed : I → Shared ↪ CoreEdge)
    (hRel : ∀ i s t,
      Told.rel κ (oldEmbed i s) (oldEmbed i t) ↔
        Tcore.rel κ (coreEmbed i s) (coreEmbed i t))
    (i : I) (u : Quotient (Told.wagonSetoid κ))
    (c : Quotient (Tcore.wagonSetoid κ)) :
    wagonContactGlue (wagonSharedEdgeContact
        (oldSharedWagonLabel Told κ oldEmbed)
        (oldSharedWagonLabel Tcore κ coreEmbed)) i u = some c ↔
      ∃ s : Shared,
        oldSharedWagonLabel Told κ oldEmbed i s = u ∧
        oldSharedWagonLabel Tcore κ coreEmbed i s = c := by
  apply wagonContactGlue_eq_some_iff
  intro j a b d hb hd
  exact wagonSharedEdgeContact_unique
    (oldSharedWagonLabel Told κ oldEmbed)
    (oldSharedWagonLabel Tcore κ coreEmbed)
    (fun k s t h =>
      (sharedWagonLabel_eq_iff Told Tcore κ oldEmbed coreEmbed hRel k s t).mp h)
    j a b d hb hd

/-- The exact order-one incidence data of the shared witness copies at
one parent cut. Edge labels are actual core edges, not copies of them. -/
def sharedWitnessOrderOneData
    {m : ℕ} (Tcore : EdgeTrainLevels CoreEdge m)
    (ν : Fin (m + 1)) (coreEmbed : I → Shared ↪ CoreEdge)
    (coreEdgeCarrier : CoreEdge → Set W) :
    OrderOneData W CoreEdge I (Quotient (Tcore.wagonSetoid ν)) where
  edgeCarrier := coreEdgeCarrier
  copyCarrier := fun i => {x | ∃ s : Shared, x ∈ coreEdgeCarrier (coreEmbed i s)}
  copyEdges := fun i => Set.range (coreEmbed i)
  parent := Quotient.mk (Tcore.wagonSetoid ν)

/-- A genuine two-source bridge at any nested child/parent cuts.

For an interior parent the supplied Bound is precisely the order-one
part of the NEXT system-girth coordinate. At a universal top parent,
pointwise shared-edge coverage gives the older, stronger bridge without
this extra hypothesis; that separate top theorem is unchanged. -/
theorem interiorParent_twoSourceBridge_of_orderOne
    {m : ℕ}
    (Told : EdgeTrainLevels OldEdge m)
    (Tcore : EdgeTrainLevels CoreEdge m)
    (μ ν : Fin (m + 1)) (hμν : μ ≤ ν)
    (oldEmbed : I → Shared ↪ OldEdge)
    (coreEmbed : I → Shared ↪ CoreEdge)
    (hRel : ∀ κ : Fin (m + 1), ∀ i s t,
      Told.rel κ (oldEmbed i s) (oldEmbed i t) ↔
        Tcore.rel κ (coreEmbed i s) (coreEmbed i t))
    (oldEdgeCarrier : I → OldEdge → Set W)
    (coreEdgeCarrier : CoreEdge → Set W)
    (hPhysical : ∀ i s,
      oldEdgeCarrier i (oldEmbed i s) = coreEdgeCarrier (coreEmbed i s))
    (coreVertices allowed : Set W)
    (hPointCoveredEdge : ∀ (i : I) (e : OldEdge) (x : W),
      x ∈ coreVertices → x ∈ oldEdgeCarrier i e →
      ∃ s : Shared, x ∈ oldEdgeCarrier i (oldEmbed i s))
    (hOrderOne :
      (sharedWitnessOrderOneData Tcore ν coreEmbed coreEdgeCarrier).Bound) :
    ParentCoreTwoSourceBridge
      (fun i => Told.wagonClassCarrier (oldEdgeCarrier i) μ)
      (Told.wagonParent μ ν hμν)
      (Tcore.wagonClassCarrier coreEdgeCarrier μ)
      (Tcore.wagonParent μ ν hμν)
      (wagonContactGlue (wagonSharedEdgeContact
        (oldSharedWagonLabel Told μ oldEmbed)
        (oldSharedWagonLabel Tcore μ coreEmbed)))
      (wagonContactGlue (wagonSharedEdgeContact
        (oldSharedWagonLabel Told ν oldEmbed)
        (oldSharedWagonLabel Tcore ν coreEmbed)))
      coreVertices allowed := by
  let D := sharedWitnessOrderOneData Tcore ν coreEmbed coreEdgeCarrier
  intro x p i u hxCore _hxForbidden hpu hxu hSecond
  obtain ⟨t, htOld, htCore⟩ :=
    (sharedWagonQuotient_contact_iff Told Tcore ν oldEmbed coreEmbed
      (hRel ν) i (Told.wagonParent μ ν hμν u) p).mp hpu
  have copyVertex : ∀ (j : I) (v : Quotient (Told.wagonSetoid μ)),
      x ∈ Told.wagonClassCarrier (oldEdgeCarrier j) μ v →
      x ∈ D.carrier (.inl j) := by
    intro j v hxv
    obtain ⟨e, _he, hxe⟩ :=
      Told.exists_incident_representative (oldEdgeCarrier j) μ v x hxv
    obtain ⟨s, hxs⟩ := hPointCoveredEdge j e x hxCore hxe
    exact ⟨s, (hPhysical j s) ▸ hxs⟩
  have hiVertex : x ∈ D.carrier (.inl i) := copyVertex i u hxu
  have hiMeets : D.Meets (.inl i) p :=
    ⟨coreEmbed i t, ⟨t, rfl⟩, htCore⟩
  have bridge : D.Bridge (.inl i) x p := by
    rcases hSecond with ⟨c, hcp, hxc⟩ | ⟨j, v, hji, hpv, hxv⟩
    · obtain ⟨e, he, hxe⟩ :=
        Tcore.exists_incident_representative coreEdgeCarrier μ c x hxc
      have hep : D.parent e = p := by
        calc
          D.parent e = Tcore.wagonParent μ ν hμν
              (Quotient.mk (Tcore.wagonSetoid μ) e) := rfl
          _ = Tcore.wagonParent μ ν hμν c := congrArg _ he
          _ = p := hcp
      exact D.bridge_of_incident_edge hOrderOne (.inl i) x p
        hiVertex hiMeets e hep hxe
    · obtain ⟨s, _hsOld, hsCore⟩ :=
        (sharedWagonQuotient_contact_iff Told Tcore ν oldEmbed coreEmbed
          (hRel ν) j (Told.wagonParent μ ν hμν v) p).mp hpv
      have hDistinct : (Sum.inl i : I ⊕ CoreEdge) ≠ Sum.inl j := by
        intro h
        exact hji (Sum.inl.inj h).symm
      exact (D.both_bridges hOrderOne (.inl i) (.inl j) x p hDistinct
        hiVertex (copyVertex j v hxv) hiMeets
        ⟨coreEmbed j s, ⟨s, rfl⟩, hsCore⟩).1
  rcases bridge with ⟨e, ⟨s, hse⟩, hep, hxe⟩
  subst e
  let v := oldSharedWagonLabel Told μ oldEmbed i s
  let c := oldSharedWagonLabel Tcore μ coreEmbed i s
  have hParent : Told.wagonParent μ ν hμν v =
      Told.wagonParent μ ν hμν u := by
    have hCoreEq : oldSharedWagonLabel Tcore ν coreEmbed i s =
        oldSharedWagonLabel Tcore ν coreEmbed i t := hep.trans htCore.symm
    have hOldEq := (sharedWagonLabel_eq_iff Told Tcore ν oldEmbed coreEmbed
      (hRel ν) i s t).mpr hCoreEq
    exact hOldEq.trans htOld
  refine ⟨v, c, hParent, ?_, ?_, ?_⟩
  · apply Told.mem_wagonClassCarrier_of_mem_edge
    exact (hPhysical i s).symm ▸ hxe
  · apply (sharedWagonQuotient_contact_iff Told Tcore μ oldEmbed coreEmbed
      (hRel μ) i v c).mpr
    exact ⟨s, rfl, rfl⟩
  · exact Tcore.mem_wagonClassCarrier_of_mem_edge
      coreEdgeCarrier μ (coreEmbed i s) x hxe

end StructuralRamsey.Girth
