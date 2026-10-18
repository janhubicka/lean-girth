import Girth.TrainCrossStandardCoreWagon

/-!
# Circulation: physical core-edge incidence witnesses for shared wagons

A shared/core-tagged actual output wagon does more than merely have
a named contraction. Every edge of this wagon arriving from standard i
has a *genuine gluing edge s* in the same old wagon, whose actual core
ancestor equals the contraction. This is the incidence fact Section 12
needs to conclude that a retained wagon boundary connects its two
contracted witness-copy labels.

The proof recovers the physical edge using the canonical shared-edge
contact, rather than postulating a bridge or relying on equality of
wagon vertex carriers. The cross-standard corollary produces witnesses
on BOTH sides of the same output wagon.

It remains to identify the two source edges of each segment boundary
with the actual labelled-cycle incidence; this file does not construct
a legal reduct or certify A1--A3. No appendix.
-/

namespace StructuralRamsey.Girth.PhysicalWagonModel

universe v
variable {I Shared OldEdge CoreEdge : Type v} {m : ℕ}

/-- A physical edge from standard i has a core wagon tag c iff
some ACTUAL shared edge of that standard lies in the same old wagon
and has core ancestor c. This is the edge-level contact needed for
witness-wagon incidence in the geometric reduct. -/
theorem edgeTag_standard_core_iff_shared_edge
    (Told : EdgeTrainLevels OldEdge m)
    (Tcore : EdgeTrainLevels CoreEdge m)
    (inOld : Shared ↪ OldEdge)
    (inCore : I → Shared ↪ CoreEdge)
    (hRel : ∀ κ : Fin (m + 1), ∀ i s t,
      Told.rel κ (inOld s) (inOld t) ↔
        Tcore.rel κ (inCore i s) (inCore i t))
    (μ : Fin (m + 1)) (i : I) (a : OldEdge)
    (c : Quotient (Tcore.wagonSetoid μ)) :
    edgeTag Told Tcore inOld inCore μ
        (physicalStandardEdge inOld inCore i a) = Sum.inl c ↔
    ∃ s : Shared,
      Told.rel μ (inOld s) a ∧
      Quotient.mk (Tcore.wagonSetoid μ) (inCore i s) = c := by
  let oldShared : I → Shared → Quotient (Told.wagonSetoid μ) :=
    fun _ s => Quotient.mk (Told.wagonSetoid μ) (inOld s)
  let coreShared : I → Shared → Quotient (Tcore.wagonSetoid μ) :=
    fun j s => Quotient.mk (Tcore.wagonSetoid μ) (inCore j s)
  have hPreserve : ∀ j s t, oldShared j s = oldShared j t →
      coreShared j s = coreShared j t := by
    intro j s t heq
    exact Quotient.sound ((hRel μ j s t).mp (Quotient.exact heq))
  have hUnique : ∀ j u c d,
      wagonSharedEdgeContact oldShared coreShared j u c →
      wagonSharedEdgeContact oldShared coreShared j u d → c = d := by
    intro j u c d hc hd
    exact wagonSharedEdgeContact_unique
      oldShared coreShared hPreserve j u c d hc hd
  calc
    edgeTag Told Tcore inOld inCore μ
          (physicalStandardEdge inOld inCore i a) = Sum.inl c ↔
        gluedStandardNode (contact Told Tcore inOld inCore μ)
            i (Quotient.mk (Told.wagonSetoid μ) a) =
          gluedCoreNode (contact Told Tcore inOld inCore μ) c := by
      rw [edgeTag_standard_of_reflection Told Tcore inOld inCore hRel μ i a]
      rfl
    _ ↔ contact Told Tcore inOld inCore μ
        i (Quotient.mk (Told.wagonSetoid μ) a) = some c :=
      gluedStandardNode_eq_core_iff
        (contact Told Tcore inOld inCore μ)
        i (Quotient.mk (Told.wagonSetoid μ) a) c
    _ ↔ wagonSharedEdgeContact oldShared coreShared i
        (Quotient.mk (Told.wagonSetoid μ) a) c := by
      exact wagonContactGlue_eq_some_iff
        (wagonSharedEdgeContact oldShared coreShared) hUnique
        i (Quotient.mk (Told.wagonSetoid μ) a) c
    _ ↔ ∃ s : Shared,
        Told.rel μ (inOld s) a ∧
        Quotient.mk (Tcore.wagonSetoid μ) (inCore i s) = c := by
      constructor
      · rintro ⟨s, hs, hc⟩
        exact ⟨s, Quotient.exact hs, hc⟩
      · rintro ⟨s, hs, hc⟩
        exact ⟨s, Quotient.sound hs, hc⟩

/-- A wagon with incident physical edges in distinct standards
comes with actual shared-edge witnesses in both standards, and
those shared edges have one and the same core wagon ancestor. -/
theorem cross_standard_wagon_two_core_incidence_witnesses
    (Told : EdgeTrainLevels OldEdge m)
    (Tcore : EdgeTrainLevels CoreEdge m)
    (inOld : Shared ↪ OldEdge)
    (inCore : I → Shared ↪ CoreEdge)
    (hShared : ∀ i : I, Nonempty Shared)
    (hRel : ∀ κ : Fin (m + 1), ∀ i s t,
      Told.rel κ (inOld s) (inOld t) ↔
        Tcore.rel κ (inCore i s) (inCore i t))
    (μ : Fin (m + 1))
    (i j : I) (hij : i ≠ j) (a b : OldEdge)
    (hSame : (physicalPictureGeneratedTrain
      Told Tcore inOld inCore hShared).rel μ
      (physicalStandardEdge inOld inCore i a)
      (physicalStandardEdge inOld inCore j b)) :
    ∃ (c : Quotient (Tcore.wagonSetoid μ)) (s t : Shared),
      Told.rel μ (inOld s) a ∧
      Told.rel μ (inOld t) b ∧
      Quotient.mk (Tcore.wagonSetoid μ) (inCore i s) = c ∧
      Quotient.mk (Tcore.wagonSetoid μ) (inCore j t) = c := by
  obtain ⟨c, hci⟩ :=
    cross_standard_wagon_has_core_tag
      Told Tcore inOld inCore hShared hRel μ i j hij a b hSame
  have hTagEq :=
    (rel_iff_edgeTag Told Tcore inOld inCore
      hShared hRel μ _ _).mp hSame
  have hcj :
      edgeTag Told Tcore inOld inCore μ
        (physicalStandardEdge inOld inCore j b) = Sum.inl c :=
    hTagEq.symm.trans hci
  obtain ⟨s, hs, hsc⟩ :=
    (edgeTag_standard_core_iff_shared_edge
      Told Tcore inOld inCore hRel μ i a c).mp hci
  obtain ⟨t, ht, htc⟩ :=
    (edgeTag_standard_core_iff_shared_edge
      Told Tcore inOld inCore hRel μ j b c).mp hcj
  exact ⟨c, s, t, hs, ht, hsc, htc⟩

end StructuralRamsey.Girth.PhysicalWagonModel
