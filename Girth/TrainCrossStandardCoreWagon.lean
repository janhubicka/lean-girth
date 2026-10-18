import Girth.TrainPhysicalWagonQuotientModel

/-!
# Circulation: cross-standard wagon connectors have core tags

At one horizontal cut, a physical output wagon that meets two distinct
attached standards through genuine edges is a SHARED core-tagged wagon,
not a private wagon of either standard. This follows from the actual
generated edge-equivalence normal form, not from equal vertex carriers
or exact restriction inside one standard.

For shared output wagon classes, the core tag is injective because the
actual quotient-to-tag map is injective. These two lemmas reduce the
remaining cross-standard boundary-connector obligation in Section 12
to the PHYSICAL incidence witnesses of its retained boundary wagons.

No assertion about a legal reduct cycle, cyclic segmentation, A1--A3,
or cycle transfer is made. No appendix theorem is used.
-/

namespace StructuralRamsey.Girth.PhysicalWagonModel

universe v
variable {I Shared OldEdge CoreEdge : Type v} {m : ℕ}

/-- Every actual old-standard edge is tagged by its genuine old
wagon ancestor, mapped into the common core precisely when the
shared-edge contact identifies that ancestor. -/
theorem edgeTag_standard_of_reflection
    (Told : EdgeTrainLevels OldEdge m)
    (Tcore : EdgeTrainLevels CoreEdge m)
    (inOld : Shared ↪ OldEdge)
    (inCore : I → Shared ↪ CoreEdge)
    (hRel : ∀ κ : Fin (m + 1), ∀ i s t,
      Told.rel κ (inOld s) (inOld t) ↔
        Tcore.rel κ (inCore i s) (inCore i t))
    (μ : Fin (m + 1)) (i : I) (a : OldEdge) :
    edgeTag Told Tcore inOld inCore μ
        (physicalStandardEdge inOld inCore i a) =
      gluedStandardNode (contact Told Tcore inOld inCore μ) i
        (Quotient.mk (Told.wagonSetoid μ) a) := by
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
  have hContact : ∀ j s,
      contact Told Tcore inOld inCore μ j
          (Quotient.mk (Told.wagonSetoid μ) (inOld s)) =
        some (Quotient.mk (Tcore.wagonSetoid μ) (inCore j s)) := by
    intro j s
    change wagonContactGlue (wagonSharedEdgeContact oldShared coreShared)
        j (oldShared j s) = some (coreShared j s)
    apply (wagonContactGlue_eq_some_iff
      (wagonSharedEdgeContact oldShared coreShared)
      hUnique j (oldShared j s) (coreShared j s)).mpr
    exact ⟨s, rfl, rfl⟩
  exact physicalStandardEdge_tag inOld inCore
    (Quotient.mk (Tcore.wagonSetoid μ))
    (Quotient.mk (Told.wagonSetoid μ))
    (contact Told Tcore inOld inCore μ) hContact i a

/-- If one actual generated wagon contains edges coming from
two different standards, that wagon necessarily has a shared core
tag. Private tags remember the standard index and cannot cross. -/
theorem cross_standard_wagon_has_core_tag
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
    ∃ c : Quotient (Tcore.wagonSetoid μ),
      edgeTag Told Tcore inOld inCore μ
        (physicalStandardEdge inOld inCore i a) = Sum.inl c := by
  have heq :=
    (rel_iff_edgeTag Told Tcore inOld inCore
      hShared hRel μ _ _).mp hSame
  rw [edgeTag_standard_of_reflection Told Tcore inOld inCore hRel μ i a,
      edgeTag_standard_of_reflection Told Tcore inOld inCore hRel μ j b] at heq
  obtain ⟨c, hc, _⟩ :=
    gluedStandardNode_shared_of_distinct_indices
      (contact Told Tcore inOld inCore μ) i j hij
      (Quotient.mk (Told.wagonSetoid μ) a)
      (Quotient.mk (Told.wagonSetoid μ) b) heq
  refine ⟨c, ?_⟩
  rw [edgeTag_standard_of_reflection Told Tcore inOld inCore hRel μ i a]
  simp [gluedStandardNode, hc]

/-- Exact global criterion for the problematic retained connectors:
distinct ACTUAL output wagon classes with shared core tags cannot
contract to the same core wagon. It remains to exhibit their physical
cross-standard incidence witnesses in the segmented cycle. -/
theorem different_shared_classes_have_different_core_tags
    (Told : EdgeTrainLevels OldEdge m)
    (Tcore : EdgeTrainLevels CoreEdge m)
    (inOld : Shared ↪ OldEdge)
    (inCore : I → Shared ↪ CoreEdge)
    (hShared : ∀ i : I, Nonempty Shared)
    (hRel : ∀ κ : Fin (m + 1), ∀ i s t,
      Told.rel κ (inOld s) (inOld t) ↔
        Tcore.rel κ (inCore i s) (inCore i t))
    (μ : Fin (m + 1))
    (p q : Quotient ((physicalPictureGeneratedTrain
      Told Tcore inOld inCore hShared).wagonSetoid μ))
    (c d : Quotient (Tcore.wagonSetoid μ))
    (hp : classTag Told Tcore inOld inCore hShared hRel μ p = Sum.inl c)
    (hq : classTag Told Tcore inOld inCore hShared hRel μ q = Sum.inl d)
    (hpq : p ≠ q) :
    c ≠ d := by
  intro hcd
  apply hpq
  apply (classTag Told Tcore inOld inCore hShared hRel μ).injective
  calc
    classTag Told Tcore inOld inCore hShared hRel μ p =
        Sum.inl c := hp
    _ = Sum.inl d := congrArg Sum.inl hcd
    _ = classTag Told Tcore inOld inCore hShared hRel μ q := hq.symm

end StructuralRamsey.Girth.PhysicalWagonModel
