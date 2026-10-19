import Girth.TrainActualCopyLocalCoreIncidence

/-!
# Circulation: standard/core wagon boundary incidence

A standard edge and a genuine core edge in the same generated wagon
have an actual shared old edge with the same old wagon class and
whose core image belongs to the specified core wagon. This does not
construct a segmented big cycle or establish its acceptability.
No appendix input.
-/

namespace StructuralRamsey.Girth.PhysicalWagonModel

universe v
variable {I Shared OldEdge CoreEdge : Type v} {m : ℕ}

/-- A standard/core output wagon contact has a genuine gluing-edge
witness, with the precise old/core ancestor relationships. -/
theorem standard_core_wagon_incidence_witness
    (Told : EdgeTrainLevels OldEdge m)
    (Tcore : EdgeTrainLevels CoreEdge m)
    (inOld : Shared ↪ OldEdge)
    (inCore : I → Shared ↪ CoreEdge)
    (hShared : ∀ i : I, Nonempty Shared)
    (hRel : ∀ κ : Fin (m + 1), ∀ i s t,
      Told.rel κ (inOld s) (inOld t) ↔
        Tcore.rel κ (inCore i s) (inCore i t))
    (μ : Fin (m + 1)) (i : I) (a : OldEdge) (b : CoreEdge)
    (hSame : (physicalPictureGeneratedTrain
      Told Tcore inOld inCore hShared).rel μ
      (physicalStandardEdge inOld inCore i a)
      (physicalCoreEdge inOld I b)) :
    ∃ s : Shared,
      Told.rel μ (inOld s) a ∧
      Tcore.rel μ (inCore i s) b := by
  have hCoreTag :
      edgeTag Told Tcore inOld inCore μ
        (physicalCoreEdge inOld I b) =
      Sum.inl (Quotient.mk (Tcore.wagonSetoid μ) b) := by
    exact physicalCoreEdge_tag inOld
      (fun x : CoreEdge => Quotient.mk (Tcore.wagonSetoid μ) x)
      (fun x : OldEdge => Quotient.mk (Told.wagonSetoid μ) x)
      (contact Told Tcore inOld inCore μ) b
  have hTag :=
    (rel_iff_edgeTag Told Tcore inOld inCore
      hShared hRel μ _ _).mp hSame
  rw [hCoreTag] at hTag
  obtain ⟨s, hsOld, hsCore⟩ :=
    (edgeTag_standard_core_iff_shared_edge
      Told Tcore inOld inCore hRel μ i a
      (Quotient.mk (Tcore.wagonSetoid μ) b)).mp hTag
  exact ⟨s, hsOld, Quotient.exact hsCore⟩

end StructuralRamsey.Girth.PhysicalWagonModel
