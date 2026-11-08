import Girth.TrainFillingIndexedActualMPhysicalTrain
import Girth.TrainFillingSelectedRelationalStrongCover

set_option Elab.async false

/-!
# Selected old-parent edge families are exact images of genuine M support

A selected M-copy in the shortened ForestTailStage is A-strongly
induced. The old selected-picture incidence record declares every
ambient A-support edge whose carrier lies inside that selected copy.

Every such edge has at least two vertices (the source A is
nontrivial). Strong inducedness then forces it to factor through
the genuine selected M embedding, and the exact contracted support
equivalence supplies the unique original (choice, first-wagon) label.

Thus the complete selected-parent physical edge family is exactly
the range of the CONSTRUCTED selected physical edge map on all
heterogeneous first wagons. No output copyEdges_eq, image equality,
or pruning of ambient support edges is assumed. This supplies one
more concrete component of the parentwise scattering realization;
the rest of the filling and final Ramsey arrow remain separate.
-/

namespace StructuralRamsey.Girth.IndexedPrivateChoice

open StructuralRamsey.RelStructure

universe u v
variable {C V P X UA Base : Type v} {L : RelLanguage.{u}}
variable (U : C → PrivateWagonInput V P X)
variable [Nontrivial X] [Nontrivial UA]

/-- Exactly the ambient old physical edges contained in a genuinely
selected strong M-copy are images of the complete heterogeneous G0
physical first-wagon label family. This holds even when the rest of
the ambient system has additional (unselected) physical A-edges. -/
theorem selectedStageActualCopyEdges_eq_range
    (A : RelStructure L UA) (M : RelStructure L (Vertex U))
    {t : List ℕ} (T : EdgeTrainLevels P t.length) (hm : 0 < t.length)
    (hSupport : supportCopies A M = Set.range (contractedCarrier U))
    (hLinear : ∀ c : C, ∀ p q : P, p ≠ q →
      ((U c).oldCarrier p ∩ (U c).oldCarrier q).Subsingleton)
    (D : RelStructure L Base)
    (family : Set (Embedding M D))
    (allowed : Fin (t.length + 1) → Set Base)
    (S : TrainRecursiveWitness.ForestTailStage A M D family t
      (contractedPhysicalTrain U A M T hm hSupport hLinear) allowed)
    (b : DesignatedCopy M D S.system family) (hb : b ∈ S.selected) :
    {e : OldACarrierEdge A S.system.toRelStructure |
      e.1 ⊆ copyCarrier b.embedding} =
    Set.range (selectedActualMPhysicalEdgeEmbedding U A M T hm
      hSupport hLinear D family allowed S b) := by
          ext e
          constructor
          · intro hInside
            have hMeet : ¬ (e.1 ∩ copyCarrier b.embedding).Subsingleton := by
              intro hSub
              obtain ⟨a, ha⟩ := e.2
              obtain ⟨x, y, hxy⟩ := exists_pair_ne UA
              have hx : a x ∈ e.1 := by
                rw [← ha]
                exact ⟨x, rfl⟩
              have hy : a y ∈ e.1 := by
                rw [← ha]
                exact ⟨y, rfl⟩
              exact hxy (a.injective
                (hSub ⟨hx, hInside hx⟩ ⟨hy, hInside hy⟩))
            obtain ⟨s, hs⟩ :=
              selectedSupportOldEdge_mem_range_of_strong A M
                S.system.toRelStructure b.embedding (S.strong b hb) e hMeet
            obtain ⟨cp, hcp⟩ :=
              (contractedPhysicalEdgeEquiv U A M hSupport hLinear).surjective s
            refine ⟨cp, ?_⟩
            apply Subtype.ext
            change b.embedding.toFunctionEmbedding ''
              (contractedPhysicalEdgeEquiv U A M hSupport hLinear cp).1 = e.1
            calc
              _ = b.embedding.toFunctionEmbedding '' s.1 :=
                congrArg (fun E : Set (Vertex U) =>
                  b.embedding.toFunctionEmbedding '' E)
                  (congrArg Subtype.val hcp)
              _ = e.1 := congrArg Subtype.val hs
          · rintro ⟨cp, rfl⟩
            intro z hz
            change z ∈ b.embedding.toFunctionEmbedding ''
              (contractedPhysicalEdgeEquiv U A M hSupport hLinear cp).1 at hz
            obtain ⟨w, _, rfl⟩ := hz
            exact ⟨w, rfl⟩

end StructuralRamsey.Girth.IndexedPrivateChoice
