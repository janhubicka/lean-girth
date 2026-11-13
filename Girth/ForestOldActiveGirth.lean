import Girth.ForestActiveTraceBoundary
import Girth.ForestCompleteBSupportIntrinsic
import Girth.LinearityGirthTwo
import Girth.DesignatedPicture

/-!
# Old active-subsystem girth from the real designated-picture invariant

This packages the paper's argument for old active girth without
mentioning a newly constructed local Ramsey witness. The inputs
are exactly the old finite forest-completion property, A-linearity,
A-strong designated base projections, and the actual active A-edge
family (with its embedding and containment interfaces).

Each selected edge is already inside the old active carrier.
The only nontrivial trace test is for an added designated B-member.
The latter follows from the existing projected B-boundary theorem,
including membership in the B-member's own complete A-support.

This is a candidate implementation of the old-active girth
component of lemma puresubsystem. No local Lean build or axiom
audit has been run in this session.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {UA VB P X : Type v}

/-- A genuine designated B-member, represented by its complete
support of embedded A-copies, not by a mere vertex carrier. -/
def designatedPictureASupport
    (A : RelStructure L UA)
    (B : RelStructure L VB)
    (D : RelStructure L P)
    (C : StructuralRamsey.Partite.System L P X)
    (family : Set (RelStructure.Embedding B D))
    (T : HypergraphPiece X) : Prop :=
  ∃ q : DesignatedCopy B D C family,
    T = bSupportPiece A q.embedding

/-- The tested family in the structural picture invariant consists
of actual ambient A-edges and genuine designated B-supports. -/
def testedPictureABSupport
    (A : RelStructure L UA)
    (B : RelStructure L VB)
    (D : RelStructure L P)
    (C : StructuralRamsey.Partite.System L P X)
    (family : Set (RelStructure.Embedding B D))
    (T : HypergraphPiece X) : Prop :=
  (∃ a : RelStructure.Embedding A C.toRelStructure,
    T = HypergraphPiece.oneEdge (copyCarrier a)) ∨
  designatedPictureASupport A B D C family T

/-- The whole old active A-support has girth above m.

The only hypotheses on H are the genuine induced-support facts:
H is represented by ambient A-embeddings, all its edges lie in the
active carrier, and every ambient A-embedding entirely carried by
the active carrier contributes its edge to H. -/
theorem oldActiveSupport_girthGT_of_designatedCompletion
    (A : RelStructure L UA)
    (u w : UA) (huw : u ≠ w)
    (B : RelStructure L VB)
    (D : RelStructure L P)
    (C : StructuralRamsey.Partite.System L P X)
    (family : Set (RelStructure.Embedding B D))
    (e : RelStructure.Embedding A D)
    (hOldLinear : ALinear A C.toRelStructure)
    (hBaseStrong :
      ∀ q : DesignatedCopy B D C family,
        AStrong A D (copyCarrier q.base))
    (H : Set (Set X))
    (hEdgeEmb :
      ∀ z : Set X, z ∈ H →
        ∃ a : RelStructure.Embedding A C.toRelStructure,
          z = copyCarrier a)
    (hActiveSub :
      ∀ z : Set X, z ∈ H →
        z ⊆ activeCarrier A C e.toFunctionEmbedding)
    (hAllActiveEdges :
      ∀ a : RelStructure.Embedding A C.toRelStructure,
        copyCarrier a ⊆ activeCarrier A C e.toFunctionEmbedding →
          copyCarrier a ∈ H)
    (m : ℕ)
    (hComplete :
      ForestCompletionProperty
        (testedPictureABSupport A B D C family)
        (designatedPictureASupport A B D C family) m) :
    GirthGT H m := by
  classical
  have hHSub : H ⊆ supportCopies A C.toRelStructure := by
    intro z hz
    obtain ⟨a, ha⟩ := hEdgeEmb z hz
    exact ⟨a, ha⟩
  have hLinearH : LinearEdgeSet H := by
    have hGT : GirthGT H 2 :=
      girthGT_of_subset hHSub
        (girthGT_two_of_aLinear A C.toRelStructure hOldLinear)
    intro z t hz ht hzt
    exact pairwise_subsingleton_of_girthGT_two hGT hz ht hzt
  have hBig : ∀ z : Set X, z ∈ H → ¬ z.Subsingleton := by
    intro z hz hs
    obtain ⟨a, ha⟩ := hEdgeEmb z hz
    rw [ha] at hs
    exact huw (a.injective
      (hs ⟨u, rfl⟩ ⟨w, rfl⟩))
  apply girthGT_of_forestCompletion_designated_traces
    (activeCarrier A C e.toFunctionEmbedding) H m
    (testedPictureABSupport A B D C family)
    (designatedPictureASupport A B D C family)
    hComplete hLinearH hBig hActiveSub
  · intro z hz
    obtain ⟨a, ha⟩ := hEdgeEmb z hz
    left
    refine ⟨a, ?_⟩
    exact congrArg HypergraphPiece.oneEdge ha
  · intro T hT
    obtain ⟨q, hq⟩ := hT
    rw [hq]
    apply completeBSupport_smallOrWholeBoundary_of_intrinsic
      A q.embedding H (activeCarrier A C e.toFunctionEmbedding)
    exact projectedBCopy_smallOrWhole_activeBoundary
      A B D C e q.base q.lift
      (hBaseStrong q) H hAllActiveEdges

end StructuralRamsey.Girth
