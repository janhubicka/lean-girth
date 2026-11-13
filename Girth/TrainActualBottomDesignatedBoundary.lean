import Girth.TrainActualBottomForestGeometry
import Girth.ActiveBoundary
import Girth.AttachmentGeometry

set_option autoImplicit false
set_option Elab.async false

/-!
# Exact complete boundary of an attached selected B-label at bottom

The standard/core overlap of ANY selected subcarrier is exactly the
standard image of its old intersection with the active subsystem. This
is a raw relational attachment lemma: the local witness need not itself
be presented as a Partite.System.

For selected projected B-labels, the existing active-boundary theorem
and the genuine A-support edge inside B give a SmallOrWholeEdgeBoundary.
For the mixed-singleton contradiction we only need K=Set.univ: the
overlap must be an edge OWNED BY B, not carry an extra labelled
core-edge identifier. No girth or Ramsey conclusion is assumed.
-/

namespace StructuralRamsey.Girth
open StructuralRamsey.RelStructure

universe u v

/-- A standard subcarrier meets the core in the image of precisely its
original active-subsystem part. Unlike the whole-standard identity, this
holds for arbitrary chosen subcarriers, including designated B-copies. -/
theorem attachment_subcarrier_core_intersection
    {L : RelLanguage.{u}} {X Y I : Type v}
    (B : RelStructure L X) (S : Set X) (R : RelStructure L Y)
    (f : I → RelStructure.Embedding (B.induce S) R)
    (i : I) (Q : Set X) :
    (fun x : X => RelStructure.Attachment.copyEmbedding B S R f i x) '' Q ∩
        copyCarrier (RelStructure.Attachment.coreEmbedding B S R f) =
      (fun x : X => RelStructure.Attachment.copyEmbedding B S R f i x) '' (Q ∩ S) := by
  classical
  ext z
  constructor
  · rintro ⟨⟨x, hx, hEq⟩, ⟨y, hy⟩⟩
    have hMap :
        RelStructure.Attachment.copyMap B S R f i x = Sum.inl y :=
      hEq.trans hy.symm
    have hxS : x ∈ S :=
      RelStructure.Attachment.mem_of_copyMap_eq_inl hMap
    exact ⟨x, ⟨hx, hxS⟩, hEq⟩
  · rintro ⟨x, ⟨hx, hxS⟩, rfl⟩
    constructor
    · exact ⟨x, hx, rfl⟩
    · let sx : S := ⟨x, hxS⟩
      refine ⟨f i sx, ?_⟩
      exact (RelStructure.Attachment.copy_extends B S R f i sx).symm

section ActualSelectedBottomBoundary

variable {L : RelLanguage.{u}} {UA VB P X Y I : Type v}
variable (A : RelStructure L UA) (hA : A.Irreducible)
variable (B : RelStructure L VB) (D : RelStructure L P)
variable (C : StructuralRamsey.Partite.System L P X)
variable (family : Set (RelStructure.Embedding B D))
variable (selected : Set (DesignatedCopy B D C family))
variable (e : RelStructure.Embedding A D) (R : RelStructure L Y)
variable (f : I → RelStructure.Embedding
  (C.toRelStructure.induce (activeCarrier A C e.toFunctionEmbedding)) R)
variable {m : ℕ}
variable (T : EdgeTrainLevels (OldACarrierEdge A C.toRelStructure) m)
variable (U : EdgeTrainLevels (OldACarrierEdge A R) m)
variable (hShared : ∀ _i : I, Nonempty
  (SharedOldACarrierEdge A C.toRelStructure
    (activeCarrier A C e.toFunctionEmbedding)))

local notation "S" => activeCarrier A C e.toFunctionEmbedding
local notation "Actual" => RelStructure.Attachment.attach C.toRelStructure S R f
local notation "ActualEdge" => OldACarrierEdge A Actual
local notation "Selected" => {q : DesignatedCopy B D C family // q ∈ selected}
local notation "Std" => RelStructure.Attachment.copyEmbedding C.toRelStructure S R f
local notation "Core" => RelStructure.Attachment.coreEmbedding C.toRelStructure S R f
local notation "μBottom" => (⟨0, Nat.zero_lt_succ m⟩ : Fin (m + 1))
local notation "Out" => attachedSelectedPictureOrderOneData
  A hA B D C family selected e R f T U hShared μBottom

/-- The designated original B-copy's complete core boundary is a
singleton or one of its OWN actual physical A-support edges. The
ambient set of allowed boundary edges may be Set.univ here. -/
theorem attachedSelectedPicture_bottom_designated_boundary
    (H : (Out).BottomForestGeometry)
    (hStrong : ∀ q : Selected, AStrong A D (copyCarrier q.1.base)) :
    ∀ a : (I × Selected) ⊕ ActualEdge, (Out).designated a →
      SmallOrWholeEdgeBoundary
        (Set.univ : Set (Set (RelStructure.Attachment.Vertex S (W := Y) (I := I))))
        (copyCarrier Core)
        ((Out).bottomForestPiece H a) := by
  intro label hDes
  cases label with
  | inr edge =>
      cases hDes
  | inl iq =>
      rcases iq with ⟨i, q⟩
      have hClass :=
        projectedCopy_activeCarrier_intersection_classify
          A B D C e q.1.base q.1.lift (hStrong q)
      have hIntersection :
          ((fun x : X => Std i x) '' copyCarrier q.1.embedding) ∩
              copyCarrier Core =
            (fun x : X => Std i x) ''
              (copyCarrier q.1.embedding ∩ S) :=
        attachment_subcarrier_core_intersection
          C.toRelStructure S R f i (copyCarrier q.1.embedding)
      rcases hClass with hSmall | ⟨aB, hWhole⟩
      · left
        change (((fun x : X => Std i x) '' copyCarrier q.1.embedding) ∩
          copyCarrier Core).Subsingleton
        rw [hIntersection]
        intro z hz w hw
        obtain ⟨x, hx, rfl⟩ := hz
        obtain ⟨y, hy, rfl⟩ := hw
        exact congrArg (Std i) (hSmall hx hy)
      · let oldA : RelStructure.Embedding A C.toRelStructure :=
          q.1.embedding.comp aB
        let imageA : RelStructure.Embedding A Actual :=
          (Std i).comp oldA
        let edge : ActualEdge :=
          ⟨copyCarrier imageA, ⟨imageA, rfl⟩⟩
        have he : edge ∈ (Out).edges (Sum.inl (i, q)) := by
          change edge.1 ⊆
            (fun x : X => Std i x) '' copyCarrier q.1.embedding
          rw [show edge.1 =
            (fun x : X => Std i x) '' copyCarrier oldA from
              copyCarrier_comp_eq_image (Std i) oldA]
          apply Set.image_mono
          rintro z ⟨b, rfl⟩
          exact ⟨aB b, rfl⟩
        right
        refine ⟨edge.1, Set.mem_univ _, ⟨edge, he, rfl⟩, ?_⟩
        change (((fun x : X => Std i x) '' copyCarrier q.1.embedding) ∩
            copyCarrier Core) = edge.1
        rw [hIntersection, hWhole]
        exact (copyCarrier_comp_eq_image (Std i) oldA).symm

end ActualSelectedBottomBoundary

end StructuralRamsey.Girth
