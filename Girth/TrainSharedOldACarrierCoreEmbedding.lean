import Girth.TrainActualSharedACarrierSubfamily
import Girth.TrainActualSupportCarrierUniqueness

/-!
# Canonical embedding of genuine shared old A-support edges into core A-support

The concrete physical train pushout requires not just the injection
of shared old A-support carriers into all old A-support edges, but also
an injection into the actual core A-support carriers for each standard
picture index.

A genuine shared old A-edge has a complete old carrier contained in the
gluing subsystem. Its standard image is therefore exactly the image
of a genuine CORE A-copy carrier. That core carrier is unique because
the core embedding into the attachment is injective on vertex sets.

We construct this map without choosing a label for a raw A-embedding.
Classical choice selects an actual core CARRIER witnessing the image;
the unique image means the choice cannot change its physical value.
The resulting map is injective because the standard vertex embedding
is injective on carrier sets as well.

This is the required true shared-to-core support-edge embedding for
the one-cut physical edge-pushout model. Preserving and reflecting
train wagon relations on its image is a separate assumption to check.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {UA Old Core I : Type v}

/-- Every genuine shared OLD A-support carrier transports to the
image of an ACTUAL core A-support carrier. -/
theorem sharedOldACarrier_exists_coreImage
    (A : RelStructure L UA)
    (B : RelStructure L Old)
    (S : Set Old)
    (D : RelStructure L Core)
    (f : I → RelStructure.Embedding (B.induce S) D)
    (i : I)
    (T : SharedOldACarrierEdge A B S) :
    ∃ U : OldACarrierEdge A D,
      ((fun x : Old =>
        (RelStructure.Attachment.copyEmbedding B S D f i) x) '' T.1.1) =
      ((fun y : Core =>
        (RelStructure.Attachment.coreEmbedding B S D f) y) '' U.1) := by
  have hShared :
      T.1 ∈ Set.range (sharedOldACarrierInclusion A B S) :=
    (oldACarrier_mem_shared_range_iff A B S T.1).mpr T.2
  obtain ⟨aCore, hImage⟩ :=
    (oldACarrier_shared_iff_actual_core A B S D f i T.1).mp hShared
  refine ⟨⟨copyCarrier aCore, ⟨aCore, rfl⟩⟩, ?_⟩
  change
    ((fun x : Old =>
      (RelStructure.Attachment.copyEmbedding B S D f i) x) '' T.1.1) =
    ((fun y : Core =>
      (RelStructure.Attachment.coreEmbedding B S D f) y) ''
        copyCarrier aCore)
  exact hImage.trans (copyCarrier_comp_eq_image
    (RelStructure.Attachment.coreEmbedding B S D f) aCore)

/-- Map genuine shared old A-support carriers to their unique
corresponding core A-support carrier. -/
noncomputable def sharedOldACarrierCoreMap
    (A : RelStructure L UA)
    (B : RelStructure L Old)
    (S : Set Old)
    (D : RelStructure L Core)
    (f : I → RelStructure.Embedding (B.induce S) D)
    (i : I) :
    SharedOldACarrierEdge A B S → OldACarrierEdge A D :=
  fun T => Classical.choose (sharedOldACarrier_exists_coreImage
    A B S D f i T)

/-- The chosen core carrier is characterized by the equality of its
ACTUAL physical image with the entire old shared carrier image. -/
theorem sharedOldACarrierCoreMap_image
    (A : RelStructure L UA)
    (B : RelStructure L Old)
    (S : Set Old)
    (D : RelStructure L Core)
    (f : I → RelStructure.Embedding (B.induce S) D)
    (i : I)
    (T : SharedOldACarrierEdge A B S) :
    ((fun x : Old =>
      (RelStructure.Attachment.copyEmbedding B S D f i) x) '' T.1.1) =
    ((fun y : Core =>
      (RelStructure.Attachment.coreEmbedding B S D f) y) ''
        (sharedOldACarrierCoreMap A B S D f i T).1) :=
  Classical.choose_spec (sharedOldACarrier_exists_coreImage
    A B S D f i T)

/-- Distinct genuine shared old carriers map to distinct core
A-support carriers, since the standard embedding reflects equality
of physical carrier images. -/
theorem sharedOldACarrierCoreMap_injective
    (A : RelStructure L UA)
    (B : RelStructure L Old)
    (S : Set Old)
    (D : RelStructure L Core)
    (f : I → RelStructure.Embedding (B.induce S) D)
    (i : I) :
    Function.Injective (sharedOldACarrierCoreMap A B S D f i) := by
  intro T U hEq
  have hImages :
      ((fun x : Old =>
        (RelStructure.Attachment.copyEmbedding B S D f i) x) '' T.1.1) =
      ((fun x : Old =>
        (RelStructure.Attachment.copyEmbedding B S D f i) x) '' U.1.1) := by
    calc
      _ = ((fun y : Core =>
             (RelStructure.Attachment.coreEmbedding B S D f) y) ''
             (sharedOldACarrierCoreMap A B S D f i T).1) :=
        sharedOldACarrierCoreMap_image A B S D f i T
      _ = ((fun y : Core =>
             (RelStructure.Attachment.coreEmbedding B S D f) y) ''
             (sharedOldACarrierCoreMap A B S D f i U).1) :=
        congrArg (fun X : OldACarrierEdge A D =>
          (fun y : Core =>
            (RelStructure.Attachment.coreEmbedding B S D f) y) '' X.1) hEq
      _ = ((fun x : Old =>
             (RelStructure.Attachment.copyEmbedding B S D f i) x) '' U.1.1) :=
        (sharedOldACarrierCoreMap_image A B S D f i U).symm
  have hCarriers : T.1.1 = U.1.1 :=
    supportCarrier_image_eq_of_injective
      (fun x : Old =>
        (RelStructure.Attachment.copyEmbedding B S D f i) x)
      (RelStructure.Attachment.copyEmbedding B S D f i).injective hImages
  apply Subtype.ext
  apply Subtype.ext
  exact hCarriers

/-- The canonical genuine shared-to-core support-edge EMBEDDING. -/
noncomputable def sharedOldACarrierCoreEmbedding
    (A : RelStructure L UA)
    (B : RelStructure L Old)
    (S : Set Old)
    (D : RelStructure L Core)
    (f : I → RelStructure.Embedding (B.induce S) D)
    (i : I) :
    SharedOldACarrierEdge A B S ↪ OldACarrierEdge A D where
  toFun := sharedOldACarrierCoreMap A B S D f i
  inj' := sharedOldACarrierCoreMap_injective A B S D f i

end StructuralRamsey.Girth
