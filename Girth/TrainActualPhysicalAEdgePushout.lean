import Girth.TrainPhysicalPictureEdgePushout
import Girth.TrainActualASupportPushoutEquiv
import Girth.TrainSharedOldACarrierCoreEmbedding

/-!
# Genuine A-support edges as the concrete physical picture-edge pushout

The physical one-level edge pushout has shared-old-edge inclusion
and injections of shared old edges into core edges.

For actual A-copy supports, old edges are A-carriers, shared old
edges are A-carriers wholly inside the gluing subsystem, and core
edges are A-carriers of the core relational structure.

We prove this concrete physical edge type is equivalent to the
genuine core/private A-carrier presentation. Composing with the
checked equivalence of that presentation with ALL actual attached
A-support edges gives a real-edge bijection to use for train transfer.

Distinct raw A-embeddings with the same image carrier are ONE edge.
This theorem does not assert wagon relation reflection or system-Girth.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {UA Old Core I : Type v}

/-- The actual A-support physical edge pushout with its old and
core sorts specialized to genuine image carriers. -/
abbrev ActualAPicturePushoutEdge
    (A : RelStructure L UA)
    (B : RelStructure L Old)
    (S : Set Old)
    (D : RelStructure L Core)
    (I : Type v) :=
  PhysicalPictureEdge (sharedOldACarrierInclusion A B S) I
    (OldACarrierEdge A D)

/-- Convert the concrete physical support-edge label into the
genuine core/private carrier presentation. -/
noncomputable def actualAPictureToGenuine
    (A : RelStructure L UA)
    (B : RelStructure L Old)
    (S : Set Old)
    (D : RelStructure L Core)
    (I : Type v) :
    ActualAPicturePushoutEdge A B S D I →
      GenuineACarrierPresentation A B S D I
  | .inl U => ⟨Sum.inl U.1, U.2⟩
  | .inr (i, T) =>
      ⟨Sum.inr (i,
        ⟨T.1.1, (oldACarrier_not_shared_iff_private
          A B S T.1).mp T.2⟩), T.1.2⟩

/-- Replace the actual private-carrier witness with a certificate
that this old support edge is not in the shared-old-edge image. -/
noncomputable def genuineToActualAPicture
    (A : RelStructure L UA)
    (B : RelStructure L Old)
    (S : Set Old)
    (D : RelStructure L Core)
    (I : Type v) :
    GenuineACarrierPresentation A B S D I →
      ActualAPicturePushoutEdge A B S D I
  | ⟨Sum.inl U, hU⟩ => Sum.inl ⟨U, hU⟩
  | ⟨Sum.inr (i, T), hT⟩ =>
      Sum.inr (i,
        ⟨⟨T.1, hT⟩,
          (oldACarrier_not_shared_iff_private
            A B S ⟨T.1, hT⟩).mpr T.2⟩)

/-- An equivalence between the concrete physical edge pushout and
the presentation with explicit true private carrier witnesses. -/
noncomputable def actualAPictureGenuineEquiv
    (A : RelStructure L UA)
    (B : RelStructure L Old)
    (S : Set Old)
    (D : RelStructure L Core)
    (I : Type v) :
    ActualAPicturePushoutEdge A B S D I ≃
      GenuineACarrierPresentation A B S D I where
  toFun := actualAPictureToGenuine A B S D I
  invFun := genuineToActualAPicture A B S D I
  left_inv := by
    intro x
    cases x with
    | inl U =>
        rfl
    | inr z =>
        rcases z with ⟨i, T⟩
        rfl
  right_inv := by
    intro x
    rcases x with ⟨p, hp⟩
    cases p with
    | inl U =>
        rfl
    | inr z =>
        rcases z with ⟨i, T⟩
        rfl

/-- The concrete support-edge pushout is bijective to the EXACT
set of real A-support carriers in a free relational attachment. -/
noncomputable def actualAPictureEdgeEquiv
    (A : RelStructure L UA)
    (hA : A.Irreducible)
    (B : RelStructure L Old)
    (S : Set Old)
    (D : RelStructure L Core)
    (f : I → RelStructure.Embedding (B.induce S) D) :
    ActualAPicturePushoutEdge A B S D I ≃
      {e : Set (RelStructure.Attachment.Vertex S
          (W := Core) (I := I)) //
        e ∈ actualACopyCarriers A
          (RelStructure.Attachment.attach B S D f)} :=
  (actualAPictureGenuineEquiv A B S D I).trans
    (actualACarrierPushoutEquiv A hA B S D f)

end StructuralRamsey.Girth
