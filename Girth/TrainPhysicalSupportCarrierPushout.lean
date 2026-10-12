import Girth.TrainActualSupportCarrierUniqueness

/-!
# Canonical edge-CARRIER pushout is physically injective

At the vertex level a free relational attachment is core vertices
plus private vertices indexed by their standard-copy owner. The
physical carrier of a core edge is its vertex image, and each old
edge carrier with an off-gluing vertex has a private image.

This module models ALL set-valued edge carriers, not embedding
labels: a core carrier U or an index i together with an old carrier
T having at least one vertex outside the gluing subsystem S.
The evaluation into actual vertex SETS is injective. The proof
uses precisely:
* injectivity of core/standard vertex maps on carrier sets;
* a private carrier cannot equal any core carrier;
* equal private carriers have the same standard-copy index.

Restricting this injective evaluation to genuine A-copy carriers
will give the desired injective physical A-edge pushout, once its
surjective support cover and shared-edge characterization are
identified with the real attachment (separate Lean modules).
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {Old Core I : Type v}

/-- An old support carrier with a real private vertex. -/
abbrev PrivateSupportCarrier (S : Set Old) :=
  {T : Set Old // ∃ x : Old, x ∈ T ∧ x ∉ S}

/-- Disjoint presentation of physical support carriers: whole
core carriers and genuinely private old carriers with owner index. -/
abbrev PhysicalSupportCarrierPushout
    (S : Set Old) (I Core : Type v) :=
  Set Core ⊕ (I × PrivateSupportCarrier S)

/-- Evaluate a presented support carrier as the actual set of
physical vertices in the free relational attachment. -/
def physicalSupportCarrierEval
    (B : RelStructure L Old)
    (S : Set Old)
    (D : RelStructure L Core)
    (f : I → RelStructure.Embedding (B.induce S) D) :
    PhysicalSupportCarrierPushout S I Core →
      Set (RelStructure.Attachment.Vertex S (W := Core) (I := I))
  | .inl U =>
      (fun y : Core =>
        (RelStructure.Attachment.coreEmbedding B S D f) y) '' U
  | .inr (i, T) =>
      (fun x : Old =>
        (RelStructure.Attachment.copyEmbedding B S D f i) x) '' T.1

/-- The concrete physical evaluation NEVER identifies distinct
core support carriers, distinct private standard owners, or
distinct carriers within the same standard copy. Thus the
shared/private carrier representation is an actual injection. -/
theorem physicalSupportCarrierEval_injective
    (B : RelStructure L Old)
    (S : Set Old)
    (D : RelStructure L Core)
    (f : I → RelStructure.Embedding (B.induce S) D) :
    Function.Injective (physicalSupportCarrierEval B S D f) := by
  intro a b hab
  cases a with
  | inl U =>
      cases b with
      | inl V =>
          have hUV : U = V :=
            supportCarrier_image_eq_of_injective
              (fun y : Core =>
                (RelStructure.Attachment.coreEmbedding B S D f) y)
              (RelStructure.Attachment.coreEmbedding B S D f).injective
              hab
          cases hUV
          rfl
      | inr z =>
          rcases z with ⟨i, T⟩
          exfalso
          exact
            (attachment_privateStandardCarrier_ne_core
              B S D f i T.1 U T.2) hab.symm
  | inr z =>
      rcases z with ⟨i, T⟩
      cases b with
      | inl U =>
          exfalso
          exact
            (attachment_privateStandardCarrier_ne_core
              B S D f i T.1 U T.2) hab
      | inr z =>
          rcases z with ⟨j, U⟩
          have hij : i = j :=
            attachment_privateStandardCarrier_unique_index
              B S D f i j T.1 U.1 T.2 hab
          subst j
          have hTU : T.1 = U.1 :=
            (attachment_standardCarrier_image_eq_iff
              B S D f i T.1 U.1).mp hab
          have hSub : T = U := Subtype.ext hTU
          cases hSub
          rfl

end StructuralRamsey.Girth
