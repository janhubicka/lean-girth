import Girth.TrainPhysicalSupportCarrierPushout
import Girth.TrainActualASharedEdges
import Girth.TrainActualACopyEdgeCover

/-!
# Actual A-support hypergraph edges are the canonical core/private carrier pushout

The underlying PHYSICAL A-support edges in a genuine free relational
attachment are SETS of ambient vertices. For irreducible A, every such
support is either the image of a core A-copy, or the image of an old
A-copy belonging to a standard picture. A standard support entirely
in the active gluing subsystem is already a core support; otherwise it
has a genuine private vertex.

The resulting presentation by genuine core A-copy carriers and
standard-indexed private old A-copy carriers is bijective to the
actual A-support edge set. No automorphism labels, arbitrary designated
copy coverage, or edge pruning occur.

This completes the purely SET-THEORETIC edge-carrier pushout bridge.
Compatibility with old/core train wagon labels, their generated
relations, part-intersection parameters and system-Girth is separate.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {UA Old Core I : Type v}

/-- Carrier of a composite copy is the image of the old carrier
under its ambient structure embedding. -/
theorem copyCarrier_comp_eq_image
    {W X : Type v}
    {A : RelStructure L UA}
    {D : RelStructure L W}
    {E : RelStructure L X}
    (g : RelStructure.Embedding D E)
    (a : RelStructure.Embedding A D) :
    (fun x : W => g x) '' copyCarrier a =
      copyCarrier (g.comp a) := by
  ext x
  constructor
  · rintro ⟨w, ⟨t, rfl⟩, rfl⟩
    exact ⟨t, rfl⟩
  · rintro ⟨t, rfl⟩
    exact ⟨a t, ⟨t, rfl⟩, rfl⟩

/-- Genuine physical A-support edge presentations: a genuine
core A-copy carrier, or one genuinely private old A-copy carrier
with its standard-picture index. -/
def GenuineACarrierPresentation
    (A : RelStructure L UA)
    (B : RelStructure L Old)
    (S : Set Old)
    (D : RelStructure L Core)
    (I : Type v) :=
  {p : PhysicalSupportCarrierPushout S I Core //
    match p with
    | .inl U => U ∈ actualACopyCarriers A D
    | .inr (_, T) => T.1 ∈ actualACopyCarriers A B}

/-- Forget the presentation and evaluate the corresponding genuine
physical support edge in the attached relational structure. -/
def genuineACarrierEval
    (A : RelStructure L UA)
    (B : RelStructure L Old)
    (S : Set Old)
    (D : RelStructure L Core)
    (f : I → RelStructure.Embedding (B.induce S) D) :
    GenuineACarrierPresentation A B S D I →
      Set (RelStructure.Attachment.Vertex S (W := Core) (I := I)) :=
  fun p => physicalSupportCarrierEval B S D f p.1

/-- Each genuine presentation evaluates to an ACTUAL A-support edge. -/
theorem genuineACarrierEval_mem
    (A : RelStructure L UA)
    (B : RelStructure L Old)
    (S : Set Old)
    (D : RelStructure L Core)
    (f : I → RelStructure.Embedding (B.induce S) D)
    (q : GenuineACarrierPresentation A B S D I) :
    genuineACarrierEval A B S D f q ∈
      actualACopyCarriers A (RelStructure.Attachment.attach B S D f) := by
  rcases q with ⟨p, hp⟩
  cases p with
  | inl U =>
      change U ∈ actualACopyCarriers A D at hp
      rcases hp with ⟨aCore, hU⟩
      refine ⟨(RelStructure.Attachment.coreEmbedding B S D f).comp aCore, ?_⟩
      change
        ((fun y : Core =>
          (RelStructure.Attachment.coreEmbedding B S D f) y) '' U) =
          copyCarrier ((RelStructure.Attachment.coreEmbedding B S D f).comp aCore)
      rw [hU]
      exact copyCarrier_comp_eq_image
        (RelStructure.Attachment.coreEmbedding B S D f) aCore
  | inr z =>
      rcases z with ⟨i, T⟩
      change T.1 ∈ actualACopyCarriers A B at hp
      rcases hp with ⟨aOld, hT⟩
      refine ⟨(RelStructure.Attachment.copyEmbedding B S D f i).comp aOld, ?_⟩
      change
        ((fun x : Old =>
          (RelStructure.Attachment.copyEmbedding B S D f i) x) '' T.1) =
          copyCarrier ((RelStructure.Attachment.copyEmbedding B S D f i).comp aOld)
      rw [hT]
      exact copyCarrier_comp_eq_image
        (RelStructure.Attachment.copyEmbedding B S D f i) aOld

/-- The physical carrier evaluation is injective on all genuine
core/private presentations, as it is on all carrier sets. -/
theorem genuineACarrierEval_injective
    (A : RelStructure L UA)
    (B : RelStructure L Old)
    (S : Set Old)
    (D : RelStructure L Core)
    (f : I → RelStructure.Embedding (B.induce S) D) :
    Function.Injective (genuineACarrierEval A B S D f) := by
  intro p q hpq
  apply Subtype.ext
  exact physicalSupportCarrierEval_injective B S D f hpq

/-- Every actual A-support edge has a genuine core/private
presentation. Full A-copies inside the shared subsystem are
represented on the core side rather than duplicated as private
edges. -/
theorem genuineACarrierEval_surjective
    (A : RelStructure L UA)
    (hA : A.Irreducible)
    (B : RelStructure L Old)
    (S : Set Old)
    (D : RelStructure L Core)
    (f : I → RelStructure.Embedding (B.induce S) D) :
    ∀ e : Set (RelStructure.Attachment.Vertex S (W := Core) (I := I)),
      e ∈ actualACopyCarriers A (RelStructure.Attachment.attach B S D f) →
      ∃ q : GenuineACarrierPresentation A B S D I,
        genuineACarrierEval A B S D f q = e := by
  classical
  intro e he
  rcases he with ⟨aNew, ha⟩
  rcases attached_actualACopyCarrier_core_or_standard
    A hA B S D f aNew with ⟨aCore, hCore⟩ | ⟨i, aOld, hStd⟩
  · refine ⟨⟨Sum.inl (copyCarrier aCore), ?_⟩, ?_⟩
    · change copyCarrier aCore ∈ actualACopyCarriers A D
      exact ⟨aCore, rfl⟩
    · change
        ((fun y : Core =>
          (RelStructure.Attachment.coreEmbedding B S D f) y) ''
            copyCarrier aCore) = e
      rw [copyCarrier_comp_eq_image]
      exact (ha.trans hCore).symm
  · by_cases hInside : ∀ u : UA, aOld u ∈ S
    · obtain ⟨aCore, hShared⟩ :=
        (attached_standardACopy_is_shared_iff
          A B S D f i aOld).mpr hInside
      refine ⟨⟨Sum.inl (copyCarrier aCore), ?_⟩, ?_⟩
      · change copyCarrier aCore ∈ actualACopyCarriers A D
        exact ⟨aCore, rfl⟩
      · change
          ((fun y : Core =>
            (RelStructure.Attachment.coreEmbedding B S D f) y) ''
              copyCarrier aCore) = e
        rw [copyCarrier_comp_eq_image]
        exact (ha.trans (hStd.trans hShared)).symm
    · push_neg at hInside
      obtain ⟨u, hu⟩ := hInside
      let T : PrivateSupportCarrier S :=
        ⟨copyCarrier aOld, ⟨aOld u, ⟨u, rfl⟩, hu⟩⟩
      refine ⟨⟨Sum.inr (i, T), ?_⟩, ?_⟩
      · change T.1 ∈ actualACopyCarriers A B
        exact ⟨aOld, rfl⟩
      · change
          ((fun x : Old =>
            (RelStructure.Attachment.copyEmbedding B S D f i) x) ''
              copyCarrier aOld) = e
        rw [copyCarrier_comp_eq_image]
        exact (ha.trans hStd).symm

/-- Every genuine A-support edge has a unique genuine carrier
presentation. In particular, this equivalence identifies actual
physical A-edges, never raw embeddings or their automorphism
labels. -/
noncomputable def actualACarrierPushoutEquiv
    (A : RelStructure L UA)
    (hA : A.Irreducible)
    (B : RelStructure L Old)
    (S : Set Old)
    (D : RelStructure L Core)
    (f : I → RelStructure.Embedding (B.induce S) D) :
    GenuineACarrierPresentation A B S D I ≃
      {e : Set (RelStructure.Attachment.Vertex S (W := Core) (I := I)) //
        e ∈ actualACopyCarriers A (RelStructure.Attachment.attach B S D f)} := by
  let φ :
      GenuineACarrierPresentation A B S D I →
        {e : Set (RelStructure.Attachment.Vertex S (W := Core) (I := I)) //
          e ∈ actualACopyCarriers A (RelStructure.Attachment.attach B S D f)} :=
    fun q => ⟨genuineACarrierEval A B S D f q,
      genuineACarrierEval_mem A B S D f q⟩
  apply Equiv.ofBijective φ
  constructor
  · intro p q hpq
    apply genuineACarrierEval_injective A B S D f
    exact congrArg Subtype.val hpq
  · rintro ⟨e, he⟩
    obtain ⟨q, hq⟩ :=
      genuineACarrierEval_surjective A hA B S D f e he
    refine ⟨q, ?_⟩
    apply Subtype.ext
    exact hq

end StructuralRamsey.Girth
