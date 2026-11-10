import Girth.ACopyActualLinkDomain
import Girth.TrainActualASupportPushoutEquiv
import Girth.TrainPhysicalPictureEdgePushout

set_option autoImplicit false

/-!
# Concrete A-copy diagram nodes = actual attached physical A-support

The actual A-copy diagram has basic node types
  core:  Copy(A,D),
  shared: Copy(A,B.induce S),
  old:   Copy(A,B),
and the shared-old inclusion is the canonical induced-node map.
This compares its explicit core/private physical NODE pushout with the
already checked genuine core/private A-CARRIER pushout of the ACTUAL
relational attachment.

The key issue is that the private old nodes are exactly those whose
carrier is not contained in S. This equivalence follows from the
induced-node-map exact range theorem; point coverage alone would not do.
Distinct designated B-chart labels are never quotiented.

Composition with actualACarrierPushoutEquiv then shows that the
diagram's physical node pushout is indexed by precisely all actual
A-copies in the relational picture, with no artificial geometric
assumption beyond irreducibility and genuine induced attachment.
-/

namespace StructuralRamsey.Girth.ACopyConcretePhysicalPushout

open StructuralRamsey.RelStructure
open ACopyCanonicalSites ACopyCanonicalLinks ACopyActualLinkDomain

universe u v

variable {L : RelLanguage.{u}}
variable {UA Old Core I : Type v}

/-- The literal physical node sort in a free star of A-copy sites. -/
abbrev ActualPictureNodes
    (A : RelStructure L UA)
    (B : RelStructure L Old)
    (S : Set Old)
    (D : RelStructure L Core)
    (I : Type v) :=
  PhysicalPictureEdge (inducedNodeMap (A := A) B S) I (supportCopies A D)

/-- Convert one actual physical A-copy node into the existing concrete
core/private CARRIER presentation. The private condition is justified
by the complete induced-link domain, not a chosen edge covering. -/
noncomputable def toGenuine
    (A : RelStructure L UA)
    (B : RelStructure L Old)
    (S : Set Old)
    (D : RelStructure L Core)
    (I : Type v) :
    ActualPictureNodes A B S D I →
      GenuineACarrierPresentation A B S D I
  | .inl e => ⟨.inl e.val, e.property⟩
  | .inr ⟨i, e⟩ => by
      have hNot : ¬ e.val.val ⊆ S := by
        intro hSub
        exact e.property ((inducedNodeMap_range_iff B S e.val).mpr hSub)
      exact ⟨.inr (i,
        ⟨e.val.val, Set.not_subset.mp hNot⟩), e.val.property⟩

/-- Recover a physical A-copy node from its genuine carrier
presentation. The chosen private vertex excludes the link image. -/
noncomputable def fromGenuine
    (A : RelStructure L UA)
    (B : RelStructure L Old)
    (S : Set Old)
    (D : RelStructure L Core)
    (I : Type v) :
    GenuineACarrierPresentation A B S D I →
      ActualPictureNodes A B S D I
  | ⟨.inl U, hU⟩ =>
      .inl ⟨U, hU⟩
  | ⟨.inr (i, T), hT⟩ => by
      let e : supportCopies A B := ⟨T.val, hT⟩
      have hPrivate : e ∉ Set.range (inducedNodeMap B S) := by
        intro hIn
        have hSub : e.val ⊆ S :=
          (inducedNodeMap_range_iff B S e).mp hIn
        obtain ⟨x, hx, hn⟩ := T.property
        exact hn (hSub hx)
      exact .inr (i, ⟨e, hPrivate⟩)

/-- There is no duplicate source A-node: the explicit physical-node
pushout and the concrete carrier pushout have the same indexed sites. -/
noncomputable def physicalNodesEquivGenuine
    (A : RelStructure L UA)
    (B : RelStructure L Old)
    (S : Set Old)
    (D : RelStructure L Core)
    (I : Type v) :
    ActualPictureNodes A B S D I ≃
      GenuineACarrierPresentation A B S D I where
  toFun := toGenuine A B S D I
  invFun := fromGenuine A B S D I
  left_inv := by
    intro x
    cases x with
    | inl p =>
        apply congrArg Sum.inl
        apply Subtype.ext
        rfl
    | inr ip =>
        rcases ip with ⟨i, e⟩
        apply congrArg Sum.inr
        apply Prod.ext
        · rfl
        · apply Subtype.ext
          apply Subtype.ext
          rfl
  right_inv := by
    intro x
    rcases x with ⟨p, hp⟩
    cases p with
    | inl U =>
        apply Subtype.ext
        rfl
    | inr ip =>
        rcases ip with ⟨i, T⟩
        apply Subtype.ext
        rfl

/-- Exact physical A-copy site set of the TRUE free relational picture.
This is the direct actual-attachment counterpart of the generic
faithful-star support theorem, avoiding an additional abstract
carrier/edge overlap assertion. -/
noncomputable def actualPictureNodeSupportEquiv
    (A : RelStructure L UA)
    (hA : A.Irreducible)
    (B : RelStructure L Old)
    (S : Set Old)
    (D : RelStructure L Core)
    (f : I → Embedding (B.induce S) D) :
    ActualPictureNodes A B S D I ≃
      {e : Set (RelStructure.Attachment.Vertex S (W := Core) (I := I)) //
        e ∈ actualACopyCarriers A
          (RelStructure.Attachment.attach B S D f)} :=
  (physicalNodesEquivGenuine A B S D I).trans
    (actualACarrierPushoutEquiv A hA B S D f)

end StructuralRamsey.Girth.ACopyConcretePhysicalPushout
