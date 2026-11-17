import Girth.ForestOldActiveSetGirth
import Girth.ForestPhysicalCopySetCompletion

/-!
# The manuscript's finite sets of physical A- and B-copies

An embedding label is NOT a physical copy. The finite physical copy
type below records an A-carrier or a designated B-carrier, with a
tag distinguishing the two sorts. The support of an actual B-copy
depends only on its carrier: it is the set of ALL ambient A-copy
edges contained in that carrier.

Physical-copy completion is stated as an extension of finite SETS
of physical carriers; the output forest is indexed by its finite
set of DISTINCT complete support pieces. This exactly avoids
duplicating a multi-edge B-piece when many embeddings have the
same carrier.

No kernel check has been run for this source candidate.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {UA VB P X : Type v}

/-- The full ambient A-support on a physical vertex carrier.
For the carrier of an embedded B-copy, this is definitionally
the complete support used by bSupportPiece. -/
def physicalBCarrierSupport
    (A : RelStructure L UA)
    (C : RelStructure L X)
    (V : Set X) : HypergraphPiece X where
  carrier := V
  edges := {e | ∃ a : RelStructure.Embedding A C,
    copyCarrier a = e ∧ copyCarrier a ⊆ V}
  edge_subset_carrier := by
    intro e he
    obtain ⟨a, heq, hSub⟩ := he
    rw [← heq]
    exact hSub

/-- The complete support of a tagged physical A- or B-copy. -/
def pictureABPhysicalSupport
    (A : RelStructure L UA)
    (C : RelStructure L X) :
    (Set X ⊕ Set X) → HypergraphPiece X
  | .inl V => HypergraphPiece.oneEdge V
  | .inr V => physicalBCarrierSupport A C V

/-- Send a genuine A-embedding or designated B-embedding to its
PHYSICAL vertex carrier, retaining its A/B sort tag. -/
def pictureABPhysicalKey
    (A : RelStructure L UA)
    (B : RelStructure L VB)
    (D : RelStructure L P)
    (C : StructuralRamsey.Partite.System L P X)
    (family : Set (RelStructure.Embedding B D)) :
    (RelStructure.Embedding A C.toRelStructure ⊕
      DesignatedCopy B D C family) → (Set X ⊕ Set X)
  | .inl a => .inl (copyCarrier a)
  | .inr q => .inr (copyCarrier q.embedding)

/-- The eligible physical objects are exactly A-carriers or
carriers of actual designated B-copies. -/
def pictureABPhysicalEligible
    (A : RelStructure L UA)
    (B : RelStructure L VB)
    (D : RelStructure L P)
    (C : StructuralRamsey.Partite.System L P X)
    (family : Set (RelStructure.Embedding B D)) :
    (Set X ⊕ Set X) → Prop
  | .inl V => ∃ a : RelStructure.Embedding A C.toRelStructure,
      copyCarrier a = V
  | .inr V => ∃ q : DesignatedCopy B D C family,
      copyCarrier q.embedding = V

/-- Only designated physical B-copies may be newly added. -/
def pictureABPhysicalDesignated
    (B : RelStructure L VB)
    (D : RelStructure L P)
    (C : StructuralRamsey.Partite.System L P X)
    (family : Set (RelStructure.Embedding B D)) :
    (Set X ⊕ Set X) → Prop
  | .inl _ => False
  | .inr V => ∃ q : DesignatedCopy B D C family,
      copyCarrier q.embedding = V

/-- Complete support is determined by the physical carrier,
not by the chosen presentation as an embedding. -/
theorem pictureABLabelSupport_eq_physicalSupport
    (A : RelStructure L UA)
    (B : RelStructure L VB)
    (D : RelStructure L P)
    (C : StructuralRamsey.Partite.System L P X)
    (family : Set (RelStructure.Embedding B D))
    (label : RelStructure.Embedding A C.toRelStructure ⊕
      DesignatedCopy B D C family) :
    pictureABLabelSupport A B D C family label =
      pictureABPhysicalSupport A C.toRelStructure
        (pictureABPhysicalKey A B D C family label) := by
  cases label with
  | inl a => rfl
  | inr q => rfl

/-- Every actual embedding label has an eligible physical copy key. -/
theorem pictureABPhysicalKey_eligible
    (A : RelStructure L UA)
    (B : RelStructure L VB)
    (D : RelStructure L P)
    (C : StructuralRamsey.Partite.System L P X)
    (family : Set (RelStructure.Embedding B D))
    (label : RelStructure.Embedding A C.toRelStructure ⊕
      DesignatedCopy B D C family) :
    pictureABPhysicalEligible A B D C family
      (pictureABPhysicalKey A B D C family label) := by
  cases label with
  | inl a => exact ⟨a, rfl⟩
  | inr q => exact ⟨q, rfl⟩

/-- A designated physical B-copy maps to a permitted complete
designated B-support piece, regardless of its embedding label. -/
theorem pictureABPhysicalDesignated_support
    (A : RelStructure L UA)
    (B : RelStructure L VB)
    (D : RelStructure L P)
    (C : StructuralRamsey.Partite.System L P X)
    (family : Set (RelStructure.Embedding B D))
    (physical : Set X ⊕ Set X)
    (hDesignated : pictureABPhysicalDesignated B D C family physical) :
    designatedPictureASupport A B D C family
      (pictureABPhysicalSupport A C.toRelStructure physical) := by
  cases physical with
  | inl V =>
      exact False.elim hDesignated
  | inr V =>
      obtain ⟨q, hCarrier⟩ := hDesignated
      refine ⟨q, ?_⟩
      rw [← hCarrier]
      rfl

/-- The exact old-active girth consequence of a forest extension
property quantified over finite SETS of PHYSICAL A/B copies.

All support collisions, including several labels of one B-carrier,
are collapsed to distinct support pieces in the output forest.
The cutoff m>=2 supplies old A-linearity; the designated base
projections supply the trace boundary classification. -/
theorem oldActiveInduced_girthGT_of_physicalCopySetExtension
    (A : RelStructure L UA)
    (u w : UA) (huw : u ≠ w)
    (B : RelStructure L VB)
    (D : RelStructure L P)
    (C : StructuralRamsey.Partite.System L P X)
    (family : Set (RelStructure.Embedding B D))
    (e : RelStructure.Embedding A D)
    (hBaseStrong :
      ∀ q : DesignatedCopy B D C family,
        AStrong A D (copyCarrier q.base))
    (m : ℕ) (hm : 2 ≤ m)
    (hPhysical :
      PhysicalCopySetForestExtension
        (pictureABPhysicalSupport A C.toRelStructure)
        (pictureABPhysicalEligible A B D C family)
        (pictureABPhysicalDesignated B D C family) m) :
    GirthGT
      (supportCopies A
        (C.induce
          (activeCarrier A C e.toFunctionEmbedding)).toRelStructure) m := by
  have hLabel :
      FinsetLabelForestCompletionProperty
        (pictureABLabelSupport A B D C family)
        (fun _ => True)
        (designatedPictureASupport A B D C family) m := by
    apply PhysicalCopySetForestExtension.toLabelFinset
      hPhysical
      (pictureABPhysicalKey A B D C family)
      (pictureABLabelSupport A B D C family)
      (fun _ => True)
    · intro label
      exact pictureABLabelSupport_eq_physicalSupport
        A B D C family label
    · intro label _
      exact pictureABPhysicalKey_eligible
        A B D C family label
    · intro physical hDesignated
      exact pictureABPhysicalDesignated_support
        A B D C family physical hDesignated
  exact oldActiveInduced_girthGT_of_actualCopySets_without_oldLinear
    A u w huw B D C family e hBaseStrong m hm hLabel

end StructuralRamsey.Girth
