import Girth.ForestMarkedSupportTransport
import Girth.ForestImage
import Mathlib.Tactic

/-!
# Multi-owner standard-copy transport and the joint forest kernel

In a genuine partite picture step the selected B-copies need not live
inside ONE standard copy. Each has its own owner q and a corresponding
injective standard embedding phi_q of the old picture.

We tag old vertices by their selected member index c. The evaluations
(c,x) ↦ phi_(owner c)(x) remember all cross-owner coincidences.
If two such standard-embedding configurations have the SAME equality
kernel on this JOINT tagged domain, the exact finite forest property
of their selected support pieces is the same.

This is strictly more general than applying one injective ambient map
to the entire family. The nontrivial remaining train task is to show
the gluing geometry yields the requisite cross-owner kernel agreement
through the proposed history reductions, without freezing all
retrospective profiles under every free-successor shape map.
-/

namespace StructuralRamsey.Girth

universe v
variable {Old W Z Q C : Type v}

/-- Evaluation of an old vertex carrying a selected B-copy owner tag. -/
def ownerTaggedVertex
    (owner : C → Q) (φ : Q → Old ↪ W) :
    C × Old → W :=
  fun p => φ (owner p.1) p.2

/-- Tagged old vertices comprising one selected support piece. -/
def ownerTaggedCarrier
    (P : C → HypergraphPiece Old) (c : C) : Set (C × Old) :=
  {p | p.1 = c ∧ p.2 ∈ (P c).carrier}

/-- Tagged intrinsic A-support atoms of one selected old piece. -/
def ownerTaggedAtoms
    (P : C → HypergraphPiece Old) (c : C) :
    Set (Set (C × Old)) :=
  {a | ∃ e ∈ (P c).edges, a = {p | p.1 = c ∧ p.2 ∈ e}}

/-- A standard-copy image's full carrier is the evaluation of the
corresponding tagged old carrier. -/
theorem ownerTagged_carrier_eq_image
    (P : C → HypergraphPiece Old)
    (owner : C → Q) (φ : Q → Old ↪ W) (c : C) :
    ((P c).map (φ (owner c))).carrier =
      ownerTaggedVertex owner φ '' ownerTaggedCarrier P c := by
  change (φ (owner c)) '' (P c).carrier =
    ownerTaggedVertex owner φ '' ownerTaggedCarrier P c
  ext y
  constructor
  · rintro ⟨x, hx, hxy⟩
    exact ⟨(c, x), ⟨rfl, hx⟩, hxy⟩
  · rintro ⟨⟨d, x⟩, hd, hxy⟩
    have hdc : d = c := hd.1
    subst d
    exact ⟨x, hd.2, hxy⟩

/-- Evaluating a tagged old support edge is the corresponding
physical support edge of its owner's standard picture. -/
theorem ownerTagged_image_atom
    (owner : C → Q) (φ : Q → Old ↪ W)
    (c : C) (e : Set Old) :
    ownerTaggedVertex owner φ ''
      {p : C × Old | p.1 = c ∧ p.2 ∈ e} =
      (φ (owner c)) '' e := by
  ext y
  constructor
  · rintro ⟨⟨d, x⟩, hd, hxy⟩
    have hdc : d = c := hd.1
    subst d
    exact ⟨x, hd.2, hxy⟩
  · rintro ⟨x, hx, hxy⟩
    exact ⟨(c, x), ⟨rfl, hx⟩, hxy⟩

/-- The support edges of each standard-copy image are precisely
evaluations of its fixed old intrinsic support atoms. -/
theorem ownerTagged_edges_eq_atoms
    (P : C → HypergraphPiece Old)
    (owner : C → Q) (φ : Q → Old ↪ W)
    (c : C) (e : Set W) :
    e ∈ ((P c).map (φ (owner c))).edges ↔
      ∃ a ∈ ownerTaggedAtoms P c,
        e = ownerTaggedVertex owner φ '' a := by
  constructor
  · rintro ⟨e0, he0, hEq⟩
    refine ⟨{p : C × Old | p.1 = c ∧ p.2 ∈ e0},
      ⟨e0, he0, rfl⟩, ?_⟩
    calc
      e = (φ (owner c)) '' e0 := hEq
      _ = ownerTaggedVertex owner φ ''
        {p : C × Old | p.1 = c ∧ p.2 ∈ e0} :=
        (ownerTagged_image_atom owner φ c e0).symm
  · rintro ⟨a, ⟨e0, he0, ha⟩, hEq⟩
    subst a
    exact ⟨e0, he0,
      hEq.trans (ownerTagged_image_atom owner φ c e0)⟩

/-- The same tagged intrinsic presentation works across two
independently chosen families of standard-picture embeddings. -/
theorem ownerTagged_sameMarkedSupportPresentation
    (P : C → HypergraphPiece Old)
    (owner : C → Q)
    (φ : Q → Old ↪ W) (ψ : Q → Old ↪ Z) :
    SameMarkedSupportPresentation
      (fun c => (P c).map (φ (owner c)))
      (fun c => (P c).map (ψ (owner c)))
      (ownerTaggedVertex owner φ)
      (ownerTaggedVertex owner ψ)
      (ownerTaggedCarrier P)
      (ownerTaggedAtoms P) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro c
    exact ownerTagged_carrier_eq_image P owner φ c
  · intro c
    exact ownerTagged_carrier_eq_image P owner ψ c
  · intro c e
    exact ownerTagged_edges_eq_atoms P owner φ c e
  · intro c e
    exact ownerTagged_edges_eq_atoms P owner ψ c e

/-- Complete forest geometry for a finite family of B-pieces is
invariant under any change of owner embeddings which preserves the
FULL joint equality kernel of their tagged old vertices. No single
global vertex embedding between the two hosts is assumed. -/
theorem forestOfCopies_ownerMaps_iff_of_jointKernel
    [Fintype C]
    (P : C → HypergraphPiece Old)
    (owner : C → Q)
    (φ : Q → Old ↪ W) (ψ : Q → Old ↪ Z)
    (hKernel : SameMarkedKernel
      (ownerTaggedVertex owner φ)
      (ownerTaggedVertex owner ψ)) :
    ForestOfCopies (fun c => (P c).map (φ (owner c))) ↔
      ForestOfCopies (fun c => (P c).map (ψ (owner c))) := by
  exact markedFamily_forest_iff_of_supportPresentation
    (fun c => (P c).map (φ (owner c)))
    (fun c => (P c).map (ψ (owner c)))
    (ownerTaggedVertex owner φ)
    (ownerTaggedVertex owner ψ) hKernel
    (ownerTaggedCarrier P) (ownerTaggedAtoms P)
    (ownerTagged_sameMarkedSupportPresentation P owner φ ψ)

/-- The geometric requirement can be stated as explicit pairwise
cross-owner identifications, including identical owners and distinct
owners. This is the actual gluing-kernel condition to establish for
train pictures. -/
theorem forestOfCopies_ownerMaps_iff_of_crossOwnerAgreement
    [Fintype C]
    (P : C → HypergraphPiece Old)
    (owner : C → Q)
    (φ : Q → Old ↪ W) (ψ : Q → Old ↪ Z)
    (hAgreement : ∀ c d : C, ∀ x y : Old,
      φ (owner c) x = φ (owner d) y ↔
        ψ (owner c) x = ψ (owner d) y) :
    ForestOfCopies (fun c => (P c).map (φ (owner c))) ↔
      ForestOfCopies (fun c => (P c).map (ψ (owner c))) := by
  apply forestOfCopies_ownerMaps_iff_of_jointKernel P owner φ ψ
  intro i j
  exact hAgreement i.1 j.1 i.2 j.2

end StructuralRamsey.Girth
