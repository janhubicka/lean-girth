import Girth.ActiveCarrierStrong
import Girth.TrainActualStandardNoNewPair

/-!
# A-strongness of actual attached standards from the circulation base

The zero-cut supreme-plan lift needs A-strongness of the whole
attached standard, not just an induced relational embedding.

At a picture step, the current picture is genuinely partite over
an A-linear base and the chosen base A-copy is rigid. Therefore
the TRUE active gluing subsystem S is A-strong in the old picture,
by the previously verified activeCarrier theorem. Separately, the
partite local witness is required to have each entire gluing-copy
image f_i(S) A-strong in the core. The existing free-attachment
strongness theorem then establishes A-strongness of every attached
standard and hence reflection of every real ambient A-support edge
through two distinct standard vertices.

This is a small interface lemma for the actual induction; the
hypothesis that the local witness has A-strong WHOLE gluing copies
is not deduced from mixed forest intersections on small B-copies.
No appendix.
-/

namespace StructuralRamsey.Girth
open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}} {UA P X Y I : Type v}

/-- An actual standard in a true A-partite picture attachment is
A-strong whenever the base is A-linear/rigid and the entire
prescribed gluing images are A-strong in the local witness. -/
theorem activeAttached_standard_aStrong_of_base_aLinear
    (A : RelStructure L UA)
    (hA : A.Irreducible)
    (D : RelStructure L P)
    (C : StructuralRamsey.Partite.System L P X)
    (hPartite : C.IsPartiteOver D)
    (hLinear : ALinear A D)
    (e : RelStructure.Embedding A D)
    (hRigid : ∀ b : RelStructure.Embedding A D,
      SameCopy b e → b = e)
    (R : RelStructure L Y)
    (f : I → RelStructure.Embedding
      (C.toRelStructure.induce (activeCarrier A C e.toFunctionEmbedding)) R)
    (hCoreStrong : ∀ i : I, AStrong A R (copyCarrier (f i)))
    (i : I) :
    AStrong A
      (RelStructure.Attachment.attach C.toRelStructure
        (activeCarrier A C e.toFunctionEmbedding) R f)
      (copyCarrier
        (RelStructure.Attachment.copyEmbedding C.toRelStructure
          (activeCarrier A C e.toFunctionEmbedding) R f i)) := by
  have hOldStrong :
      AStrong A C.toRelStructure
        (activeCarrier A C e.toFunctionEmbedding) :=
    activeCarrier_aStrong_of_base_aLinear
      A D C hA hPartite hLinear e hRigid
  exact attachment_copy_aStrong
    C.toRelStructure (activeCarrier A C e.toFunctionEmbedding) R f
    hA hOldStrong hCoreStrong i

/-- The same explicit inductive geometry supplies the precise
distinct-boundary pair-edge reflection needed by long supreme
replacement pieces. This rules out a new ambient A-edge through
two actual attached standard vertices. -/
theorem activeAttached_standard_pairEdge_back_of_base_aLinear
    (A : RelStructure L UA)
    (hA : A.Irreducible)
    (D : RelStructure L P)
    (C : StructuralRamsey.Partite.System L P X)
    (hPartite : C.IsPartiteOver D)
    (hLinear : ALinear A D)
    (e : RelStructure.Embedding A D)
    (hRigid : ∀ b : RelStructure.Embedding A D,
      SameCopy b e → b = e)
    (R : RelStructure L Y)
    (f : I → RelStructure.Embedding
      (C.toRelStructure.induce (activeCarrier A C e.toFunctionEmbedding)) R)
    (hCoreStrong : ∀ i : I, AStrong A R (copyCarrier (f i)))
    (i : I) (x y : X) (hxy : x ≠ y) :
    let S := activeCarrier A C e.toFunctionEmbedding
    let Std := RelStructure.Attachment.copyEmbedding
      C.toRelStructure S R f i
    ∀ edge : OldACarrierEdge A
        (RelStructure.Attachment.attach C.toRelStructure S R f),
      Std x ∈ edge.1 → Std y ∈ edge.1 →
      ∃ old : OldACarrierEdge A C.toRelStructure,
        x ∈ old.1 ∧ y ∈ old.1 := by
  intro edge hx hy
  let S := activeCarrier A C e.toFunctionEmbedding
  let Std := RelStructure.Attachment.copyEmbedding C.toRelStructure S R f i
  have hStrong :
      AStrong A
        (RelStructure.Attachment.attach C.toRelStructure S R f)
        (copyCarrier Std) :=
    activeAttached_standard_aStrong_of_base_aLinear
      A hA D C hPartite hLinear e hRigid R f hCoreStrong i
  obtain ⟨a, ha⟩ := edge.2
  have hxA : Std x ∈ copyCarrier a := by
    rw [← ha]
    exact hx
  have hyA : Std y ∈ copyCarrier a := by
    rw [← ha]
    exact hy
  have hLarge : ¬(copyCarrier a ∩ copyCarrier Std).Subsingleton := by
    intro hh
    have heq : Std x = Std y :=
      hh ⟨hxA, ⟨x, rfl⟩⟩ ⟨hyA, ⟨y, rfl⟩⟩
    exact hxy (Std.injective heq)
  have hSub : edge.1 ⊆ copyCarrier Std := by
    rw [ha]
    exact hStrong a hLarge
  obtain ⟨old, _, hEq⟩ :=
    oldACarrierEdge_pullback_of_subset_image
      A C.toRelStructure
      (RelStructure.Attachment.attach C.toRelStructure S R f)
      Std Set.univ edge (by
        intro z hz
        obtain ⟨u, hu⟩ := hSub hz
        exact ⟨u, Set.mem_univ u, hu⟩)
  refine ⟨old, ?_, ?_⟩
  · have hImg : Std x ∈ (fun z : X => Std z) '' old.1 := by
      rw [hEq]
      exact hx
    obtain ⟨u, hu, hux⟩ := hImg
    exact (Std.injective hux) ▸ hu
  · have hImg : Std y ∈ (fun z : X => Std z) '' old.1 := by
      rw [hEq]
      exact hy
    obtain ⟨u, hu, huy⟩ := hImg
    exact (Std.injective huy) ▸ hu

end StructuralRamsey.Girth
