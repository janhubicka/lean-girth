import Girth.TrainRecursiveTrueActiveCoverage
import Girth.Support
import Mathlib.Tactic

set_option autoImplicit false
set_option Elab.async false

/-!
# A-strong copies reflect irreducible A-coverage on 2+ vertices

The q=2 source-level gap is structural, not just a missing proof of
A-generation -> irreducible A-extension. An ambient E which contains
an A-strong induced copy of a graph R CANNOT extend any irreducible
substructure of R with at least two vertices to an A-copy unless
that substructure already extends to A INSIDE R.

Indeed any ambient A-copy containing two vertices of the selected
copy has a non-subsingleton intersection with it. A-strongness
forces the whole A-copy into the selected image. Inducedness then
pulls the entire A-embedding back to R.

The empty and single-vertex cases are intentionally excluded:
strongness only controls intersections of size at least two.
The theorem holds in arbitrary relational languages and does not
use graph-specific features, finiteness or an invented witness.

This yields a precise no-go criterion for the q=2 use of
ActiveAttachmentBounds.coreCoverage when F_2 selected embeddings
remain A-strong.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v

/-- Every irreducible induced source substructure with TWO DISTINCT
vertices has an A-copy covering it if its target has complete
A-irreducible coverage and the source embedding is A-strong.
This reflects a two-vertex-or-larger extension, not full coverage
of empty/singleton substructures. -/
theorem irreducible_two_point_extension_reflect_of_aStrong
    {L : RelLanguage.{u}} {UA VB W : Type v}
    (A : RelStructure L UA) (B : RelStructure L VB)
    (C : RelStructure L W)
    (b : RelStructure.Embedding B C)
    (hStrong : AStrong A C (copyCarrier b))
    (hCCover : IrreduciblesExtendTo A C)
    (S : Set VB) (hIrr : (B.induce S).Irreducible)
    (x y : VB) (hx : x ∈ S) (hy : y ∈ S) (hxy : x ≠ y) :
    ∃ a : RelStructure.Embedding A B,
      ∀ z : S, ∃ u : UA, z.1 = a u := by
  classical
  let inc : RelStructure.Embedding (B.induce S) B :=
    RelStructure.inclusion B S
  let mapped : RelStructure.Embedding (B.induce S) C :=
    b.comp inc
  have hIrrC :
      (C.induce (Set.range mapped)).Irreducible :=
    hIrr.range_embedding mapped
  obtain ⟨aC, hACover⟩ :=
    hCCover (Set.range mapped) hIrrC
  have hxRange : b x ∈ Set.range mapped := by
    exact ⟨⟨x, hx⟩, rfl⟩
  have hyRange : b y ∈ Set.range mapped := by
    exact ⟨⟨y, hy⟩, rfl⟩
  obtain ⟨ux, hux⟩ := hACover ⟨b x, hxRange⟩
  obtain ⟨uy, huy⟩ := hACover ⟨b y, hyRange⟩
  have hxIn : b x ∈ copyCarrier aC := by
    exact ⟨ux, hux.symm⟩
  have hyIn : b y ∈ copyCarrier aC := by
    exact ⟨uy, huy.symm⟩
  have hLarge :
      ¬ (copyCarrier aC ∩ copyCarrier b).Subsingleton := by
    intro hSmall
    apply hxy
    apply b.injective
    exact hSmall ⟨hxIn, ⟨x, rfl⟩⟩ ⟨hyIn, ⟨y, rfl⟩⟩
  have hInside : copyCarrier aC ⊆ copyCarrier b :=
    hStrong aC hLarge
  have hFactor : ∀ u : UA, ∃ v : VB, aC u = b v := by
    intro u
    obtain ⟨v, hv⟩ := hInside ⟨u, rfl⟩
    exact ⟨v, hv.symm⟩
  let aB : RelStructure.Embedding A B :=
    aC.factorThroughRange b hFactor
  have hEq : aC = b.comp aB := by
    apply RelStructure.Embedding.ext
    intro u
    exact Classical.choose_spec (hFactor u)
  refine ⟨aB, ?_⟩
  intro z
  have hzRange : b z.1 ∈ Set.range mapped := by
    exact ⟨z, rfl⟩
  obtain ⟨u, hu⟩ := hACover ⟨b z.1, hzRange⟩
  refine ⟨u, ?_⟩
  apply b.injective
  rw [← hEq]
  exact hu

/-- If a 2+ vertex irreducible in B has NO A-extension, no A-strong
induced embedding B -> C can land in a C with total irreducible
A-coverage. In particular a q=2 local core cannot simply be
completed outside an A-strong selected B-copy to discharge the
generic ActiveAttachmentBounds.coreCoverage field. -/
theorem no_aStrong_covered_extension_of_irreducible_obstruction
    {L : RelLanguage.{u}} {UA VB W : Type v}
    (A : RelStructure L UA) (B : RelStructure L VB)
    (C : RelStructure L W)
    (b : RelStructure.Embedding B C)
    (hStrong : AStrong A C (copyCarrier b))
    (S : Set VB) (hIrr : (B.induce S).Irreducible)
    (x y : VB) (hx : x ∈ S) (hy : y ∈ S) (hxy : x ≠ y)
    (hNoExtension :
      ¬ ∃ a : RelStructure.Embedding A B,
        ∀ z : S, ∃ u : UA, z.1 = a u) :
    ¬ IrreduciblesExtendTo A C := by
  intro hC
  exact hNoExtension
    (irreducible_two_point_extension_reflect_of_aStrong
      A B C b hStrong hC S hIrr x y hx hy hxy)

end StructuralRamsey.Girth
