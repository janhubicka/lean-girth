import Girth.BergeGlue
import Girth.TreeGeometry

/-! # Girth of supported tree amalgams

This module connects the pure Berge-gluing lemmas to the relational
A-supported tree construction.  All incidence arguments live in BergeGlue;
here we only identify the two mapped support hypergraphs and their
free-amalgamation overlap.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {U V W X : Type v}

/-- The two copies of the amalgamation base have the same carrier in a free
amalgam. -/
theorem freeAmalgam_overlap_carrier_eq
    {D : RelStructure L U} {Left : RelStructure L V}
    {Right : RelStructure L W} {Whole : RelStructure L X}
    {fL : Embedding D Left} {fR : Embedding D Right}
    {iL : Embedding Left Whole} {iR : Embedding Right Whole}
    (hfree : IsFreeAmalgam fL fR iL iR) :
    copyCarrier (iL.comp fL) = copyCarrier (iR.comp fR) := by
  apply Set.Subset.antisymm
  · rintro x ⟨d, hd⟩
    refine ⟨d, ?_⟩
    have hov :
        iL (fL d) = iR (fR d) :=
      (hfree.overlap (fL d) (fR d)).mpr ⟨d, rfl, rfl⟩
    exact hov.symm.trans hd
  · rintro x ⟨d, hd⟩
    refine ⟨d, ?_⟩
    have hov :
        iL (fL d) = iR (fR d) :=
      (hfree.overlap (fL d) (fR d)).mpr ⟨d, rfl, rfl⟩
    exact hov.trans hd

/-- Every support copy in a free amalgam of relational structures lies on one
side, provided A is irreducible. -/
theorem supportCopies_eq_union_mapped_of_freeAmalgam
    {A : RelStructure L U} {Left : RelStructure L V}
    {Right : RelStructure L W} {Whole : RelStructure L X}
    {D : Type v} {Base : RelStructure L D}
    {fL : Embedding Base Left} {fR : Embedding Base Right}
    {iL : Embedding Left Whole} {iR : Embedding Right Whole}
    (hA : A.Irreducible)
    (hfree : IsFreeAmalgam fL fR iL iR) :
    supportCopies A Whole =
      mappedSupportCopies A Left Whole iL ∪
        mappedSupportCopies A Right Whole iR := by
  ext E
  constructor
  · rintro ⟨e, rfl⟩
    rcases irreducibleCopy_side_of_freeAmalgam hfree hA e with
      ⟨eL, heL⟩ | ⟨eR, heR⟩
    · exact Or.inl ⟨eL, heL⟩
    · exact Or.inr ⟨eR, heR⟩
  · rintro (⟨eL, rfl⟩ | ⟨eR, rfl⟩)
    · exact ⟨iL.comp eL, rfl⟩
    · exact ⟨iR.comp eR, rfl⟩

/-- Cross-side mapped support edges meet only inside the free-amalgamation
base carrier. -/
theorem mappedSupport_cross_subset_overlap
    {A : RelStructure L U} {Left : RelStructure L V}
    {Right : RelStructure L W} {Whole : RelStructure L X}
    {D : Type v} {Base : RelStructure L D}
    {fL : Embedding Base Left} {fR : Embedding Base Right}
    {iL : Embedding Left Whole} {iR : Embedding Right Whole}
    (hfree : IsFreeAmalgam fL fR iL iR) :
    ∀ ⦃eL eR : Set X⦄,
      eL ∈ mappedSupportCopies A Left Whole iL →
      eR ∈ mappedSupportCopies A Right Whole iR →
      eL ∩ eR ⊆ copyCarrier (iL.comp fL) := by
  intro eL eR hL hR x hx
  rcases hL with ⟨aL, rfl⟩
  rcases hR with ⟨aR, rfl⟩
  have hxSides : x ∈ Set.range iL ∩ Set.range iR := by
    constructor
    · rcases hx.1 with ⟨a, ha⟩
      exact ⟨aL a, ha⟩
    · rcases hx.2 with ⟨a, ha⟩
      exact ⟨aR a, ha⟩
  rw [freeAmalgam_side_intersection hfree] at hxSides
  exact hxSides

/-- The image of a one-point amalgamation base is subsingleton. -/
theorem punit_overlap_subsingleton
    {D : RelStructure L PUnit} {Left : RelStructure L V}
    {Whole : RelStructure L X}
    (f : Embedding D Left) (i : Embedding Left Whole) :
    (copyCarrier (i.comp f)).Subsingleton := by
  intro x hx y hy
  rcases hx with ⟨dx, hdx⟩
  rcases hy with ⟨dy, hdy⟩
  have hdyx : dy = dx := Subsingleton.elim _ _
  calc
    x = i (f dx) := hdx.symm
    _ = i (f dy) := congrArg (fun d => i (f d)) hdyx.symm
    _ = y := hdy

/-- An isomorphic copy has exactly the mapped support hypergraph. -/
theorem supportCopies_eq_mapped_of_iso
    {A : RelStructure L U} {B : RelStructure L V}
    {T : RelStructure L W}
    (h : Iso B T) :
    supportCopies A T =
      mappedSupportCopies A B T h.toEmbedding := by
  ext E
  constructor
  · rintro ⟨e, rfl⟩
    let hInv : Embedding T B := {
      toFun := h.toEquiv.symm
      injective := h.toEquiv.symm.injective
      map_rel_iff := by
        intro R x
        have hx := h.map_rel_iff R (h.toEquiv.symm ∘ x)
        have heq :
            h.toEquiv ∘ (h.toEquiv.symm ∘ x) = x := by
          funext i
          simp
        rw [heq] at hx
        exact hx.symm
    }
    let eB : Embedding A B := hInv.comp e
    refine ⟨eB, ?_⟩
    change copyCarrier e =
      copyCarrier (h.toEmbedding.comp eB)
    apply Set.Subset.antisymm
    · rintro x ⟨a, rfl⟩
      refine ⟨a, ?_⟩
      change h.toEquiv (h.toEquiv.symm (e a)) = e a
      exact h.toEquiv.apply_symm_apply (e a)
    · rintro x ⟨a, rfl⟩
      refine ⟨a, ?_⟩
      change e a = h.toEquiv (h.toEquiv.symm (e a))
      exact (h.toEquiv.apply_symm_apply (e a)).symm
  · rintro ⟨e, rfl⟩
    exact ⟨h.toEmbedding.comp e, rfl⟩

namespace ASupportedTreeAmalgam

/-- The support hypergraph of an A-supported tree amalgam has the same girth
lower bound as the constituent B. -/
theorem girthGT
    {A : RelStructure L U} {B : RelStructure L V}
    {T : RelStructure L W} {g : ℕ}
    (hA : A.Irreducible)
    (hBase : GirthGT (supportCopies A B) g)
    (hT : ASupportedTreeAmalgam A B W T) :
    GirthGT (supportCopies A T) g := by
  induction hT with
  | copy h =>
      rw [supportCopies_eq_mapped_of_iso h]
      exact girthGT_mappedSupportCopies A B _ h.toEmbedding hBase
  | glueA h₀ f₀ fB i₀ iB hfree ih =>
      let HL := mappedSupportCopies A _ _ i₀
      let HR := mappedSupportCopies A B _ iB
      have hHL : GirthGT HL g :=
        girthGT_mappedSupportCopies A _ _ i₀ ih
      have hHR : GirthGT HR g :=
        girthGT_mappedSupportCopies A B _ iB hBase
      have hSupp :
          supportCopies A _ = HL ∪ HR :=
        supportCopies_eq_union_mapped_of_freeAmalgam hA hfree
      rw [hSupp]
      let separator : Set _ := copyCarrier (i₀.comp f₀)
      have hsepL : separator ∈ HL := by
        exact ⟨f₀, rfl⟩
      have hoverlap :
          separator = copyCarrier (iB.comp fB) := by
        exact freeAmalgam_overlap_carrier_eq hfree
      have hsepR : separator ∈ HR := by
        exact ⟨fB, hoverlap⟩
      have hcross :
          ∀ ⦃eL eR : Set _⦄, eL ∈ HL → eR ∈ HR →
            eL ∩ eR ⊆ separator := by
        exact mappedSupport_cross_subset_overlap hfree
      exact girthGT_union_of_edge_glue
        hsepL hsepR hcross hHL hHR
  | gluePoint h₀ f₀ fB support₀ supportB i₀ iB hfree ih =>
      let HL := mappedSupportCopies A _ _ i₀
      let HR := mappedSupportCopies A B _ iB
      have hHL : GirthGT HL g :=
        girthGT_mappedSupportCopies A _ _ i₀ ih
      have hHR : GirthGT HR g :=
        girthGT_mappedSupportCopies A B _ iB hBase
      have hSupp :
          supportCopies A _ = HL ∪ HR :=
        supportCopies_eq_union_mapped_of_freeAmalgam hA hfree
      rw [hSupp]
      let separator : Set _ := copyCarrier (i₀.comp f₀)
      have hsepSmall : separator.Subsingleton :=
        punit_overlap_subsingleton f₀ i₀
      have hcross :
          ∀ ⦃eL eR : Set _⦄, eL ∈ HL → eR ∈ HR →
            eL ∩ eR ⊆ separator := by
        exact mappedSupport_cross_subset_overlap hfree
      exact girthGT_union_of_subsingleton_glue
        hsepSmall hcross hHL hHR

end ASupportedTreeAmalgam

end StructuralRamsey.Girth
