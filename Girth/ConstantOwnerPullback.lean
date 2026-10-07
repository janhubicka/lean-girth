import Girth.Berge

/-! # Pulling support cycles through one ambient copy

The constant-owner case in the circulation girth argument is purely generic:
if every A-support edge of a Berge cycle lies inside the range of one ambient
embedding, each edge factors through that embedding and the whole cycle is a
cycle among mapped support copies.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {UA X Y : Type v}

/-- A support copy contained in the range of an ambient embedding is a mapped
support copy. -/
theorem supportCopy_mem_mappedSupportCopies_of_subset
    (A : RelStructure L UA)
    (Old : RelStructure L X)
    (Whole : RelStructure L Y)
    (i : RelStructure.Embedding Old Whole)
    (a : RelStructure.Embedding A Whole)
    (hSub : copyCarrier a ⊆ copyCarrier i) :
    copyCarrier a ∈ mappedSupportCopies A Old Whole i := by
  classical
  have hFactor : ∀ u : UA, ∃ x : X, a u = i x := by
    intro u
    rcases hSub ⟨u, rfl⟩ with ⟨x, hx⟩
    exact ⟨x, hx.symm⟩
  let aOld : RelStructure.Embedding A Old :=
    a.factorThroughRange i hFactor
  have haEq : a = i.comp aOld := by
    apply RelStructure.Embedding.ext
    intro u
    exact Classical.choose_spec (hFactor u)
  refine ⟨aOld, ?_⟩
  rw [haEq]

/-- Reinterpret a support Berge cycle all of whose edges lie in one ambient
copy as a cycle among mapped support copies of that copy. -/
noncomputable def bergeCycle_mappedSupportCopies_of_edge_subset
    (A : RelStructure L UA)
    (Old : RelStructure L X)
    (Whole : RelStructure L Y)
    (i : RelStructure.Embedding Old Whole)
    (c : BergeCycle (supportCopies A Whole))
    (hSub : ∀ j, c.edge j ⊆ copyCarrier i) :
    BergeCycle (mappedSupportCopies A Old Whole i) :=
  c.ofEdgeMem fun j => by
    rcases c.edge_mem j with ⟨a, ha⟩
    rw [ha]
    exact
      supportCopy_mem_mappedSupportCopies_of_subset
        A Old Whole i a
        (by simpa [ha] using hSub j)

/-- Constant-owner contradiction: a short support cycle contained in one
embedded old picture contradicts the old support girth. -/
theorem no_short_support_cycle_in_embedding
    (A : RelStructure L UA)
    (Old : RelStructure L X)
    (Whole : RelStructure L Y)
    (i : RelStructure.Embedding Old Whole)
    (g : ℕ)
    (hOld : GirthGT (supportCopies A Old) g)
    (c : BergeCycle (supportCopies A Whole))
    (hLen : c.length ≤ g)
    (hSub : ∀ j, c.edge j ⊆ copyCarrier i) :
    False := by
  have hMapped :
      GirthGT (mappedSupportCopies A Old Whole i) g :=
    girthGT_mappedSupportCopies A Old Whole i hOld
  exact hMapped
    ⟨bergeCycle_mappedSupportCopies_of_edge_subset
      A Old Whole i c hSub, hLen⟩

end StructuralRamsey.Girth
