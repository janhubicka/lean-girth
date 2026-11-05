import Girth.TrainRecursiveWitnessPass

set_option autoImplicit false
set_option Elab.async false

/-!
# Actual selected relational copies reflect physical train relations

The shorter-train induction does NOT merely output an arbitrary relational
copy of M. Its ForestTailStage includes genuine selected designated copies,
and targetRestriction proves their full proper-cut (and bottom/top) train
relation equivalences on actual A-support embeddings.

Here we transport those equivalences from a choice of A-embeddings to
the PHYSICAL edge type OldACarrierEdge, whose elements are literal
carriers, not occurrence-labelled A-embeddings. Equal carriers have
equal transported carriers because the selected vertex map is injective.

This constructs the physical old-edge embedding from the actual selected
relational copy and proves that it preserves AND REFLECTS each actual
train relation, precisely the hypothesis needed by the selected-filled
wagon map in the cutoff-two application.

The true contracted source M and its identification with heterogeneous
G0, including its top relation and the final selected target H embedding,
remain application work. No appendix or output girth hypothesis.
-/

namespace StructuralRamsey.Girth.TrainRecursiveWitness

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}} {UA VB P : Type v}
variable {A : RelStructure L UA} {B : RelStructure L VB}
variable {D : RelStructure L P} {family : Set (Embedding B D)}
variable {t : List ℕ}
variable {targetTrain : EdgeTrainLevels (OldACarrierEdge A B) t.length}
variable {allowed : Fin (t.length + 1) → Set P}

/-- Every selected copy produces an injective map of the WHOLE physical
A-edge carrier families. Its edge map is constructed from the vertex
embedding, not provided as a separate witness field. -/
def selectedPhysicalEdgeEmbedding
    (S : ForestTailStage A B D family t targetTrain allowed)
    (b : DesignatedCopy B D S.system family) :
    OldACarrierEdge A B ↪ OldACarrierEdge A S.system.toRelStructure where
  toFun e := ⟨b.embedding.toFunctionEmbedding '' e.1, by
    obtain ⟨a, ha⟩ := e.2
    refine ⟨b.embedding.comp a, ?_⟩
    rw [ha]
    exact (copyCarrier_comp_eq_image b.embedding a).symm⟩
  inj' := by
    intro e f hef
    apply Subtype.ext
    have hImage : b.embedding.toFunctionEmbedding '' e.1 =
        b.embedding.toFunctionEmbedding '' f.1 :=
      congrArg (fun edge : OldACarrierEdge A S.system.toRelStructure =>
        edge.1) hef
    ext x
    constructor
    · intro hx
      have hIn : b.embedding x ∈ b.embedding.toFunctionEmbedding '' f.1 := by
        rw [← hImage]
        exact ⟨x, hx, rfl⟩
      obtain ⟨y, hy, hxy⟩ := hIn
      have hyx : y = x := b.embedding.injective hxy
      simpa only [hyx] using hy
    · intro hx
      have hIn : b.embedding x ∈ b.embedding.toFunctionEmbedding '' e.1 := by
        rw [hImage]
        exact ⟨x, hx, rfl⟩
      obtain ⟨y, hy, hxy⟩ := hIn
      have hyx : y = x := b.embedding.injective hxy
      simpa only [hyx] using hy

/-- On each genuine source A-embedding, the physical carrier map is
literally the physical edge of its composite with the selected B-copy. -/
@[simp] theorem selectedPhysicalEdgeEmbedding_actualEdge
    (S : ForestTailStage A B D family t targetTrain allowed)
    (b : DesignatedCopy B D S.system family)
    (a : Embedding A B) :
    S.selectedPhysicalEdgeEmbedding b (actualEdge a) =
      actualEdge (b.embedding.comp a) := by
  apply Subtype.ext
  exact (copyCarrier_comp_eq_image b.embedding a).symm

/-- The checked targetRestriction of the shorter recursive witness
extends from representative A-embeddings to ANY pair of genuine
physical source A-edge carriers. No new train-reflection assumption. -/
theorem selectedPhysicalEdgeEmbedding_train_iff
    (S : ForestTailStage A B D family t targetTrain allowed)
    (b : DesignatedCopy B D S.system family)
    (hb : b ∈ S.selected)
    (μ : Fin (t.length + 1))
    (e f : OldACarrierEdge A B) :
    S.train.rel μ (S.selectedPhysicalEdgeEmbedding b e)
        (S.selectedPhysicalEdgeEmbedding b f) ↔
      targetTrain.rel μ e f := by
  obtain ⟨a, ha⟩ := e.2
  obtain ⟨a', ha'⟩ := f.2
  have he : e = actualEdge a := Subtype.ext ha
  have hf : f = actualEdge a' := Subtype.ext ha'
  subst e
  subst f
  rw [S.selectedPhysicalEdgeEmbedding_actualEdge b a,
      S.selectedPhysicalEdgeEmbedding_actualEdge b a']
  exact S.targetRestriction b hb μ a a'

/-- Direct interface for the faithful restored-wagon constructor:
the relation equivalence is supplied in the orientation expected by
the physical selected-filling lemma. The ambient N train and selected
old-edge map come from the same genuine selected witness. -/
theorem selectedPhysicalEdgeEmbedding_train_faithful
    (S : ForestTailStage A B D family t targetTrain allowed)
    (b : DesignatedCopy B D S.system family)
    (hb : b ∈ S.selected)
    (μ : Fin (t.length + 1))
    (e f : OldACarrierEdge A B) :
    targetTrain.rel μ e f ↔
      S.train.rel μ (S.selectedPhysicalEdgeEmbedding b e)
        (S.selectedPhysicalEdgeEmbedding b f) :=
  (S.selectedPhysicalEdgeEmbedding_train_iff b hb μ e f).symm

end StructuralRamsey.Girth.TrainRecursiveWitness
