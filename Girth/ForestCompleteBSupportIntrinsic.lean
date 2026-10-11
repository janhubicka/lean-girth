import Girth.SupportForestToTree
import Girth.ForestRelationalBoundarySupport

/-!
# Complete ambient B-support equals intrinsic transported A-support

Two support-piece representations occur in the circulation
formalization:

* bSupportPiece A b stores ALL ambient embedded A-copies whose
  carriers are contained in the given embedded B-copy.
* embeddedACopySupportPiece A b stores images of genuine embeddings
  A -> B, transported along b.

For a relational EMBEDDING b these are exactly equivalent: any
ambient A-embedding lying inside b's image factors through b, by
reflection of relations. This needs neither girth nor strong
inducedness. In particular the checked local-core boundary lemma for
intrinsic selected B-pieces also applies to the genuine COMPLETE
A-support used by the final circulation forest invariant.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {UA VB W : Type v}

/-- The complete ambient A-support piece of an embedded B-copy is
exactly its intrinsic A-support transported along the embedding. -/
theorem bSupportPiece_eq_embeddedACopySupportPiece
    (A : RelStructure L UA)
    {B : RelStructure L VB} {D : RelStructure L W}
    (b : RelStructure.Embedding B D) :
    bSupportPiece A b = embeddedACopySupportPiece A b := by
  classical
  have hEdges :
      (bSupportPiece A b).edges =
        (embeddedACopySupportPiece A b).edges := by
    ext e
    constructor
    · rintro ⟨a, hCarrier, hSub⟩
      have hFactor (u : UA) :
          ∃ x : VB, a u = b x := by
        obtain ⟨x, hx⟩ := hSub ⟨u, rfl⟩
        exact ⟨x, hx.symm⟩
      let aB : RelStructure.Embedding A B :=
        a.factorThroughRange b hFactor
      have hCompCarrier :
          copyCarrier a = copyCarrier (b.comp aB) := by
        ext y
        constructor
        · rintro ⟨u, rfl⟩
          refine ⟨u, ?_⟩
          exact (Classical.choose_spec (hFactor u)).symm
        · rintro ⟨u, rfl⟩
          refine ⟨u, ?_⟩
          exact Classical.choose_spec (hFactor u)
      exact ⟨aB, hCarrier.symm.trans hCompCarrier⟩
    · rintro ⟨aB, rfl⟩
      refine ⟨b.comp aB, rfl, ?_⟩
      rintro y ⟨u, rfl⟩
      exact ⟨aB u, rfl⟩
  have hCarrier :
      (bSupportPiece A b).carrier =
        (embeddedACopySupportPiece A b).carrier := rfl
  cases hF : bSupportPiece A b with
  | mk c edges hSub =>
      cases hG : embeddedACopySupportPiece A b with
      | mk d edges' hSub' =>
          simp only [hF, hG] at hCarrier hEdges
          cases hCarrier
          cases hEdges
          rfl

end StructuralRamsey.Girth
