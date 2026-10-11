import Girth.SupportForestToTree
import Girth.ForestRelationalBoundarySupport
import Girth.ForestActualPartiteBoundary

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

/-- Boundary data established on the intrinsic support of a B-embedding
also governs its COMPLETE ambient A-support piece. -/
theorem completeBSupport_smallOrWholeBoundary_of_intrinsic
    (A : RelStructure L UA)
    {B : RelStructure L VB} {D : RelStructure L W}
    (b : RelStructure.Embedding B D)
    (K : Set (Set W)) (S : Set W)
    (hBoundary :
      SmallOrWholeEdgeBoundary K S (embeddedACopySupportPiece A b)) :
    SmallOrWholeEdgeBoundary K S (bSupportPiece A b) := by
  rw [bSupportPiece_eq_embeddedACopySupportPiece A b]
  exact hBoundary

/-- The checked ACTUAL partite B-copy boundary statement, upgraded to
the full ambient A-support notion consumed by the circulation theorem.
The intrinsic and ambient support notions coincide by factorization
through the relational standard-copy embedding. -/
theorem attachedProjectedBCopy_completeSupportBoundary
    {P X Y I : Type v}
    (A : RelStructure L UA)
    (B : RelStructure L VB)
    (D : RelStructure L P)
    (C : StructuralRamsey.Partite.System L P X)
    (e : RelStructure.Embedding A D)
    (b : RelStructure.Embedding B D)
    (q : StructuralRamsey.Partite.ProjectedEmbedding B C b)
    (hStrong : AStrong A D (copyCarrier b))
    (E : StructuralRamsey.Partite.System L P Y)
    (f : I → StructuralRamsey.Partite.Embedding
      (C.induce (activeCarrier A C e.toFunctionEmbedding)) E)
    (i : I) :
    let S := activeCarrier A C e.toFunctionEmbedding
    let copyI :=
      (StructuralRamsey.Partite.Attachment.copyEmbedding C S E f i).toEmbedding
    let core :=
      (StructuralRamsey.Partite.Attachment.coreEmbedding C S E f).toEmbedding
    SmallOrWholeEdgeBoundary
      {t : Set (StructuralRamsey.Partite.Attachment.Vertex S
          (W := Y) (I := I)) |
        ∃ aE : RelStructure.Embedding A E.toRelStructure,
          t = copyCarrier (core.comp aE)}
      (copyCarrier core)
      (bSupportPiece A (copyI.comp q.val)) := by
  let S := activeCarrier A C e.toFunctionEmbedding
  let copyI :=
    (StructuralRamsey.Partite.Attachment.copyEmbedding C S E f i).toEmbedding
  let core :=
    (StructuralRamsey.Partite.Attachment.coreEmbedding C S E f).toEmbedding
  exact completeBSupport_smallOrWholeBoundary_of_intrinsic
    A (copyI.comp q.val) _ _
    (attachedProjectedBCopy_smallOrWholeBoundary
      A B D C e b q hStrong E f i)

end StructuralRamsey.Girth
