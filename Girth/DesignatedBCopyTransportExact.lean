import Girth.DesignatedAttachment
import Girth.SupportForestToTree

/-!
# Every actual B-copy is a transported designated old B-copy

An irreducible B-copy of the attached picture is itself an irreducible
substructure. The indexed designated-coverage theorem remembers the exact
old designated B-copy and standard-picture index covering it.

Since B is finite, containment of one B-image in another forces equality
of carriers. The COMPLETE A-support carried by a B-copy depends only on
that carrier, so its HypergraphPiece is exactly the support of the
transported designated copy, including every ambient A-edge inside it.

This completes the geometric classification of actual ambient B-copies,
conditional only on the previously formulated old designated coverage and
honest local A-copy coverage assumptions. It does not establish existence
of the local Ramsey witness or the global picture induction.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {UA VB P X Y I W : Type v}

/-- Two embedded B-copies with the same image carrier carry exactly the
same A-support HypergraphPiece, including all internal ambient A-edges. -/
theorem bSupportPiece_eq_of_sameCopy
    (A : RelStructure L UA)
    {B : RelStructure L VB} {R : RelStructure L W}
    (b c : Embedding B R)
    (hSame : SameCopy b c) :
    bSupportPiece A b = bSupportPiece A c := by
  have hCarrier :
      (bSupportPiece A b).carrier =
        (bSupportPiece A c).carrier := hSame
  have hEdges :
      (bSupportPiece A b).edges =
        (bSupportPiece A c).edges := by
    change
      {e : Set W | ∃ a : Embedding A R,
        copyCarrier a = e ∧ copyCarrier a ⊆ copyCarrier b} =
      {e : Set W | ∃ a : Embedding A R,
        copyCarrier a = e ∧ copyCarrier a ⊆ copyCarrier c}
    rw [hSame]
  cases hb : bSupportPiece A b with
  | mk cb eb hbproof =>
    cases hc : bSupportPiece A c with
    | mk cc ec hcproof =>
      simp only [hb, hc] at hCarrier hEdges
      cases hCarrier
      cases hEdges
      rfl

/-- Every actual B-embedding into the new partite picture coincides as
a *copy* with the transport, through some genuine standard picture,
of an old designated B-embedding. The complete A-support is equal too. -/
theorem actualBCopy_is_transported_designated
    (A : RelStructure L UA)
    (hA : A.Irreducible)
    (B : RelStructure L VB)
    (hB : B.Irreducible)
    [Finite VB]
    (D : RelStructure L P)
    (C : StructuralRamsey.Partite.System L P X)
    (family : Set (RelStructure.Embedding B D))
    (S : Set X)
    (E : StructuralRamsey.Partite.System L P Y)
    (f : I → StructuralRamsey.Partite.Embedding (C.induce S) E)
    (hOld : DesignatedCoversIrreducibles B D C family)
    (hLocal : LocalIrreduciblesCoveredByAInCopies A E f)
    (bNew : Embedding B
      (StructuralRamsey.Partite.Attachment.attach C S E f).toRelStructure) :
    ∃ (i : I) (q : DesignatedCopy B D C family),
      SameCopy bNew ((q.transportToStandard f i).embedding) ∧
      bSupportPiece A bNew =
        bSupportPiece A ((q.transportToStandard f i).embedding) := by
  classical
  let Whole :=
    (StructuralRamsey.Partite.Attachment.attach C S E f).toRelStructure
  let T : Set _ := copyCarrier bNew
  have hIrr : (Whole.induce T).Irreducible :=
    hB.range_embedding bNew
  obtain ⟨i, q, hCover⟩ :=
    transportedDesignatedCoversIrreducibles_partiteAttachment
      A B D C family S E f hA hOld hLocal T hIrr
  have hInto :
      ∀ v : VB, ∃ w : VB,
        bNew v = (q.transportToStandard f i).embedding w := by
    intro v
    exact hCover ⟨bNew v, ⟨v, rfl⟩⟩
  have hSame :
      SameCopy bNew ((q.transportToStandard f i).embedding) :=
    sameCopy_of_range_subset bNew
      ((q.transportToStandard f i).embedding) hInto
  exact ⟨i, q, hSame, bSupportPiece_eq_of_sameCopy A bNew
    ((q.transportToStandard f i).embedding) hSame⟩

end StructuralRamsey.Girth
