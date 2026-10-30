import Girth.TrainForeignDesignatedSupport
import Girth.ForestSelectedMixedCoverage
import Girth.ForestToSupremeActualGeometry
import Girth.ForestActualRecursiveSupport

set_option Elab.async false

/-!
# Indexed attachment labels are the actual transported selected copies

The cycle model of an attachment labels a designated occurrence by a pair
consisting of its standard index and its selected old copy.  A recursive
stage instead stores the set of actual transported designated copies.
These two types must be related by a genuine bijection, rather than by
identifying equal vertex carriers.

Every selected old copy with two distinct support edges has a vertex
outside the active subsystem, provided its base copy is A-strong.  A
private vertex determines the attached standard.  Injectivity of that
standard's embedding then determines the original designated copy.
Surjectivity is the definition of the transported selection.

This also preserves physical support-piece injectivity from the old
selection.  No rigidity of B, ambient finiteness, output cycle bound, or
injectivity of the family of gluing images is required.  The one-edge
target is deliberately outside this interface: there a selected copy can
lie wholly in the active subsystem, so the standard index can disappear.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v

section TransportedLabels

variable {L : RelLanguage.{u}} {VB P X Y I : Type v}
variable (B : RelStructure L VB) (D : RelStructure L P)
variable (C : StructuralRamsey.Partite.System L P X)
variable (family : Set (RelStructure.Embedding B D))
variable (selected : Set (DesignatedCopy B D C family))
variable (S : Set X) (E : StructuralRamsey.Partite.System L P Y)
variable (f : I → StructuralRamsey.Partite.Embedding (C.induce S) E)

/-- The literal actual selected copy belonging to an indexed old label. -/
noncomputable def transportedSelectedCopyLabel
    (iq : I × {q : DesignatedCopy B D C family // q ∈ selected}) :
    {r : DesignatedCopy B D
      (StructuralRamsey.Partite.Attachment.attach C S E f) family //
      r ∈ transportedSelectedCopies B D C family selected S E f} :=
  ⟨iq.2.1.transportToStandard f iq.1, iq.1, iq.2.1, iq.2.2, rfl⟩

/-- Every actual selected output copy has an indexed selected old source. -/
theorem transportedSelectedCopyLabel_surjective :
    Function.Surjective
      (transportedSelectedCopyLabel B D C family selected S E f) := by
  rintro ⟨r, i, q, hq, rfl⟩
  exact ⟨(i, ⟨q, hq⟩), rfl⟩

/-- The label bijection uses the whole transported copy carrier, with its
original embedding; it does not quotient by equal carriers. -/
theorem transportedSelectedCopyLabel_carrier
    (iq : I × {q : DesignatedCopy B D C family // q ∈ selected}) :
    copyCarrier
      (transportedSelectedCopyLabel B D C family selected S E f iq).1.embedding =
      (fun x : X =>
        (StructuralRamsey.Partite.Attachment.copyEmbedding C S E f iq.1) x) ''
        copyCarrier iq.2.1.embedding := by
  exact copyCarrier_comp_eq_image
    (StructuralRamsey.Partite.Attachment.copyEmbedding C S E f iq.1).toEmbedding
    iq.2.1.embedding

end TransportedLabels

section ActiveLabels

variable {L : RelLanguage.{u}} {UA VB P X Y I : Type v}
variable (A : RelStructure L UA) (B : RelStructure L VB)
variable (D : RelStructure L P)
variable (C : StructuralRamsey.Partite.System L P X)
variable (family : Set (RelStructure.Embedding B D))
variable (selected : Set (DesignatedCopy B D C family))
variable (e : RelStructure.Embedding A D)
variable (E : StructuralRamsey.Partite.System L P Y)
variable (f : I → StructuralRamsey.Partite.Embedding
  (C.induce (activeCarrier A C e.toFunctionEmbedding)) E)

local notation "S" => activeCarrier A C e.toFunctionEmbedding
local notation "Selected" => {q : DesignatedCopy B D C family // q ∈ selected}
local notation "OldEdge" => OldACarrierEdge A C.toRelStructure
local notation "Std" => StructuralRamsey.Partite.Attachment.copyEmbedding C S E f
local notation "Label" => transportedSelectedCopyLabel B D C family selected S E f

/-- The target's two distinct physical A-copies supply two distinct old
support edges in every selected copy.  No per-copy choice is assumed. -/
theorem selectedCopy_two_edges_of_target
    (q : Selected) (a b : Embedding A B) (hne : ¬ SameCopy a b) :
    ∃ r s : OldEdge, r ≠ s ∧
      r.1 ⊆ copyCarrier q.1.embedding ∧ s.1 ⊆ copyCarrier q.1.embedding := by
  let r : OldEdge := ⟨copyCarrier (q.1.embedding.comp a), ⟨q.1.embedding.comp a, rfl⟩⟩
  let s : OldEdge := ⟨copyCarrier (q.1.embedding.comp b), ⟨q.1.embedding.comp b, rfl⟩⟩
  refine ⟨r, s, ?_, ?_, ?_⟩
  · intro h
    exact hne (sameCopy_of_comp q.1.embedding (congrArg Subtype.val h))
  · rintro x ⟨u, rfl⟩
    exact ⟨a u, rfl⟩
  · rintro x ⟨u, rfl⟩
    exact ⟨b u, rfl⟩

/-- A genuine two-edge selected copy cannot disappear entirely into the
active subsystem.  Its private vertex will remember the standard index. -/
theorem selectedCopy_private_vertex_of_two_edges [Finite UA]
    (q : Selected)
    (hStrong : AStrong A D (copyCarrier q.1.base))
    (hTwo : ∃ r s : OldEdge, r ≠ s ∧
      r.1 ⊆ copyCarrier q.1.embedding ∧ s.1 ⊆ copyCarrier q.1.embedding) :
    ∃ x : X, x ∈ copyCarrier q.1.embedding ∧ x ∉ S := by
  classical
  by_contra hNo
  have hSub : copyCarrier q.1.embedding ⊆ S := by
    intro x hx
    by_contra hxS
    exact hNo ⟨x, hx, hxS⟩
  obtain ⟨r, s, hrs, hr, hs⟩ := hTwo
  exact hrs (designated_active_source_edges_eq
    A B D C family e q.1 hStrong hSub r s hr hs)

/-- Distinct indexed labels give distinct actual transported designated
copies.  Private vertices recover the index; the injective standard map
recovers the old embedding and hence its prescribed base label. -/
theorem transportedSelectedCopyLabel_injective [Finite UA]
    (hStrong : ∀ q : Selected, AStrong A D (copyCarrier q.1.base))
    (hTwo : ∀ q : Selected, ∃ r s : OldEdge, r ≠ s ∧
      r.1 ⊆ copyCarrier q.1.embedding ∧ s.1 ⊆ copyCarrier q.1.embedding) :
    Function.Injective Label := by
  rintro ⟨i, q⟩ ⟨j, r⟩ hEq
  have hCarrier :
      (fun x : X => Std i x) '' copyCarrier q.1.embedding =
        (fun x : X => Std j x) '' copyCarrier r.1.embedding := by
    rw [← transportedSelectedCopyLabel_carrier B D C family selected S E f (i, q),
      ← transportedSelectedCopyLabel_carrier B D C family selected S E f (j, r)]
    exact congrArg (fun z => copyCarrier z.1.embedding) hEq
  have hij : i = j := attachment_privateStandardCarrier_unique_index
    C.toRelStructure S E.toRelStructure (fun i => (f i).toEmbedding)
    i j (copyCarrier q.1.embedding) (copyCarrier r.1.embedding)
    (selectedCopy_private_vertex_of_two_edges
      A B D C family selected e q (hStrong q) (hTwo q)) hCarrier
  subst j
  have hOld : q = r := by
    apply Subtype.ext
    apply actualDesignatedCopy_embedding_injective B D C family
    apply Embedding.ext
    intro b
    apply (Std i).toEmbedding.injective
    exact congrArg (fun z => z.1.embedding b) hEq
  cases hOld
  rfl

/-- The exact designated-label equivalence needed to pass from the indexed
cycle model to the actual selected family in a recursive stage. -/
noncomputable def transportedSelectedCopyEquiv [Finite UA]
    (hStrong : ∀ q : Selected, AStrong A D (copyCarrier q.1.base))
    (hTwo : ∀ q : Selected, ∃ r s : OldEdge, r ≠ s ∧
      r.1 ⊆ copyCarrier q.1.embedding ∧ s.1 ⊆ copyCarrier q.1.embedding) :
    (I × Selected) ≃
      {r : DesignatedCopy B D
        (StructuralRamsey.Partite.Attachment.attach C S E f) family //
        r ∈ transportedSelectedCopies B D C family selected S E f} :=
  Equiv.ofBijective Label
    ⟨transportedSelectedCopyLabel_injective A B D C family selected e E f hStrong hTwo,
      transportedSelectedCopyLabel_surjective B D C family selected S E f⟩

/-- Literal transported selection preserves physical support injectivity.
The original stage's condition suffices; rigidity of the target structure
and an independent output-injectivity assumption are unnecessary. -/
theorem transportedSelectedCopies_physical_injective [Finite UA]
    (hStrong : ∀ q : Selected, AStrong A D (copyCarrier q.1.base))
    (hTwo : ∀ q : Selected, ∃ r s : OldEdge, r ≠ s ∧
      r.1 ⊆ copyCarrier q.1.embedding ∧ s.1 ⊆ copyCarrier q.1.embedding)
    (hOld : Function.Injective (fun q : Selected => bSupportPiece A q.1.embedding)) :
    Function.Injective
      (fun r : {r : DesignatedCopy B D
        (StructuralRamsey.Partite.Attachment.attach C S E f) family //
        r ∈ transportedSelectedCopies B D C family selected S E f} =>
          bSupportPiece A r.1.embedding) := by
  intro u v hPieces
  obtain ⟨⟨i, q⟩, rfl⟩ :=
    transportedSelectedCopyLabel_surjective B D C family selected S E f u
  obtain ⟨⟨j, r⟩, rfl⟩ :=
    transportedSelectedCopyLabel_surjective B D C family selected S E f v
  have hCarrier :
      (fun x : X => Std i x) '' copyCarrier q.1.embedding =
        (fun x : X => Std j x) '' copyCarrier r.1.embedding := by
    rw [← transportedSelectedCopyLabel_carrier B D C family selected S E f (i, q),
      ← transportedSelectedCopyLabel_carrier B D C family selected S E f (j, r)]
    exact congrArg HypergraphPiece.carrier hPieces
  have hij : i = j := attachment_privateStandardCarrier_unique_index
    C.toRelStructure S E.toRelStructure (fun i => (f i).toEmbedding)
    i j (copyCarrier q.1.embedding) (copyCarrier r.1.embedding)
    (selectedCopy_private_vertex_of_two_edges
      A B D C family selected e q (hStrong q) (hTwo q)) hCarrier
  subst j
  have hMapped :
      (bSupportPiece A q.1.embedding).map (Std i).toEmbedding.toFunctionEmbedding =
        (bSupportPiece A r.1.embedding).map (Std i).toEmbedding.toFunctionEmbedding := by
    rw [bSupportPiece_map_exact, bSupportPiece_map_exact]
    exact hPieces
  have hOldPieces := actualRecursiveSupport_map_injective
    (Std i).toEmbedding.toFunctionEmbedding hMapped
  have hqr : q = r := hOld hOldPieces
  cases hqr
  rfl

end ActiveLabels
end StructuralRamsey.Girth
