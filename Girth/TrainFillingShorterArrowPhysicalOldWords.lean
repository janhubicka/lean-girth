import Girth.TrainFillingIndexedContractedCarriers
import Girth.ALinearRamsey

set_option Elab.async false

/-!
# The actual shorter M Ramsey arrow gives one common complete old-edge word

The shorter-train ORDER witness supplies an ordinary relational
Ramsey arrow A→M in the ambient N, as well as stronger designated
train/strongness information for the genuinely selected M-copy.

The complete A-support edges of M have an EXACT physical indexing
by the contracted heterogeneous first-wagon labels (choice, wagon).
To colour the old edges of N by COMPLETE local template-colour
words, colour each relational A-embedding a : A↪N by the word on
the physical support carrier a(A). This is independent of how the
same physical carrier might be represented by several embeddings.

Choose a monochromatic M-copy b by the existing Ramsey arrow.
Every contracted source first wagon is the image of a genuine
A-embedding into M, so its b-image receives that same word.
Actual local linearity makes the image of these full first-wagon
carriers injective as OLD N-edge labels. Thus the old-word arrow
needed in the last two-arrow colour composition is a theorem,
not a separately postulated hOldArrow input.

The stage's designated-family membership, train-faithfulness and
strongness remain to be retained by choosing b from the stronger
DesignatedArrow rather than a bare Arrow in the final application.
No output girth or final target-labelled arrow is claimed here.
-/

namespace StructuralRamsey.Girth.IndexedPrivateChoice

open StructuralRamsey.RelStructure

universe u v w
variable {L : RelLanguage.{u}}
variable {C V P X Y UA : Type v} {κ : Type w}
variable (U : C → PrivateWagonInput V P X)
variable [Nontrivial X]

/-- The actual relational SHORTER Ramsey arrow, combined with
complete M-support equality and linearity, yields one old physical
edge injection β:C×P↪H.OldEdge on which the WHOLE local template
colour word is constant. No independent β or word-equality hypothesis. -/
theorem contractedOldEdge_commonWord_of_relationalRamsey
    [Nonempty (C × P)]
    (A : RelStructure L UA)
    (M : RelStructure L (Vertex U))
    (N : RelStructure L Y)
    (H : UniformFillingData Y X)
    (hOld : H.oldEdges = supportCopies A N)
    (hSupport : supportCopies A M = Set.range (contractedCarrier U))
    (hLinear : ∀ c : C, ∀ p q : P, p ≠ q →
      ((U c).oldCarrier p ∩ (U c).oldCarrier q).Subsingleton)
    (hArrow : StructuralRamsey.Arrow A M N (H.TemplateEdge → κ))
    (word : H.OldEdge → H.TemplateEdge → κ) :
    ∃ (β : (C × P) ↪ H.OldEdge)
      (ρ : H.TemplateEdge → κ),
      ∀ cp : C × P, word (β cp) = ρ := by
  classical
  let χ : Embedding A N → H.TemplateEdge → κ :=
    fun a => word ⟨copyCarrier a, by
      rw [hOld]
      exact ⟨a, rfl⟩⟩
  obtain ⟨b, hb⟩ := hArrow χ
  let vertex : Vertex U ↪ Y := b.toFunctionEmbedding
  have hImage : ∀ cp : C × P,
      vertex '' contractedCarrier U cp ∈ H.oldEdges := by
    intro cp
    rw [hOld]
    have hc : contractedCarrier U cp ∈ supportCopies A M := by
      rw [hSupport]
      exact ⟨cp, rfl⟩
    exact supportCopy_image_mem A M N b
      ⟨contractedCarrier U cp, hc⟩
  let β : (C × P) ↪ H.OldEdge :=
    contractedOldEdgeEmbedding U hLinear H vertex hImage
  obtain ⟨cp₀⟩ := (inferInstance : Nonempty (C × P))
  have hRep (cp : C × P) :
      ∃ a : Embedding A M,
        copyCarrier a = contractedCarrier U cp := by
    have h : contractedCarrier U cp ∈ supportCopies A M := by
      rw [hSupport]
      exact ⟨cp, rfl⟩
    obtain ⟨a, ha⟩ := h
    exact ⟨a, ha.symm⟩
  let a₀ : Embedding A M := Classical.choose (hRep cp₀)
  let ρ : H.TemplateEdge → κ := χ (b.comp a₀)
  refine ⟨β, ρ, ?_⟩
  intro cp
  let a : Embedding A M := Classical.choose (hRep cp)
  have hCarrier : (β cp).1 = copyCarrier (b.comp a) := by
    calc
      (β cp).1 = vertex '' contractedCarrier U cp :=
        contractedOldEdgeEmbedding_carrier U hLinear H vertex hImage cp
      _ = vertex '' copyCarrier a :=
        congrArg (fun F : Set (Vertex U) => vertex '' F)
          (Classical.choose_spec (hRep cp)).symm
      _ = copyCarrier (b.comp a) :=
        (copyCarrier_comp_eq_image b a).symm
  have hMember : copyCarrier (b.comp a) ∈ H.oldEdges := by
    rw [hOld]
    exact ⟨b.comp a, rfl⟩
  have hOldEdgeEq :
      β cp = (⟨copyCarrier (b.comp a), hMember⟩ : H.OldEdge) :=
    Subtype.ext hCarrier
  calc
    word (β cp) = χ (b.comp a) :=
      congrArg word hOldEdgeEq
    _ = χ (b.comp a₀) := hb a a₀
    _ = ρ := rfl

end StructuralRamsey.Girth.IndexedPrivateChoice
