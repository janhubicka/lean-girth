import Girth.TrainColouredOwnerSelectedLift
import Girth.Support

/-!
# Track 1: selected A-strongness supplies owner-splitting oldStrong

For a full selected B embedding with A-strong image, every retained old
physical A-edge meeting its carrier twice is a genuine source A-edge.
This is the exact input required by selected_strong_of_old.
No new Ramsey property or source-copy existence is assumed.

DRAFT / UNCOMPILED; no kernel certificate is claimed.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}} {UA VB V I : Type v}

namespace ColouredOwnerSelectedCopy

/-- Translate an actual A-strong selected B embedding into the old
edge-incidence reflection premise used in the checked owner-splitting API. -/
theorem oldStrong_of_aStrong
    (A : StructuralRamsey.RelStructure L UA)
    (B : StructuralRamsey.RelStructure L VB)
    (D : StructuralRamsey.RelStructure L V)
    (H : ColouredEdgeOwnerSplit V I)
    (S : ColouredOwnerSelectedCopy (W := VB) H)
    (b : RelStructure.Embedding B D)
    (hEmbed : ∀ v : VB, S.embedding v = b v)
    (hSupport : ∀ f : H.OldEdge,
      ∃ a : RelStructure.Embedding A D, f.1 = copyCarrier a)
    (hSrc : ∀ a : RelStructure.Embedding A B,
      copyCarrier a ∈ S.sourceEdges)
    (hStrong : AStrong A D (copyCarrier b)) :
    ∀ (f : H.OldEdge) (x y : V),
      x ≠ y → x ∈ f.1 → y ∈ f.1 →
      x ∈ Set.range S.embedding → y ∈ Set.range S.embedding →
      ∃ a : S.SourceEdge, S.physicalEdge a = f := by
  classical
  intro f x y hxy hx hy hxb hyb
  obtain ⟨a, hfa⟩ := hSupport f
  have hxa : x ∈ copyCarrier a := by rw [← hfa]; exact hx
  have hya : y ∈ copyCarrier a := by rw [← hfa]; exact hy
  have hxB : x ∈ copyCarrier b := by
    obtain ⟨v, hv⟩ := hxb
    exact ⟨v, (hEmbed v).symm.trans hv⟩
  have hyB : y ∈ copyCarrier b := by
    obtain ⟨v, hv⟩ := hyb
    exact ⟨v, (hEmbed v).symm.trans hv⟩
  have hMeet : ¬ (copyCarrier a ∩ copyCarrier b).Subsingleton := by
    intro hs
    exact hxy (hs ⟨hxa, hxB⟩ ⟨hya, hyB⟩)
  have hSub : copyCarrier a ⊆ copyCarrier b := hStrong a hMeet
  have hFact : ∀ u : UA, ∃ v : VB, a u = b v := by
    intro u
    obtain ⟨v, hv⟩ := hSub ⟨u, rfl⟩
    exact ⟨v, hv.symm⟩
  let aB : RelStructure.Embedding A B := a.factorThroughRange b hFact
  have hFactor (u : UA) : a u = b (aB u) :=
    Classical.choose_spec (hFact u)
  let edge : S.SourceEdge := ⟨copyCarrier aB, hSrc aB⟩
  have hImg : b '' copyCarrier aB = copyCarrier a := by
    apply Set.Subset.antisymm
    · rintro z ⟨v, ⟨u, huv⟩, hvz⟩
      refine ⟨u, ?_⟩
      calc
        a u = b (aB u) := hFactor u
        _ = b v := by rw [huv]
        _ = z := hvz
    · rintro z ⟨u, hu⟩
      refine ⟨aB u, ⟨u, rfl⟩, ?_⟩
      exact (hFactor u).symm.trans hu
  have hSelectedImg : S.embedding '' copyCarrier aB =
      b '' copyCarrier aB := by
    apply Set.ext
    intro z
    constructor
    · rintro ⟨v, hv, hvz⟩
      exact ⟨v, hv, (hEmbed v).symm.trans hvz⟩
    · rintro ⟨v, hv, hvz⟩
      exact ⟨v, hv, (hEmbed v).trans hvz⟩
  refine ⟨edge, ?_⟩
  apply Subtype.ext
  calc
    (S.physicalEdge edge).1 = S.embedding '' edge.1 := S.edge_image edge
    _ = b '' copyCarrier aB := hSelectedImg
    _ = copyCarrier a := hImg
    _ = f.1 := hfa.symm

#print axioms StructuralRamsey.Girth.ColouredOwnerSelectedCopy.oldStrong_of_aStrong

end ColouredOwnerSelectedCopy
end StructuralRamsey.Girth
