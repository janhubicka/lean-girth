import Girth.TrainFillingPrivateSummand

set_option Elab.async false

/-!
# One selected disjoint-union copy gives all first-wagon templates

At cutoff two, X is chosen once, together with a selected embedding
s : W -> X of the DISJOINT UNION W of the first wagons. Every summand
has its own type F_p and embedding u_p : F_p -> W. The actual local
template is s.comp (u_p), not an independently selected copy of W.

The central elementary lemma proves that A-strongness of a copy is
preserved by composing A-strong embeddings. Consequently, provided
the inclusions u_p are A-strong (true for the disjoint union of the
original first-wagon relational structures), the selected W-copy's
strongness implies all selected summand strongnesses.

This constructs one SummandPrivateTemplate family from the SAME
selected s, without assuming each first wagon is isomorphic to W.
The construction of W as a concrete disjoint union, and the selected
M-copy with exact train maps, remain separate application tasks.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v

/-- Strong inducedness with respect to the coloured edge type A
is transitive under composition of relational embeddings. This is
a direct pullback of every A-copy meeting the smaller range twice. -/
theorem aStrong_compose
    {L : RelLanguage.{u}}
    {UA W X Y : Type v}
    (A : RelStructure L UA)
    (F : RelStructure L Y)
    (B : RelStructure L W)
    (R : RelStructure L X)
    (inc : RelStructure.Embedding F B)
    (sel : RelStructure.Embedding B R)
    (hInc : AStrong A B (copyCarrier inc))
    (hSel : AStrong A R (copyCarrier sel)) :
    AStrong A R (copyCarrier (sel.comp inc)) := by
  classical
  intro a hMeet
  have hSubSel : copyCarrier (sel.comp inc) ⊆ copyCarrier sel := by
    rintro z ⟨y, hy⟩
    exact ⟨inc y, hy⟩
  have hMeetSel : ¬ (copyCarrier a ∩ copyCarrier sel).Subsingleton := by
    intro hSmall
    apply hMeet
    intro z hz w hw
    exact hSmall ⟨hz.1, hSubSel hz.2⟩
      ⟨hw.1, hSubSel hw.2⟩
  have hInsideSel : copyCarrier a ⊆ copyCarrier sel :=
    hSel a hMeetSel
  have hFactor : ∀ x : UA, ∃ y : W, a x = sel y := by
    intro x
    obtain ⟨y, hy⟩ := hInsideSel ⟨x, rfl⟩
    exact ⟨y, hy.symm⟩
  let b : RelStructure.Embedding A B :=
    a.factorThroughRange sel hFactor
  have hMeetInc : ¬ (copyCarrier b ∩ copyCarrier inc).Subsingleton := by
    intro hSmall
    apply hMeet
    intro z hz w hw
    obtain ⟨hzA, hzC⟩ := hz
    obtain ⟨hwA, hwC⟩ := hw
    obtain ⟨x, hx⟩ := hzA
    obtain ⟨y, hy⟩ := hzC
    obtain ⟨x', hx'⟩ := hwA
    obtain ⟨y', hy'⟩ := hwC
    have hxy : b x = inc y := sel.injective (by
      calc
        sel (b x) = a x := (Classical.choose_spec (hFactor x)).symm
        _ = z := hx
        _ = sel (inc y) := hy.symm)
    have hx'y' : b x' = inc y' := sel.injective (by
      calc
        sel (b x') = a x' := (Classical.choose_spec (hFactor x')).symm
        _ = w := hx'
        _ = sel (inc y') := hy'.symm)
    have heq : b x = b x' :=
      hSmall ⟨⟨x, rfl⟩, ⟨y, hxy⟩⟩
        ⟨⟨x', rfl⟩, ⟨y', hx'y'⟩⟩
    calc
      z = a x := hx.symm
      _ = sel (b x) := Classical.choose_spec (hFactor x)
      _ = sel (b x') := congrArg sel heq
      _ = a x' := (Classical.choose_spec (hFactor x')).symm
      _ = w := hx'
  have hInsideInc : copyCarrier b ⊆ copyCarrier inc :=
    hInc b hMeetInc
  rintro z ⟨x, hx⟩
  obtain ⟨y, hy⟩ := hInsideInc ⟨x, rfl⟩
  refine ⟨y, ?_⟩
  calc
    (sel.comp inc) y = sel (inc y) := rfl
    _ = sel (b x) := congrArg sel hy.symm
    _ = a x := (Classical.choose_spec (hFactor x)).symm
    _ = z := hx

namespace SummandPrivateTemplate

variable {L : RelLanguage.{u}}
variable {UA W X V P : Type v}

/-- Build all unequal first-wagon templates from ONE selected embedding
of the disjoint union into X. Each local template has its own target
edge family, and every local template shares the full A-support of X.
No separate strongness of the composites is assumed. -/
noncomputable def fromSelectedUnion
    (A : RelStructure L UA)
    (B : RelStructure L W)
    (R : RelStructure L X)
    (oldCarrier : P → Set V)
    (local : (p : P) → RelStructure L {x : V // x ∈ oldCarrier p})
    (include : (p : P) → RelStructure.Embedding (local p) B)
    (selected : RelStructure.Embedding B R)
    (hInclude : ∀ p, AStrong A B (copyCarrier (include p)))
    (hSelected : AStrong A R (copyCarrier selected))
    (hCovered : ∀ p (x : {x : V // x ∈ oldCarrier p}),
      ∃ a : RelStructure.Embedding A (local p), x ∈ copyCarrier a) :
    SummandPrivateTemplate V P X where
  oldCarrier := oldCarrier
  templateEdges := supportCopies A R
  piece := fun p =>
    UniformPrivateTemplate.ofStrongEmbedding
      A (local p) R (selected.comp (include p))
        (aStrong_compose A (local p) B R
          (include p) selected (hInclude p) hSelected)
        (hCovered p)
  templateEdges_eq := by
    intro p
    rfl

end SummandPrivateTemplate
end StructuralRamsey.Girth
