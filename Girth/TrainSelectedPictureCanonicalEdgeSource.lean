import Girth.TrainSelectedPictureOutputLabelCover

/-!
# Circulation: canonical core/private ownership of actual support edges

The exhaustive label-cover statement has an intentional ambiguity:
a physical shared edge may be represented by old labels in several
attached standards. The ACTUAL physical edge pushout gives a canonical
core/private distinction. Genuine private edges have exactly one
standard index and one old edge; no core edge equals a private edge.

This is the precise ownership property needed by a minimum-segment
construction. It does not infer any segment index for designated
copies from geometric containment, nor build a legal cyclic reduct.
No appendix results.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v

section CanonicalActualSource

variable {L : RelLanguage.{u}} {UA Old Core I : Type v}
variable (A : RelStructure L UA) (hA : A.Irreducible)
variable (B : RelStructure L Old) (S : Set Old)
variable (D : RelStructure L Core)
variable (f : I → RelStructure.Embedding (B.induce S) D)

local notation "OldEdge" => OldACarrierEdge A B
local notation "CoreEdge" => OldACarrierEdge A D
local notation "SharedEdge" => SharedOldACarrierEdge A B S
local notation "inOld" => sharedOldACarrierInclusion A B S
local notation "inCore" => sharedOldACarrierCoreEmbedding A B S D f
local notation "Eqv" => actualAPictureEdgeEquiv A hA B S D f
local notation "ActualEdge" => OldACarrierEdge A
  (RelStructure.Attachment.attach B S D f)
local notation "StdEdge" => (fun (i : I) (a : OldEdge) =>
  Eqv (physicalStandardEdge inOld inCore i a))
local notation "CoreActual" => (fun (b : CoreEdge) =>
  Eqv (physicalCoreEdge inOld I b))

/-- Canonical exhaustive normal form of a physical A-support edge:
either one actual witness-core edge, or one private old edge with its
standard index. The private case explicitly excludes the shared edge
image; the two arms are therefore disjoint in the physical pushout. -/
theorem actualAttachedAEdge_core_or_private
    (edge : ActualEdge) :
    (∃ b : CoreEdge, edge = CoreActual b) ∨
    (∃ (i : I) (a : OldEdge),
      a ∉ Set.range inOld ∧ edge = StdEdge i a) := by
  let pre := (Eqv).symm edge
  cases hp : pre with
  | inl b =>
      left
      refine ⟨b, ?_⟩
      have hPhysical : pre = physicalCoreEdge inOld I b := hp
      apply (Eqv).symm.injective
      simpa [pre] using hPhysical
  | inr ia =>
      rcases ia with ⟨i, a⟩
      right
      refine ⟨i, a.1, a.2, ?_⟩
      have hPhysical : pre =
          physicalStandardEdge inOld inCore i a.1 := by
        rw [physicalStandardEdge_private inOld inCore i a.1 a.2]
        exact hp
      apply (Eqv).symm.injective
      simpa [pre] using hPhysical

/-- Two representations of the SAME genuinely private output edge
have identical standard indices and old physical edge labels.
This is stronger than equality of their vertex carriers alone. -/
theorem actualAttachedAEdge_private_owner_unique
    (i j : I) (a b : OldEdge)
    (ha : a ∉ Set.range inOld)
    (hb : b ∉ Set.range inOld)
    (hEq : StdEdge i a = StdEdge j b) :
    i = j ∧ a = b := by
  have hPhysical := (Eqv).injective hEq
  rw [physicalStandardEdge_private inOld inCore i a ha,
      physicalStandardEdge_private inOld inCore j b hb] at hPhysical
  have hPair := Sum.inr.inj hPhysical
  exact ⟨congrArg Prod.fst hPair,
    congrArg (fun q : I × {x : OldEdge // x ∉ Set.range inOld} =>
      q.2.1) hPair⟩

/-- A core A-support edge cannot be the image of a genuinely
private standard edge, regardless of overlap of their carriers. -/
theorem actualAttachedAEdge_core_ne_private
    (b : CoreEdge) (i : I) (a : OldEdge)
    (ha : a ∉ Set.range inOld) :
    CoreActual b ≠ StdEdge i a := by
  intro heq
  have hPhysical := (Eqv).injective heq
  rw [physicalStandardEdge_private inOld inCore i a ha] at hPhysical
  cases hPhysical

end CanonicalActualSource

end StructuralRamsey.Girth
