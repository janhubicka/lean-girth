import Girth.ACopyCanonicalLinks

set_option autoImplicit false

/-!
# Exact physical A-copy node domain of a genuine induced link

For an induced link B.induce S included in B, the actual A-copy sites
of the link map bijectively onto the actual ambient A-copies whose
entire image carrier lies in S.

This is stronger and more concrete than point coverage, and removes
the separate FullNodeDomains assumption in the actual picture. It is
independent of A-linearity, irreducibility, Ramsey properties and
chosen order, because physical sites are image-copy carriers.
-/

namespace StructuralRamsey.Girth.ACopyActualLinkDomain

open StructuralRamsey.RelStructure
open ACopyCanonicalSites ACopyCanonicalLinks
open ACopyActualRelationalStar

universe u v

variable {L : RelLanguage.{u}}
variable {U W : Type v} {A : RelStructure L U}

/-- Actual physical A-nodes of an induced link embed into the source's
actual A-copy sites. No arbitrary node index map is assumed. -/
noncomputable def inducedNodeMap
    (B : RelStructure L W) (S : Set W) :
    supportCopies A (B.induce S) ↪ supportCopies A B :=
  ⟨nodeMap (RelStructure.inclusion B S),
    nodeMap_injective (RelStructure.inclusion B S)⟩

/-- A physical A-node occurs in the induced link iff every vertex of
its ambient A-carrier lies in the link domain. Thus the induced link
has the complete physical-node domain required by faithful star gluing. -/
theorem inducedNodeMap_range_iff
    (B : RelStructure L W) (S : Set W) (p : supportCopies A B) :
    p ∈ Set.range (inducedNodeMap (A := A) B S) ↔ p.val ⊆ S := by
  classical
  let j : Embedding (B.induce S) B := RelStructure.inclusion B S
  constructor
  · rintro ⟨q, rfl⟩
    change (nodeMap j q).val ⊆ S
    intro x hx
    rw [nodeMap_mem_image] at hx
    obtain ⟨y, _, hy⟩ := hx
    rw [← hy]
    exact y.property
  · intro hInside
    have hRange : ∀ a : U, ∃ y : ↥S,
        representative p a = j y := by
      intro a
      have hp : representative p a ∈ p.val := by
        rw [← representative_carrier p]
        exact ⟨a, rfl⟩
      refine ⟨⟨representative p a, hInside hp⟩, rfl⟩
    let b : Embedding A (B.induce S) :=
      (representative p).factorThroughRange j hRange
    let q : supportCopies A (B.induce S) :=
      ⟨copyCarrier b, ⟨b, rfl⟩⟩
    refine ⟨q, ?_⟩
    apply Subtype.ext
    change copyCarrier (j.comp (representative q)) = p.val
    have hLocal : SameCopy b (representative q) :=
      (representative_carrier q).symm
    have hComp : SameCopy (j.comp b) (j.comp (representative q)) :=
      sameCopy_comp j b (representative q) hLocal
    have hPullback : j.comp b = representative p := by
      apply Embedding.ext
      intro a
      exact (Classical.choose_spec (hRange a)).symm
    calc
      copyCarrier (j.comp (representative q)) =
          copyCarrier (j.comp b) := hComp.symm
      _ = copyCarrier (representative p) := congrArg copyCarrier hPullback
      _ = p.val := representative_carrier p

end StructuralRamsey.Girth.ACopyActualLinkDomain
