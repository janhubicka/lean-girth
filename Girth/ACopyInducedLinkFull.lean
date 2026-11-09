import Girth.ACopySupportAssembly

set_option autoImplicit false

/-!
# Full physical node domains from induced gluing links

If a gluing link is the *full induced substructure* on the shared point
domain, and its physical nodes list **all** A-copies in that domain, then
the source node-domain fullness required by ACopyFullDomain is a theorem,
not an additional geometric assumption.

This is separate from point coverage by shared nodes. A nonshared A-copy
can have all its points shared (the three-edge-path regression).

The proof is relational: it factors an induced A-embedding with image inside
the link through the link inclusion, uses physical-copy coverage there,
and then uses injectivity of the source's physical-carrier map. No
A-linearity, Ramsey property, or new axioms are needed.
-/

namespace StructuralRamsey.Girth.ACopyInducedLinkFull

open StructuralRamsey.RelStructure
open ACopyLayeredStar ACopyDecoratedStar ACopyFullDomain

universe u v

variable {L : RelLanguage.{u}}
variable {K W U : Type v}
variable {A : RelStructure L K}
variable {S : RelStructure L W} {Q : RelStructure L U}

/-- An induced link which records all its physical A-copies necessarily
contains every source physical node whose complete carrier lies in its
point domain. Carrier-injectivity of the source physical node labels
is essential: otherwise there could be distinct source labels for one
physical A-copy and only one would belong to the link. -/
theorem full_physical_node_domain_of_induced_link
    {ES EQ : Type v}
    (j : Embedding Q S)
    (source : ES → Embedding A S)
    (link : EQ → Embedding A Q)
    (beta : EQ → ES)
    (hSource : Function.Injective (fun e => copyCarrier (source e)))
    (hLink : ∀ b : Embedding A Q, ∃ q : EQ, SameCopy b (link q))
    (hBeta : ∀ q, SameCopy (j.comp (link q)) (source (beta q)))
    (e : ES)
    (hInside : copyCarrier (source e) ⊆ copyCarrier j) :
    ∃ q : EQ, beta q = e := by
  have hPre : ∀ a : K, ∃ b : U, source e a = j b := by
    intro a
    rcases hInside ⟨a, rfl⟩ with ⟨b, hb⟩
    exact ⟨b, hb.symm⟩
  let b : Embedding A Q := (source e).factorThroughRange j hPre
  obtain ⟨q, hq⟩ := hLink b
  have hEq : j.comp b = source e := by
    apply Embedding.ext
    intro a
    exact (Classical.choose_spec (hPre a)).symm
  refine ⟨q, hSource ?_⟩
  have hComp : SameCopy (j.comp b) (j.comp (link q)) := by
    apply Set.Subset.antisymm
    · rintro _ ⟨a, rfl⟩
      have ha : b a ∈ copyCarrier (link q) := by
        rw [← hq]
        exact ⟨a, rfl⟩
      obtain ⟨z, hz⟩ := ha
      exact ⟨z, congrArg j hz⟩
    · rintro _ ⟨a, rfl⟩
      have ha : link q a ∈ copyCarrier b := by
        rw [hq]
        exact ⟨a, rfl⟩
      obtain ⟨z, hz⟩ := ha
      exact ⟨z, congrArg j hz⟩
  calc
    copyCarrier (source (beta q)) = copyCarrier (j.comp (link q)) := (hBeta q).symm
    _ = copyCarrier (j.comp b) := hComp.symm
    _ = copyCarrier (source e) := congrArg copyCarrier hEq

/-- An actual induced shared chart automatically supplies the abstract
full-domain condition of the decorated A-copy star. The link's node
family must cover *every* A-copy induced on its point set, not merely
cover the points. The complete source coordinate equation is used only
to identify abstract and genuine physical-node carriers. -/
theorem decorated_fullNodeDomains_of_induced_links
    {Core I PC : Type v} {Source Shared PS PQ : I → Type v}
    {N : Diagram Core I Source Shared}
    (D : Data N K PC PS PQ)
    (C : (i : I) → RelStructure L (Quotient (D.sourceEq i)))
    (src : (i : I) → Source i → Embedding A (C i))
    (hSrcCarrier : ∀ i e, copyCarrier (src i e) = sourceNodeCarrier D i e)
    (hSource : ∀ i, Function.Injective (sourceNodeCarrier D i))
    (link : (i : I) → Shared i →
      Embedding A ((C i).induce (sharedSourcePoints D i)))
    (hLink : ∀ i (b : Embedding A ((C i).induce (sharedSourcePoints D i))),
      ∃ q : Shared i, SameCopy b (link i q))
    (hBeta : ∀ i q,
      SameCopy ((RelStructure.inclusion (C i) (sharedSourcePoints D i)).comp
          (link i q)) (src i (N.beta i q))) :
    FullNodeDomains D := by
  intro i e hInside
  let j : Embedding ((C i).induce (sharedSourcePoints D i)) (C i) :=
    RelStructure.inclusion (C i) (sharedSourcePoints D i)
  have hSrcInj : Function.Injective (fun e => copyCarrier (src i e)) := by
    intro e f h
    apply hSource i
    calc
      sourceNodeCarrier D i e = copyCarrier (src i e) := (hSrcCarrier i e).symm
      _ = copyCarrier (src i f) := h
      _ = sourceNodeCarrier D i f := hSrcCarrier i f
  have hContain : copyCarrier (src i e) ⊆ copyCarrier j := by
    rw [hSrcCarrier i e]
    intro p hp
    have hpShared : p ∈ sharedSourcePoints D i := hInside hp
    exact ⟨⟨p, hpShared⟩, rfl⟩
  exact full_physical_node_domain_of_induced_link j (src i) (link i)
    (N.beta i) hSrcInj (hLink i) (hBeta i) e hContain

end StructuralRamsey.Girth.ACopyInducedLinkFull
