import Girth.TrainFillingPrivateCompletedWSummand
import Girth.TrainFillingPrivateRealUnionLinear

set_option Elab.async false

/-!
# Support, coverage, strong summands and A-linearity of completed W

The ACTUAL cutoff-two W has all binary within-colour comparisons,
including between first-wagon summands. It retains precisely the
componentwise SMALL coloured k-hyperedges.

Every small-A copy of completed W has its spanning full edge
inside a single summand. The induced summand embeddings therefore
factor all small-A copies and show:
 * every F_p inclusion is A-strong;
 * the complete A-support of W is exactly the tagged union of the
   complete A-support families of the actual induced F_p;
 * if the old T is A-linear, then the completed W is A-linear.

These are input-side properties only. The Ramsey arrow and the
covered/marked order completion of its EHN output remain separate
Track 1 integration obligations.

All statements are candidates until exact-head Lean compilation.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v
variable {I : Type u} {V P : Type v}
variable [LinearOrder I] [LinearOrder V] [LinearOrder P]
variable (k : ℕ) (hk : 2 ≤ k)
variable (profile : Fin k → I)
variable (oldEdges : Set (Set V)) (colour : V → I)
variable (carrier : P → Set V)

private abbrev A :=
  colouredOrderedEdgeSource.{u,v} k profile
private noncomputable abbrev W :=
  completedFirstWagonColouredUnion k oldEdges colour carrier
private abbrev localStructure (p : P) :=
  (colouredOrderedEdgeTarget k oldEdges colour).induce (carrier p)
private noncomputable def inc (p : P) :
    Embedding (localStructure k oldEdges colour carrier p)
      (W k oldEdges colour carrier) :=
  completedFirstWagonSummandEmbedding k hk oldEdges colour carrier p

/-- Every small-A copy of the completed W is supported inside
one genuine first-wagon summand. This is the exact
factorization prerequisite for the subsequent proof, not a
postulated output embedding of any selected EHN witness. -/
theorem completedFirstWagon_ACopy_subset_summand :
    ∀ a : Embedding (A k profile) (W k oldEdges colour carrier),
      ∃ p : P, copyCarrier a ⊆
        Set.range (inc k hk oldEdges colour carrier p) := by
  intro a
  obtain ⟨p, hInside⟩ :=
    completedFirstWagon_ACopy_in_one_summand k profile
      oldEdges colour carrier a
  refine ⟨p, ?_⟩
  rintro z ⟨x, rfl⟩
  obtain ⟨y, hy⟩ := hInside x
  exact ⟨y, hy.symm⟩

/-- Every actual first-wagon summand is A-strong inside the
COMPLETED W, even though its external within-colour comparisons
are present in W. The spanning A-edge forces each A-copy
meeting one summand into exactly that summand. -/
theorem completedFirstWagonSummand_aStrong (p : P) :
    AStrong (A k profile) (W k oldEdges colour carrier)
      (copyCarrier (inc k hk oldEdges colour carrier p)) := by
  intro a hMeet
  obtain ⟨q, hLocal⟩ :=
    completedFirstWagon_ACopy_subset_summand
      k hk profile oldEdges colour carrier a
  by_cases hpq : q = p
  · subst q
    exact hLocal
  · have hSmall :
        (copyCarrier a ∩
          copyCarrier (inc k hk oldEdges colour carrier p)).Subsingleton := by
      intro z hz w hw
      obtain ⟨x, hx⟩ := hLocal hz.1
      obtain ⟨y, hy⟩ := hz.2
      have hqp : q = p :=
        congrArg Sigma.fst (hx.trans hy.symm)
      exact False.elim (hpq hqp)
    exact False.elim (hMeet hSmall)

/-- EXACT complete small-A support decomposition of completed W.
This differs from the raw coproduct's support theorem because
the binary relational order is now globally completed, while
the genuine spanning k-edge still localizes every A-copy.

No new cross-summand A-edges appear. -/
theorem completedFirstWagon_supportCopies_iff
    (e : Set (FirstWagonUnionVertex carrier)) :
    e ∈ supportCopies (A k profile) (W k oldEdges colour carrier) ↔
      ∃ (p : P)
        (f : Set {x : V // x ∈ carrier p}),
        f ∈ supportCopies (A k profile)
          (localStructure k oldEdges colour carrier p) ∧
        e = (inc k hk oldEdges colour carrier p).toFunctionEmbedding '' f := by
  constructor
  · rintro ⟨a, ha⟩
    obtain ⟨p, hLocal⟩ :=
      completedFirstWagon_ACopy_subset_summand
        k hk profile oldEdges colour carrier a
    let inclusion := inc k hk oldEdges colour carrier p
    have hFactor : ∀ x : ULift.{v} (Fin k),
        ∃ y : {y : V // y ∈ carrier p}, a x = inclusion y := by
      intro x
      obtain ⟨y, hy⟩ := hLocal ⟨x, rfl⟩
      exact ⟨y, hy.symm⟩
    let b : Embedding (A k profile)
        (localStructure k oldEdges colour carrier p) :=
      a.factorThroughRange inclusion hFactor
    have hComp : inclusion.comp b = a := by
      apply Embedding.ext
      intro x
      exact (Classical.choose_spec (hFactor x)).symm
    refine ⟨p, copyCarrier b, ⟨b, rfl⟩, ?_⟩
    calc
      e = copyCarrier a := ha
      _ = copyCarrier (inclusion.comp b) :=
        congrArg copyCarrier hComp.symm
      _ = inclusion.toFunctionEmbedding '' copyCarrier b :=
        (UniformPrivateTemplate.image_copyCarrier_comp
          (A k profile) (localStructure k oldEdges colour carrier p)
          (W k oldEdges colour carrier) inclusion b).symm
  · rintro ⟨p, f, ⟨b, hb⟩, he⟩
    let inclusion := inc k hk oldEdges colour carrier p
    refine ⟨inclusion.comp b, ?_⟩
    calc
      e = inclusion.toFunctionEmbedding '' f := he
      _ = inclusion.toFunctionEmbedding '' copyCarrier b :=
        congrArg (fun E : Set {x : V // x ∈ carrier p} =>
          inclusion.toFunctionEmbedding '' E) hb
      _ = copyCarrier (inclusion.comp b) :=
        UniformPrivateTemplate.image_copyCarrier_comp
          (A k profile) (localStructure k oldEdges colour carrier p)
          (W k oldEdges colour carrier) inclusion b

include hk in
/-- Completed W is A-covered whenever the genuine induced
first-wagon structures are A-covered. This is exactly
the source-side coverage needed for the ordered EHN call. -/
theorem completedFirstWagon_covered
    (hLocal : ∀ p (x : {x : V // x ∈ carrier p}),
      ∃ a : Embedding (A k profile)
        (localStructure k oldEdges colour carrier p), x ∈ copyCarrier a) :
    ∀ w : FirstWagonUnionVertex carrier,
      ∃ a : Embedding (A k profile)
        (W k oldEdges colour carrier), w ∈ copyCarrier a := by
  rintro ⟨p, x⟩
  obtain ⟨a, hx⟩ := hLocal p x
  obtain ⟨u, hu⟩ := hx
  refine ⟨(inc k hk oldEdges colour carrier p).comp a, ⟨u, ?_⟩⟩
  change (⟨p, a u⟩ : FirstWagonUnionVertex carrier) = ⟨p, x⟩
  exact congrArg (fun z : {z : V // z ∈ carrier p} =>
    (⟨p, z⟩ : FirstWagonUnionVertex carrier)) hu

include hk in
/-- A-linearity passes from the genuine LOCAL induced F_p
structures to the COMPLETED ordered disjoint union W.
The stronger global order relation does not affect the
componentwise A-support carrier intersections. -/
theorem completedFirstWagon_aLinear
    (hLocal : ∀ p : P,
      ALinear (A k profile) (localStructure k oldEdges colour carrier p)) :
    ALinear (A k profile) (W k oldEdges colour carrier) := by
  intro a b hDistinct
  have haSupport :
      copyCarrier a ∈ supportCopies (A k profile)
        (W k oldEdges colour carrier) := ⟨a, rfl⟩
  have hbSupport :
      copyCarrier b ∈ supportCopies (A k profile)
        (W k oldEdges colour carrier) := ⟨b, rfl⟩
  obtain ⟨p, fa, hfa, ha⟩ :=
    (completedFirstWagon_supportCopies_iff
      k hk profile oldEdges colour carrier (copyCarrier a)).mp haSupport
  obtain ⟨q, fb, hfb, hb⟩ :=
    (completedFirstWagon_supportCopies_iff
      k hk profile oldEdges colour carrier (copyCarrier b)).mp hbSupport
  by_cases hpq : p = q
  · subst q
    have hfne : fa ≠ fb := by
      intro hf
      apply hDistinct
      change copyCarrier a = copyCarrier b
      calc
        copyCarrier a =
            (inc k hk oldEdges colour carrier p).toFunctionEmbedding '' fa := ha
        _ = (inc k hk oldEdges colour carrier p).toFunctionEmbedding '' fb := by
          rw [hf]
        _ = copyCarrier b := hb.symm
    obtain ⟨aLocal, haLoc⟩ := hfa
    obtain ⟨bLocal, hbLoc⟩ := hfb
    have hDifferent : ¬ SameCopy aLocal bLocal := by
      intro hs
      exact hfne (by
        calc
          fa = copyCarrier aLocal := haLoc
          _ = copyCarrier bLocal := hs
          _ = fb := hbLoc.symm)
    have hLocalSmall : (fa ∩ fb).Subsingleton := by
      rw [haLoc, hbLoc]
      exact hLocal p aLocal bLocal hDifferent
    rw [ha, hb]
    exact subsingleton_image_inter_of_injective
      (inc k hk oldEdges colour carrier p).toFunctionEmbedding
      fa fb hLocalSmall
  · intro z hz w hw
    rw [ha, hb] at hz
    obtain ⟨x, _, hxz⟩ := hz.1
    obtain ⟨y, _, hyz⟩ := hz.2
    have hEq : p = q := congrArg Sigma.fst (hxz.trans hyz.symm)
    exact False.elim (hpq hEq)

end StructuralRamsey.Girth
