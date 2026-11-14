import Girth.TrainFillingPrivateRealUnionColoured
import Girth.TrainFillingPrivateUniform

set_option Elab.async false

/-!
# Exact support edges and A-linearity of the REAL unequal union W

Let W = disjointUnion_p F_p, where each F_p is its actual
induced relational first-wagon structure. The coloured edge type
A has one spanning relation and cannot straddle summands.

Every A-support edge of W is therefore LITERALLY the image
of an A-support edge in exactly one summand F_p. Conversely,
every local A-support edge gives a genuine support edge of W.

This exact support decomposition proves A-linearity of W
from A-linearity of each original first wagon, with NO new
global old-edge linearity premise and no false assertion that
different original first-wagon CARRIERS are disjoint before
making the tagged union.

The constructor is independent of the EHN output, Ramsey
arrow or new filled M. In the actual cutoff-two application
local A-linearity is inherited from the original linear T,
while first-wagon carrier linearity of T is a separate fact
needed later for contraction, supplied by its first tail girth.

Uncompiled proof candidates, no new axioms/sorries.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}} {UA V P : Type v}

/-- Every actual A-support edge of the genuine disjoint union W
is the exact IMAGE of some local F_p A-support edge; conversely,
each of these local images is an actual W A-support edge. This
does not identify two different physical occurrence labels. -/
theorem firstWagonDisjointUnion_supportCopies_iff
    (A : RelStructure L UA)
    (oldCarrier : P → Set V)
    (local : (p : P) → RelStructure L {x : V // x ∈ oldCarrier p})
    (hPositive : ∀ sym : L.Symbol, 0 < L.arity sym)
    (hSpan : HasSpanningRelation A)
    (e : Set (FirstWagonUnionVertex oldCarrier)) :
    e ∈ supportCopies A (firstWagonDisjointUnion oldCarrier local) ↔
      ∃ (p : P) (f : Set {x : V // x ∈ oldCarrier p}),
        f ∈ supportCopies A (local p) ∧
        e = (firstWagonSummandEmbedding oldCarrier local hPositive p)
             .toFunctionEmbedding '' f := by
  constructor
  · rintro ⟨a, ha⟩
    obtain ⟨p, hInside⟩ :=
      firstWagonUnion_Acopy_in_one_summand
        A oldCarrier local hPositive hSpan a
    let inc := firstWagonSummandEmbedding oldCarrier local hPositive p
    have hFactor : ∀ x : UA,
        ∃ w : {x : V // x ∈ oldCarrier p}, a x = inc w := by
      intro x
      obtain ⟨w, hw⟩ := hInside ⟨x, rfl⟩
      exact ⟨w, hw.symm⟩
    let b : Embedding A (local p) :=
      a.factorThroughRange inc hFactor
    have hComp : inc.comp b = a := by
      apply Embedding.ext
      intro x
      exact (Classical.choose_spec (hFactor x)).symm
    refine ⟨p, copyCarrier b, ⟨b, rfl⟩, ?_⟩
    calc
      e = copyCarrier a := ha
      _ = copyCarrier (inc.comp b) := congrArg copyCarrier hComp.symm
      _ = inc.toFunctionEmbedding '' copyCarrier b :=
        (UniformPrivateTemplate.image_copyCarrier_comp
          A (local p) (firstWagonDisjointUnion oldCarrier local) inc b).symm
  · rintro ⟨p, f, ⟨b, hb⟩, he⟩
    let inc := firstWagonSummandEmbedding oldCarrier local hPositive p
    refine ⟨inc.comp b, ?_⟩
    calc
      e = inc.toFunctionEmbedding '' f := he
      _ = inc.toFunctionEmbedding '' copyCarrier b :=
        congrArg (fun E : Set {x : V // x ∈ oldCarrier p} =>
          inc.toFunctionEmbedding '' E) hb
      _ = copyCarrier (inc.comp b) :=
        UniformPrivateTemplate.image_copyCarrier_comp
          A (local p) (firstWagonDisjointUnion oldCarrier local) inc b

/-- Under an injective vertex map, a pair of IMAGE edge carriers
has at most one common vertex whenever its original two edge
carriers have at most one common vertex. -/
theorem subsingleton_image_inter_of_injective
    {X Y : Type v} (f : X ↪ Y)
    (E F : Set X) (hSmall : (E ∩ F).Subsingleton) :
    (f '' E ∩ f '' F).Subsingleton := by
  rintro z ⟨x, hx, hxz⟩ ⟨y, hy, hyz⟩
    w ⟨a, ha, haw⟩ ⟨b, hb, hbw⟩
  have hxy : x = y := f.injective (hxz.trans hyz.symm)
  have hab : a = b := f.injective (haw.trans hbw.symm)
  subst y
  subst b
  have hxa : x = a := hSmall ⟨hx, hy⟩ ⟨ha, hb⟩
  calc
    z = f x := hxz.symm
    _ = f a := congrArg f hxa
    _ = w := haw

/-- A-linear original first wagons yield an A-linear disjoint
union W. If two A-copies live in different summands then they
have NO common point. If they live in one summand, its checked
local A-linearity controls their intersection. -/
theorem firstWagonDisjointUnion_aLinear
    (A : RelStructure L UA)
    (oldCarrier : P → Set V)
    (local : (p : P) → RelStructure L {x : V // x ∈ oldCarrier p})
    (hPositive : ∀ sym : L.Symbol, 0 < L.arity sym)
    (hSpan : HasSpanningRelation A)
    (hLocalLinear : ∀ p : P, ALinear A (local p)) :
    ALinear A (firstWagonDisjointUnion oldCarrier local) := by
  intro a b hDifferent
  have haSupport : copyCarrier a ∈
      supportCopies A (firstWagonDisjointUnion oldCarrier local) :=
    ⟨a, rfl⟩
  have hbSupport : copyCarrier b ∈
      supportCopies A (firstWagonDisjointUnion oldCarrier local) :=
    ⟨b, rfl⟩
  obtain ⟨p, fa, hfa, ha⟩ :=
    (firstWagonDisjointUnion_supportCopies_iff
      A oldCarrier local hPositive hSpan (copyCarrier a)).mp haSupport
  obtain ⟨q, fb, hfb, hb⟩ :=
    (firstWagonDisjointUnion_supportCopies_iff
      A oldCarrier local hPositive hSpan (copyCarrier b)).mp hbSupport
  by_cases hpq : p = q
  · subst q
    have hfne : fa ≠ fb := by
      intro hEq
      apply hDifferent
      change copyCarrier a = copyCarrier b
      calc
        copyCarrier a =
            (firstWagonSummandEmbedding oldCarrier local hPositive p)
              .toFunctionEmbedding '' fa := ha
        _ = (firstWagonSummandEmbedding oldCarrier local hPositive p)
              .toFunctionEmbedding '' fb := by rw [hEq]
        _ = copyCarrier b := hb.symm
    obtain ⟨aLocal, haLoc⟩ := hfa
    obtain ⟨bLocal, hbLoc⟩ := hfb
    have hNotSame : ¬ SameCopy aLocal bLocal := by
      intro hSame
      exact hfne (by
        calc
          fa = copyCarrier aLocal := haLoc
          _ = copyCarrier bLocal := hSame
          _ = fb := hbLoc.symm)
    have hLocalSmall : (fa ∩ fb).Subsingleton := by
      rw [haLoc, hbLoc]
      exact hLocalLinear p aLocal bLocal hNotSame
    rw [ha, hb]
    exact subsingleton_image_inter_of_injective
      (firstWagonSummandEmbedding oldCarrier local hPositive p)
        .toFunctionEmbedding fa fb hLocalSmall
  · intro z hz w hw
    rw [ha, hb] at hz
    obtain ⟨x, _, hxz⟩ := hz.1
    obtain ⟨y, _, hyz⟩ := hz.2
    have heq : p = q :=
      congrArg Sigma.fst (hxz.trans hyz.symm)
    exact False.elim (hpq heq)

end StructuralRamsey.Girth
