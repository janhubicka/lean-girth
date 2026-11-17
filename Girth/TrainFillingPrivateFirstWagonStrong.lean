import Girth.TrainFillingPrivateRealUnionLinear

set_option Elab.async false

/-!
# The original first wagon has NO extra induced A-edges

At cutoff two, the actual first wagon F_p is defined as a
CLASS of original T-edges, with carrier V(F_p).
Constructing its relational structure as D.induce V(F_p)
is legitimate only if this induced structure contains
EXACTLY the edges owned by the first wagon p.

Old A-linearity alone does not guarantee this: carrier
linearity of the FIRST WAGONS is a separate condition.
With the genuine owner map e -> firstWagon(e), every
original A-support edge lies inside its owner's carrier.
If an A-copy meets another first-wagon carrier twice,
linearity of first-wagon carriers forces that carrier
to have the SAME owner. Thus every first wagon is
A-strongly induced in the original D, and any A-edge
of its induced reduct belongs to that original wagon.

The concrete train already supplies the edge owner,
old-carrier containment and first-tail girth>2.
These are INPUT facts of original T, not output
properties assumed of the shortened M or filling H.

Candidates until exact-head Lean compilation.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}} {UA V P : Type v}

/-- The original first wagon's carrier is A-strong inside
the ORIGINAL train's relational support, derived solely
from its genuine edge-owner map and linearity of distinct
first-wagon carriers. No selected new M/H geometry. -/
theorem originalFirstWagonCarrier_aStrong
    (A : RelStructure L UA)
    (D : RelStructure L V)
    (oldCarrier : P → Set V)
    (owner : {e : Set V // e ∈ supportCopies A D} → P)
    (hOwnerCarrier : ∀ e, e.1 ⊆ oldCarrier (owner e))
    (hWagonLinear : ∀ p q : P, p ≠ q →
      (oldCarrier p ∩ oldCarrier q).Subsingleton)
    (p : P) :
    AStrong A D (oldCarrier p) := by
  intro a hMeet
  let e : {e : Set V // e ∈ supportCopies A D} :=
    ⟨copyCarrier a, ⟨a, rfl⟩⟩
  by_cases hp : owner e = p
  · exact hp ▸ (hOwnerCarrier e)
  · have hSmall :
        (copyCarrier a ∩ oldCarrier p).Subsingleton := by
      intro x hx y hy
      have hSmallWagons :
          (oldCarrier p ∩ oldCarrier (owner e)).Subsingleton :=
        hWagonLinear p (owner e) (Ne.symm hp)
      exact hSmallWagons
        ⟨hx.2, hOwnerCarrier e hx.1⟩
        ⟨hy.2, hOwnerCarrier e hy.1⟩
    exact False.elim (hMeet hSmall)

/-- A genuine A-copy in the INDUCED first-wagon
reduct D.induce V(F_p) really belongs to wagon p:
its physical source owner cannot be some different q.

The >=2 vertices assumption comes from the actual
coloured edge type, not an invented extra girth bound. -/
theorem originalFirstWagonInducedACopy_owner
    [Nontrivial UA]
    (A : RelStructure L UA) (D : RelStructure L V)
    (oldCarrier : P → Set V)
    (owner : {e : Set V // e ∈ supportCopies A D} → P)
    (hOwnerCarrier : ∀ e, e.1 ⊆ oldCarrier (owner e))
    (hWagonLinear : ∀ p q : P, p ≠ q →
      (oldCarrier p ∩ oldCarrier q).Subsingleton)
    (p : P)
    (a : Embedding A (D.induce (oldCarrier p))) :
    let b := (RelStructure.inclusion D (oldCarrier p)).comp a
    owner (⟨copyCarrier b, ⟨b, rfl⟩⟩ :
      {e : Set V // e ∈ supportCopies A D}) = p := by
  let b := (RelStructure.inclusion D (oldCarrier p)).comp a
  let e : {e : Set V // e ∈ supportCopies A D} :=
    ⟨copyCarrier b, ⟨b, rfl⟩⟩
  have hInside : copyCarrier b ⊆ oldCarrier p := by
    rintro x ⟨u, hx⟩
    change (a u).1 = x at hx
    rw [← hx]
    exact (a u).2
  by_contra hp
  have hpq : p ≠ owner e := Ne.symm hp
  obtain ⟨u, v, huv⟩ := exists_pair_ne UA
  have hPair : b u = b v :=
    hWagonLinear p (owner e) hpq
      ⟨hInside ⟨u, rfl⟩, hOwnerCarrier e ⟨u, rfl⟩⟩
      ⟨hInside ⟨v, rfl⟩, hOwnerCarrier e ⟨v, rfl⟩⟩
  exact huv (b.injective hPair)


/-- Every actual A-support edge of the dependent W disjoint
union comes from one induced F_p and has the SAME genuine
source first-wagon owner p after forgetting the tag.

This composes the exact W support decomposition with the
previous ownership lemma. It is the missing guard against
accidentally selecting extra edges in an induced local
structure not owned by its declared first wagon. -/
theorem firstWagonUnion_supportEdge_has_correct_original_owner
    [Nontrivial UA]
    (A : RelStructure L UA) (D : RelStructure L V)
    (oldCarrier : P → Set V)
    (owner : {e : Set V // e ∈ supportCopies A D} → P)
    (hPositive : ∀ sym : L.Symbol, 0 < L.arity sym)
    (hSpan : HasSpanningRelation A)
    (hOwnerCarrier : ∀ e, e.1 ⊆ oldCarrier (owner e))
    (hWagonLinear : ∀ p q : P, p ≠ q →
      (oldCarrier p ∩ oldCarrier q).Subsingleton)
    (e : Set (FirstWagonUnionVertex oldCarrier))
    (he : e ∈ supportCopies A
      (firstWagonDisjointUnion oldCarrier
        (fun p => D.induce (oldCarrier p)))) :
    ∃ (p : P)
      (a : Embedding A (D.induce (oldCarrier p))),
      owner (⟨copyCarrier
          ((RelStructure.inclusion D (oldCarrier p)).comp a),
          ⟨(RelStructure.inclusion D (oldCarrier p)).comp a, rfl⟩⟩ :
        {e : Set V // e ∈ supportCopies A D}) = p ∧
      e = (firstWagonSummandEmbedding oldCarrier
            (fun q => D.induce (oldCarrier q))
            hPositive p).toFunctionEmbedding '' copyCarrier a := by
  obtain ⟨p, f, hf, heq⟩ :=
    (firstWagonDisjointUnion_supportCopies_iff A
      oldCarrier (fun q => D.induce (oldCarrier q))
      hPositive hSpan e).mp he
  obtain ⟨a, ha⟩ := hf
  refine ⟨p, a, ?_, ?_⟩
  · exact originalFirstWagonInducedACopy_owner
      A D oldCarrier owner hOwnerCarrier hWagonLinear p a
  · calc
      e = (firstWagonSummandEmbedding oldCarrier
            (fun q => D.induce (oldCarrier q))
            hPositive p).toFunctionEmbedding '' f := heq
      _ = (firstWagonSummandEmbedding oldCarrier
            (fun q => D.induce (oldCarrier q))
            hPositive p).toFunctionEmbedding '' copyCarrier a :=
          congrArg _ ha

end StructuralRamsey.Girth
