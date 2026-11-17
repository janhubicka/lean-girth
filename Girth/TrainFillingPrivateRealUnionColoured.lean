import Girth.TrainFillingPrivateRealUnionOrder
import Girth.TrainFillingPrivateRealUnionLinear
import Girth.TrainFillingColouredOrderedEdgePresentation

set_option Elab.async false

/-!
# The coloured one-edge language discharges W-union assumptions

The generic dependent disjoint-union constructor requires:
* every language relation has positive arity, because nullary
  relations otherwise make an arbitrary summand inclusion non-induced;
* the coloured edge type A has one spanning relation, because
  A-copies must lie entirely in a single first-wagon summand.

The actual coloured edge language has one k-ary edge relation,
unary colour predicates and a binary within-colour order.
For k>=2 all are positive arity. The full k-edge relation
spans the entire A vertex type ULift(Fin k).

Hence for this PARTICULAR edge type, every genuine first-wagon
component embeds as an induced A-STRONG substructure in the
constructed disjoint-union W; no hIncludeStrong premise is
needed. The other necessary conditions hBlin, hCovered and
the selected Ramsey arrow have their own independent source
obligations and are not asserted by this statement.

Candidate until exact-head Lean compilation.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v

/-- All symbols of the genuine coloured k-edge signature have
positive arity when k>=2. The one-edge symbol has arity k,
the unary predicate symbols arity one, the order relation two. -/
theorem colouredOrderedEdgeLanguage_positive_arity
    {I : Type u} (k : ℕ) (hk : 2 ≤ k) :
    ∀ sym : (colouredOrderedEdgeLanguage I k).Symbol,
      0 < (colouredOrderedEdgeLanguage I k).arity sym := by
  intro sym
  cases sym with
  | inl r =>
    cases r with
    | inl _ =>
        change 0 < k
        omega
    | inr _ =>
        change 0 < 1
        decide
  | inr _ =>
      change 0 < 2
      decide

/-- The k-ary edge relation of the true source A is witnessed
by the full enumeration ULift.up : Fin k -> ULift(Fin k),
which is both injective and surjective. This proves the
spanning relation required by the generic W union theorem. -/
theorem colouredOrderedEdgeSource_hasSpanningRelation
    {I : Type u} (k : ℕ) (sourceColour : Fin k → I) :
    HasSpanningRelation
      (colouredOrderedEdgeSource.{u,v} k sourceColour) := by
  refine ⟨.inl (.inl ()), (fun i : Fin k => ULift.up i), ?_, ?_⟩
  · change Function.Injective (fun i : Fin k => ULift.up i)
    intro i j h
    exact congrArg ULift.down h
  · intro x
    rcases x with ⟨i⟩
    exact ⟨i, rfl⟩

/-- Every concrete original F_p is A-strong in the ACTUAL
unequal first-wagon relational disjoint union W. The
hypotheses are only k>=2 and the genuine local structures. -/
theorem colouredFirstWagonSummand_aStrong
    {I : Type u} {V P : Type v}
    (k : ℕ) (hk : 2 ≤ k)
    (sourceColour : Fin k → I)
    (oldCarrier : P → Set V)
    (local : (p : P) →
      RelStructure (colouredOrderedEdgeLanguage I k)
        {x : V // x ∈ oldCarrier p})
    (p : P) :
    AStrong (colouredOrderedEdgeSource.{u,v} k sourceColour)
      (firstWagonDisjointUnion oldCarrier local)
      (copyCarrier
        (firstWagonSummandEmbedding oldCarrier local
          (colouredOrderedEdgeLanguage_positive_arity k hk) p)) :=
  firstWagonSummandEmbedding_aStrong
    (colouredOrderedEdgeSource.{u,v} k sourceColour)
      oldCarrier local
      (colouredOrderedEdgeLanguage_positive_arity k hk)
      (colouredOrderedEdgeSource_hasSpanningRelation k sourceColour) p


/-- The exact disjoint-union W required by the FIRST EHN arrow
is A-linear whenever the ORIGINAL coloured-edge structure T
is A-linear. This is not a new property of the Ramsey witness,
nor an independent hBlin assumption on an artificial W.

All F_p are actual induced restrictions of the same original D,
so A-linearity passes to them and then to their disjoint union. -/
theorem colouredFirstWagonUnion_induced_aLinear
    {I : Type u} {V P : Type v}
    (k : ℕ) (hk : 2 ≤ k)
    (sourceColour : Fin k → I)
    (D : RelStructure (colouredOrderedEdgeLanguage I k) V)
    (hD : ALinear (colouredOrderedEdgeSource.{u,v} k sourceColour) D)
    (oldCarrier : P → Set V) :
    ALinear (colouredOrderedEdgeSource.{u,v} k sourceColour)
      (firstWagonDisjointUnion oldCarrier
        (fun p => D.induce (oldCarrier p))) :=
  firstWagonDisjointUnion_induced_aLinear
    (colouredOrderedEdgeSource.{u,v} k sourceColour)
      D hD oldCarrier
      (colouredOrderedEdgeLanguage_positive_arity k hk)
      (colouredOrderedEdgeSource_hasSpanningRelation k sourceColour)

end StructuralRamsey.Girth
