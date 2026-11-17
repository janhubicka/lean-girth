import Girth.TrainFillingPrivateCompletedWSupport

set_option Elab.async false

/-!
# Marked A₁ edge intersections in the COMPLETED ordered W

The paper's first train parameter A₁ says that two distinct
original small coloured edges inside ONE first wagon can
only share vertices in predicates indexed by A₁.

The completed W contains all first wagons as tagged
induced substructures, with no cross-summand hyperedges.
Consequently its entire genuine small-A support satisfies
the SAME restriction: edges in different summands are
disjoint, while edges in the same summand inherit it.

Equivalently, every W vertex in a forbidden predicate
(outside A₁) lies in at most one A-support edge.
This is the exact source-side hypothesis of Track 1's
marked owner-split construction.

These input properties do not automatically yield a covered
ordered X-output. The selected-owner conversion and the
Ramsey-arrow transfer remain separate Track 1 obligations.

Candidate Lean source, no kernel verification yet.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v
variable {I : Type u} {V P : Type v}
variable [LinearOrder I] [LinearOrder V] [LinearOrder P]

/-- If each first wagon's own small A-support has the
prescribed allowed-predicate intersection property,
the COMPLETE ordered union W has it too. No assumption
about an EHN output or its edge intersection pattern. -/
theorem completedFirstWagon_support_inter_allowed
    (k : ℕ) (hk : 2 ≤ k)
    (profile : Fin k → I)
    (oldEdges : Set (Set V)) (colour : V → I)
    (carrier : P → Set V) (allowed : Set I)
    (hLocal : ∀ p : P,
      ∀ e f : Set {x : V // x ∈ carrier p},
        e ∈ supportCopies (colouredOrderedEdgeSource.{u,v} k profile)
          ((colouredOrderedEdgeTarget k oldEdges colour).induce
            (carrier p)) →
        f ∈ supportCopies (colouredOrderedEdgeSource.{u,v} k profile)
          ((colouredOrderedEdgeTarget k oldEdges colour).induce
            (carrier p)) →
        e ≠ f →
        e ∩ f ⊆ {x | colour x.1 ∈ allowed}) :
    ∀ e f : Set (FirstWagonUnionVertex carrier),
      e ∈ supportCopies (colouredOrderedEdgeSource.{u,v} k profile)
        (completedFirstWagonColouredUnion
          k oldEdges colour carrier) →
      f ∈ supportCopies (colouredOrderedEdgeSource.{u,v} k profile)
        (completedFirstWagonColouredUnion
          k oldEdges colour carrier) →
      e ≠ f →
      e ∩ f ⊆ {z | colour z.2.1 ∈ allowed} := by
  intro e f he hf hne
  obtain ⟨p, ep, hep, heq⟩ :=
    (completedFirstWagon_supportCopies_iff
      k hk profile oldEdges colour carrier e).mp he
  obtain ⟨q, fq, hfq, hfqeq⟩ :=
    (completedFirstWagon_supportCopies_iff
      k hk profile oldEdges colour carrier f).mp hf
  by_cases hpq : p = q
  · subst q
    let inc := completedFirstWagonSummandEmbedding
      k hk oldEdges colour carrier p
    have hLocalNe : ep ≠ fq := by
      intro hEq
      apply hne
      calc
        e = inc.toFunctionEmbedding '' ep := heq
        _ = inc.toFunctionEmbedding '' fq := by rw [hEq]
        _ = f := hfqeq.symm
    intro z hz
    rw [heq, hfqeq] at hz
    obtain ⟨x, hx, hxz⟩ := hz.1
    obtain ⟨y, hy, hyz⟩ := hz.2
    have hxy : x = y :=
      inc.injective (hxz.trans hyz.symm)
    subst y
    have hAllowed : colour x.1 ∈ allowed :=
      hLocal p ep fq hep hfq hLocalNe ⟨hx, hy⟩
    rw [← hxz]
    exact hAllowed
  · intro z hz
    rw [heq, hfqeq] at hz
    obtain ⟨x, _hx, hxz⟩ := hz.1
    obtain ⟨y, _hy, hyz⟩ := hz.2
    have hSame : p = q :=
      congrArg Sigma.fst (hxz.trans hyz.symm)
    exact False.elim (hpq hSame)

/-- The marking condition in its actual OWNER-SPLIT form:
a vertex outside allowed predicates belongs to at most
one distinct coloured small A-support edge of completed W.

This is derived from the original per-wagon intersection
condition, not supplied as an independent hypothesis
of the desired EHN witness. -/
theorem completedFirstWagon_forbidden_vertex_unique_edge
    (k : ℕ) (hk : 2 ≤ k)
    (profile : Fin k → I)
    (oldEdges : Set (Set V)) (colour : V → I)
    (carrier : P → Set V) (allowed : Set I)
    (hLocal : ∀ p : P,
      ∀ e f : Set {x : V // x ∈ carrier p},
        e ∈ supportCopies (colouredOrderedEdgeSource.{u,v} k profile)
          ((colouredOrderedEdgeTarget k oldEdges colour).induce
            (carrier p)) →
        f ∈ supportCopies (colouredOrderedEdgeSource.{u,v} k profile)
          ((colouredOrderedEdgeTarget k oldEdges colour).induce
            (carrier p)) →
        e ≠ f →
        e ∩ f ⊆ {x | colour x.1 ∈ allowed})
    (z : FirstWagonUnionVertex carrier)
    (hz : colour z.2.1 ∉ allowed)
    (e f : Set (FirstWagonUnionVertex carrier))
    (he : e ∈ supportCopies (colouredOrderedEdgeSource.{u,v} k profile)
      (completedFirstWagonColouredUnion k oldEdges colour carrier))
    (hf : f ∈ supportCopies (colouredOrderedEdgeSource.{u,v} k profile)
      (completedFirstWagonColouredUnion k oldEdges colour carrier))
    (hze : z ∈ e) (hzf : z ∈ f) :
    e = f := by
  by_contra hne
  have hAllowed :=
    completedFirstWagon_support_inter_allowed
      k hk profile oldEdges colour carrier allowed hLocal
      e f he hf hne ⟨hze, hzf⟩
  exact hz hAllowed

end StructuralRamsey.Girth
