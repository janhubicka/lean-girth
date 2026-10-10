import Girth.ForestRepeatedOwnerOuter
import Girth.ForestCompletionSeparatorRequests

/-!
# Direct forest increment without covered-edge pruning

A local recursive Ramsey witness need not have every ambient edge contained
in a designated local target copy.  A selected core edge not assigned to
a designated local copy can instead be its OWN one-edge outer owner.

The used outer family is then indexed by designated gluing copies and
one-edge core pieces.  It is precisely the kind of mixed family covered
by the previous-cutoff forest property.  Full standard pictures extend
the former owners; one-edge owners remain unchanged.

The key equality is that a full standard picture meets the core exactly
in its small gluing copy.  Hence it also meets any core edge exactly as
the small gluing copy does.  No normalization/pruning of the local
recursive witness, and in particular no unproved tail system-Girth
transfer, is used here.

This module verifies the mixed owner transport and repeated-owner bound;
the full concrete picture-step application still needs separate work.
-/

namespace StructuralRamsey.Girth

universe v
variable {W Q E N : Type v}

/-- Outer owners consist of regular local designated copies and one-edge
core members.  The latter are genuine labelled outer pieces, not
uncovered edges artificially assigned to a designated copy. -/
def mixedOwnerSmall
    (small : Q → HypergraphPiece W) (coreEdges : E → Set W) :
    Q ⊕ E → HypergraphPiece W
  | .inl q => small q
  | .inr e => HypergraphPiece.oneEdge (coreEdges e)

/-- On regular owners take full standard pictures, while retaining
each core one-edge owner literally unchanged. -/
def mixedOwnerFull
    (full : Q → HypergraphPiece W) (coreEdges : E → Set W) :
    Q ⊕ E → HypergraphPiece W
  | .inl q => full q
  | .inr e => HypergraphPiece.oneEdge (coreEdges e)

/-- Core intersection is unchanged on every regular-versus-edge pair:
the full standard picture has no extra core vertices. -/
theorem mixedOwner_regularEdge_overlap
    (small full : Q → HypergraphPiece W)
    (core : Set W) (coreEdges : E → Set W)
    (hRegularSub : ∀ q, (small q).carrier ⊆ (full q).carrier)
    (hFullCore : ∀ q,
      (full q).carrier ∩ core = (small q).carrier)
    (hEdgesCore : ∀ e, coreEdges e ⊆ core)
    (q : Q) (e : E) :
    (full q).carrier ∩ coreEdges e =
      (small q).carrier ∩ coreEdges e := by
  ext x
  constructor
  · intro hx
    have hcore : x ∈ (full q).carrier ∩ core :=
      ⟨hx.1, hEdgesCore e hx.2⟩
    rw [hFullCore q] at hcore
    exact ⟨hcore, hx.2⟩
  · intro hx
    exact ⟨hRegularSub q hx.1, hx.2⟩

/-- Exact pairwise intersection identity across the mixed owner sum. -/
theorem mixedOwner_pair_overlap
    (small full : Q → HypergraphPiece W)
    (core : Set W) (coreEdges : E → Set W)
    (hRegularSub : ∀ q, (small q).carrier ⊆ (full q).carrier)
    (hRegularOverlap :
      ∀ ⦃q r : Q⦄, q ≠ r →
        (full q).carrier ∩ (full r).carrier =
          (small q).carrier ∩ (small r).carrier)
    (hFullCore : ∀ q,
      (full q).carrier ∩ core = (small q).carrier)
    (hEdgesCore : ∀ e, coreEdges e ⊆ core) :
    ∀ ⦃i j : Q ⊕ E⦄, i ≠ j →
      (mixedOwnerFull full coreEdges i).carrier ∩
          (mixedOwnerFull full coreEdges j).carrier =
      (mixedOwnerSmall small coreEdges i).carrier ∩
          (mixedOwnerSmall small coreEdges j).carrier := by
  intro i j hij
  cases i with
  | inl q =>
      cases j with
      | inl r =>
          have hqr : q ≠ r := by
            intro h
            subst r
            exact hij rfl
          simpa [mixedOwnerFull, mixedOwnerSmall] using
            hRegularOverlap hqr
      | inr e =>
          simpa [mixedOwnerFull, mixedOwnerSmall] using
            mixedOwner_regularEdge_overlap small full core coreEdges
              hRegularSub hFullCore hEdgesCore q e
  | inr e =>
      cases j with
      | inl r =>
          have h := mixedOwner_regularEdge_overlap small full
            core coreEdges hRegularSub hFullCore hEdgesCore r e
          simpa [mixedOwnerFull, mixedOwnerSmall] using
            (show coreEdges e ∩ (full r).carrier =
                coreEdges e ∩ (small r).carrier from by
              calc
                coreEdges e ∩ (full r).carrier =
                    (full r).carrier ∩ coreEdges e := Set.inter_comm _ _
                _ = (small r).carrier ∩ coreEdges e := h
                _ = coreEdges e ∩ (small r).carrier := Set.inter_comm _ _)
      | inr f =>
          rfl

/-- Small-to-full carrier containment holds for both owner types. -/
theorem mixedOwner_carrier_subset
    (small full : Q → HypergraphPiece W) (coreEdges : E → Set W)
    (hSub : ∀ q, (small q).carrier ⊆ (full q).carrier) :
    ∀ i : Q ⊕ E,
      (mixedOwnerSmall small coreEdges i).carrier ⊆
        (mixedOwnerFull full coreEdges i).carrier := by
  intro i
  cases i with
  | inl q => exact hSub q
  | inr e => exact Set.Subset.rfl

/-- The old small support edges remain in the full standard pictures;
exceptional core edges are unchanged. -/
theorem mixedOwner_edges_subset
    (small full : Q → HypergraphPiece W) (coreEdges : E → Set W)
    (hSub : ∀ q, (small q).edges ⊆ (full q).edges) :
    ∀ i : Q ⊕ E,
      (mixedOwnerSmall small coreEdges i).edges ⊆
        (mixedOwnerFull full coreEdges i).edges := by
  intro i
  cases i with
  | inl q => exact hSub q
  | inr e => exact Set.Subset.rfl

/-- A repeated owner map uses at most q-1 DISTINCT mixed owners.
Their small pieces are a local forest by the preceding cutoff and the
full pieces form a forest by exact overlap transport.

This branch does not require that all ambient core edges be covered
by local designated gluing copies. -/
theorem mixedFullStandardForest_repeatedOwners
    [Fintype N]
    (owner : N → Q ⊕ E)
    (small full : Q → HypergraphPiece W)
    (core : Set W) (coreEdges : E → Set W)
    (q : ℕ) (hCount : Fintype.card N ≤ q)
    (hNoninjective : ¬ Function.Injective owner)
    (hPrevious : LocalForestThrough
      (mixedOwnerSmall small coreEdges) (q - 1))
    (hRegularSub : ∀ x, (small x).carrier ⊆ (full x).carrier)
    (hRegularEdges : ∀ x, (small x).edges ⊆ (full x).edges)
    (hRegularOverlap :
      ∀ ⦃x y : Q⦄, x ≠ y →
        (full x).carrier ∩ (full y).carrier =
          (small x).carrier ∩ (small y).carrier)
    (hFullCore : ∀ x,
      (full x).carrier ∩ core = (small x).carrier)
    (hEdgesCore : ∀ e, coreEdges e ⊆ core) :
    ForestOfCopies
      (fun i : UsedOwner owner => mixedOwnerFull full coreEdges i.1) := by
  exact fullStandardForest_repeatedOwners
    owner (mixedOwnerSmall small coreEdges)
    (mixedOwnerFull full coreEdges) q
    hCount hNoninjective hPrevious
    (mixedOwner_carrier_subset small full coreEdges hRegularSub)
    (mixedOwner_edges_subset small full coreEdges hRegularEdges)
    (mixedOwner_pair_overlap small full core coreEdges
      hRegularSub hRegularOverlap hFullCore hEdgesCore)

end StructuralRamsey.Girth
