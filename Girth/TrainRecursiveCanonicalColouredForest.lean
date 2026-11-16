import Girth.TrainRecursiveUniformLargerCutoff
import Girth.TrainFillingColouredOrderedEdgePresentation

set_option autoImplicit false
set_option Elab.async false

/-!
# A correctly scoped q>2 induction over genuine coloured one-edge types

The actual coloured-edge language contains a k-ary relation naming the
full hyperedge. The shorter train at cutoff two changes its full-edge
arity from the old k to |V(X)|, so a recursive forest assertion must
quantify over k BEFORE rank induction.

However an arbitrary structure in colouredOrderedEdgeLanguage I k need
not even be a k-vertex one-edge source. The paper uses the genuine
colouredOrderedEdgeSource k sourceColour, which has precisely k vertices
and one full edge. This narrower uniform assertion is sufficient for
the coloured-edge statement, and avoids making the still-open base-two
and order-conversion obligations unnecessarily strong.

The previously checked q>2 selected-forest theorem works pointwise for
every ordered edge structure. We lift it only across the real one-edge
sources and finite nonempty colour palettes. No lower witness at the
current rank, unrestricted RR_t, cutoff-two filling, or base-two
theorem is supplied here.
-/

namespace StructuralRamsey.Girth.TrainRecursiveWitness

universe u v

/-- Universal forest assertion only for actual finite ordered
k-vertex coloured ONE-EDGE structures (with their coarse unary
predicate assignment). The extra full-edge arity k varies before
the cutoff-rank induction. -/
def UniformSelectedCanonicalColouredForest
    (t : List ℕ) : Prop :=
  ∀ (I : Type u) [Finite I] [LinearOrder I]
    (k : ℕ) (hk : 2 ≤ k) (sourceColour : Fin k → I)
    (κ : Type) [Fintype κ] [Nonempty κ],
    letI : Nonempty (ULift.{v} (Fin k)) :=
      ⟨ULift.up (⟨0, Nat.lt_of_lt_of_le (by decide : 0 < 2) hk⟩ : Fin k)⟩
    UniformSelectedPartiteForest
      (colouredOrderedEdgeSource.{u, v} k sourceColour) t κ

/-- The verified fixed-source q>2 finite pass proves the genuinely
one-edge-sourced, all-arity/all-palette forest implication. It uses
ONLY lower-rank instances with a positive replication depth. -/
theorem uniformSelectedCanonicalColouredForest_largerCutoff
    (q : ℕ) (tail : List ℕ) (hq : 2 < q)
    (hLower : ∀ d : ℕ, 0 < d →
      UniformSelectedCanonicalColouredForest.{u, v}
        (List.replicate d (q - 1) ++ tail)) :
    UniformSelectedCanonicalColouredForest.{u, v} (q :: tail) := by
  intro I _ _ k hk sourceColour κ _ _
  letI : Nonempty (ULift.{v} (Fin k)) :=
    ⟨ULift.up (⟨0, Nat.lt_of_lt_of_le (by decide : 0 < 2) hk⟩ : Fin k)⟩
  exact uniformSelectedPartiteForest_largerCutoff
    (colouredOrderedEdgeSource.{u, v} k sourceColour)
    q tail hq κ
    (fun d hd => hLower d hd I k hk sourceColour κ)

/-- Recover precisely the genuine coloured ordered edge source at any
chosen arity, e.g. k=|V(X)|. The finite colour palette is independent
of k, and may encode functions on E(X) rather than its vertices. -/
theorem UniformSelectedCanonicalColouredForest.atOneEdge
    (I : Type u) [Finite I] [LinearOrder I]
    (k : ℕ) (hk : 2 ≤ k) (sourceColour : Fin k → I)
    (t : List ℕ)
    (h : UniformSelectedCanonicalColouredForest.{u, v} t)
    (κ : Type) [Fintype κ] [Nonempty κ] :
    letI : Nonempty (ULift.{v} (Fin k)) :=
      ⟨ULift.up (⟨0, Nat.lt_of_lt_of_le (by decide : 0 < 2) hk⟩ : Fin k)⟩
    UniformSelectedPartiteForest
      (colouredOrderedEdgeSource.{u, v} k sourceColour) t κ :=
  h I k hk sourceColour κ

end StructuralRamsey.Girth.TrainRecursiveWitness
