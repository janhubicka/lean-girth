import Girth.ForestProfileElimination
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod

/-!
# Finite observable profiles of marked B-copy families

For fixed q and finite B, the complete vertex-equality/port profile of q
copies belongs to a finite palette, regardless of how many irrelevant
events occur elsewhere in the history tree.  This proves ONLY the
finite-colour interface of the proposed successor-tree argument; it does
not assert a bounded list of source presentations or a faithful geometric
evaluation.
-/

namespace StructuralRamsey.Girth

universe u v w z

/-- Formal marked vertices of q copies of one finite B. -/
abbrev MarkedCopyVertex (q : Nat) (VB : Type v) := Fin q × VB

/-- An overapproximation to observable q-copy profiles.
A profile records equality of every pair of marked vertices together
with a finite local role label for each marked vertex.  Actual profiles
satisfy equivalence and geometric constraints, but taking all Boolean
matrices already provides a finite palette. -/
abbrev ForestObservableProfile (q : Nat) (VB : Type v)
    (Role : Type u) :=
  (MarkedCopyVertex q VB → MarkedCopyVertex q VB → Bool) ×
  (MarkedCopyVertex q VB → Role)

/-- Finiteness needs only finite B and a finite role alphabet, and not
a local-finiteness hypothesis on ancestral owner closures. -/
theorem forestObservableProfile_finite
    (q : Nat) (VB : Type v) (Role : Type u)
    [Fintype VB] [Fintype Role] :
    Finite (ForestObservableProfile q VB Role) := by
  infer_instance

/-- Extract the observable equality/role profile of a family of
concrete labelled copies in a (possibly infinite) host. -/
def forestObservableProfile
    (q : Nat) {VB : Type v} {Role : Type u} {W : Type w}
    [DecidableEq W]
    (vertex : MarkedCopyVertex q VB → W)
    (role : MarkedCopyVertex q VB → Role) :
    ForestObservableProfile q VB Role :=
  (fun x y => decide (vertex x = vertex y), role)

/-- Injective host embeddings preserve the entire observable
equality/role profile.  This lemma does NOT assert that the
pointed-history evaluation is functorial under arbitrary shape maps. -/
theorem forestObservableProfile_map_injective
    (q : Nat) {VB : Type v} {Role : Type u}
    {W : Type w} {Z : Type z}
    [DecidableEq W] [DecidableEq Z]
    (vertex : MarkedCopyVertex q VB → W)
    (role : MarkedCopyVertex q VB → Role)
    (g : W → Z) (hg : Function.Injective g) :
    forestObservableProfile q (g ∘ vertex) role =
      forestObservableProfile q vertex role := by
  apply Prod.ext
  · funext x y
    change decide (g (vertex x) = g (vertex y)) =
      decide (vertex x = vertex y)
    by_cases h : vertex x = vertex y
    · have h' : g (vertex x) = g (vertex y) :=
        congrArg g h
      simp [h, h']
    · have h' : g (vertex x) ≠ g (vertex y) := by
        intro heq
        exact h (hg heq)
      simp [h, h']
  · rfl

end StructuralRamsey.Girth
