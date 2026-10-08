import Girth.ForestMarkedSupportTransport
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic

/-!
# The finite semantic forest palette for mixed A/B support families

Unlike a uniform q-tuple of B-copies, a local forest test contains both
designated B-pieces and singleton A-support-edge pieces. These need not
have the same source vertex type, so the appropriate index is an arbitrary
finite type I of all tagged vertex positions, with an arbitrary finite type
C of named members.

For a fixed labelled carrier/support-edge presentation on I, the entire
forest predicate depends only on the finite Boolean equality kernel
I → I → Bool. In particular, different source types and different
numbers of internal edges cause no difficulty for semantic finiteness.

This theorem does NOT construct free-successor histories for those
mixed families or assert equivariance under all successor shape maps.
-/

namespace StructuralRamsey.Girth

universe u v w

/-- Finite Boolean kernel palette for the jointly marked vertex positions
of arbitrary named A/B support pieces. -/
abbrev MixedForestKernelPalette (I : Type u) := I → I → Bool

theorem mixedForestKernelPalette_finite
    (I : Type u) [Fintype I] :
    Finite (MixedForestKernelPalette I) := by
  infer_instance

/-- The equality-kernel colour of a jointly labelled family. -/
def mixedForestKernelColour {I : Type u} {W : Type v}
    [DecidableEq W] (vertex : I → W) :
    MixedForestKernelPalette I :=
  fun i j => decide (vertex i = vertex j)

/-- Equality of the finite Boolean colour is exactly the semantic
kernel hypothesis used by coherent marked-carrier transport. -/
theorem sameMarkedKernel_of_mixedColour_eq
    {I : Type u} {W : Type v} {Z : Type w}
    [DecidableEq W] [DecidableEq Z]
    (f : I → W) (g : I → Z)
    (hColour : mixedForestKernelColour f = mixedForestKernelColour g) :
    SameMarkedKernel f g := by
  intro i j
  have hc := congrFun (congrFun hColour i) j
  change decide (f i = f j) = decide (g i = g j) at hc
  constructor
  · intro hi
    by_contra hj
    simp [hi, hj] at hc
  · intro hj
    by_contra hi
    simp [hi, hj] at hc

/-- Complete finite-colour congruence for arbitrary finite mixed
families of designated B-copies and auxiliary A-edge pieces. Each
named member may have an independent size and intrinsic edge pattern,
so there is no uniform B template required. -/
theorem mixedForestKernelColour_determines_forest
    {I C W Z : Type v} [Fintype C]
    [DecidableEq W] [DecidableEq Z]
    (F : C → HypergraphPiece W)
    (G : C → HypergraphPiece Z)
    (f : I → W) (g : I → Z)
    (carriers : C → Set I) (atoms : C → Set (Set I))
    (hPresent : SameMarkedSupportPresentation F G f g carriers atoms)
    (hColour : mixedForestKernelColour f = mixedForestKernelColour g) :
    ForestOfCopies F ↔ ForestOfCopies G := by
  exact markedFamily_forest_iff_of_supportPresentation
    F G f g (sameMarkedKernel_of_mixedColour_eq f g hColour)
    carriers atoms hPresent

end StructuralRamsey.Girth
