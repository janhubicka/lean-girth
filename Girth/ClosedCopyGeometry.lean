import Girth.TargetClosure
import Girth.TreeGeometry

/-! # Geometry of closed target copies

This file packages the exact combinatorial consequences used after applying
the ordered free-amalgamation theorem: pair-closed B-images are A-strong, and
target-closed pullbacks of pairwise intersections have the A-linear
intersection property.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {U V W : Type v}

/-- Pull the carrier intersection of two B-copies back to the source of the
first copy. -/
def pullbackIntersection
    {B : RelStructure L V} {D : RelStructure L W}
    (b c : Embedding B D) : Set V :=
  {x | b x ∈ copyCarrier c}

/-- If every pullback intersection of two B-copies is target-closed, then
A-linearity of the target forces the ambient B-copy family to have controlled
intersections. -/
theorem bIntersectionsControlled_of_targetClosedPullbacks
    {A : RelStructure L U} {B : RelStructure L V}
    {D : RelStructure L W}
    [Finite V]
    (hBase : ALinear A B)
    (hClosed :
      ∀ b c : Embedding B D,
        TargetClosed A B (pullbackIntersection b c)) :
    BIntersectionsControlled A B D := by
  intro b c hne
  let S : Set V := pullbackIntersection b c
  have hS : TargetClosed A B S := hClosed b c
  rcases targetClosed_classify hBase hS with
    hsub | ⟨a, ha⟩ | hall
  · left
    intro x hx y hy
    rcases hx.1 with ⟨xb, hxb⟩
    rcases hy.1 with ⟨yb, hyb⟩
    have hxbS : xb ∈ S := by
      change b xb ∈ copyCarrier c
      rw [hxb]
      exact hx.2
    have hybS : yb ∈ S := by
      change b yb ∈ copyCarrier c
      rw [hyb]
      exact hy.2
    have hxyb : xb = yb := hsub hxbS hybS
    calc
      x = b xb := hxb.symm
      _ = b yb := congrArg b hxyb
      _ = y := hyb
  · right
    refine ⟨b.comp a, ?_⟩
    apply Set.Subset.antisymm
    · intro x hx
      rcases hx.1 with ⟨u, hu⟩
      have huS : u ∈ S := by
        change b u ∈ copyCarrier c
        rw [hu]
        exact hx.2
      rw [ha] at huS
      rcases huS with ⟨v, hv⟩
      refine ⟨v, ?_⟩
      change b (a v) = x
      rw [hv, hu]
    · rintro x ⟨v, rfl⟩
      have havS : a v ∈ S := by
        rw [ha]
        exact ⟨v, rfl⟩
      constructor
      · exact ⟨a v, rfl⟩
      · exact havS
  · exfalso
    apply hne
    apply sameCopy_of_range_subset b c
    intro x
    have hxS : x ∈ S := by
      rw [hall]
      exact Set.mem_univ x
    change b x ∈ copyCarrier c at hxS
    rcases hxS with ⟨y, hy⟩
    exact ⟨y, hy.symm⟩

/-- Pair closure of every B-image is exactly the strong-inducedness conclusion
needed in the Ramsey family. -/
theorem bCopiesStrong_of_pairClosed
    {A : RelStructure L U} {B : RelStructure L V}
    {D : RelStructure L W}
    (hPair :
      ∀ b : Embedding B D,
        PairClosed A D (copyCarrier b)) :
    ∀ b : Embedding B D,
      AStrong A D (copyCarrier b) := by
  intro b
  exact (pairClosed_iff_aStrong A D (copyCarrier b)).mp (hPair b)

/-- Abstract geometry of a family of closed target copies.  This is precisely
the second conclusion of the manuscript's target-closure lemma once the
function-language closedness facts are supplied. -/
theorem closedTargetCopies_geometry
    {A : RelStructure L U} {B : RelStructure L V}
    {D : RelStructure L W}
    [Finite V]
    (hBase : ALinear A B)
    (hPair :
      ∀ b : Embedding B D,
        PairClosed A D (copyCarrier b))
    (hInter :
      ∀ b c : Embedding B D,
        TargetClosed A B (pullbackIntersection b c)) :
    BIntersectionsControlled A B D ∧
      ∀ b : Embedding B D,
        AStrong A D (copyCarrier b) := by
  exact ⟨bIntersectionsControlled_of_targetClosedPullbacks hBase hInter,
    bCopiesStrong_of_pairClosed hPair⟩

end StructuralRamsey.Girth
