import Girth.ForestTraceMissingFaces
import Mathlib.Data.Finset.Card

/-!
# Internal join-tree completion and minimal missing-clique faces

This module uses FINITE SETS OF ORIGINAL INDEX LABELS.  A bounded
selected family N must extend to S containing N, and the join tree
is on the members of S themselves.  There are no invented bags.

The main lemma says that if every deletion face K \ {z} is contained
in a chosen original member and the number of chosen indices does
not exceed the permitted completion cutoff, then one original member
contains all of K.  This is the heart of the manuscript's conformality
argument for an inclusion-minimal uncovered clique of size at least
three.

We have not yet proved that a minimal uncovered clique yields all
these hypotheses, nor the chordality / clique-tree steps.  Nothing in
this module claims the final small-trace lemma.
-/

namespace StructuralRamsey.Girth

universe v
variable {W ι : Type v}

/-- Every nonempty selected family of at most q ORIGINAL members
extends, inside the indexed cover itself, to a family with a join
tree.  The empty-family convention is deliberately separate. -/
def HasInternalJoinTreeCompletions
    (F : ι → Set W) (q : ℕ) : Prop :=
  ∀ N : Finset ι, N.Nonempty → N.card ≤ q →
    ∃ S : Finset ι, N ⊆ S ∧
      Nonempty (JoinTree
        (fun j : {i : ι // i ∈ S} => setBagPiece (F j.1)))

/-- Under bounded internal completion, the selected missing faces
of K force a SINGLE ORIGINAL containing member.  The third-vertex
condition is automatic when K has at least three elements; it is
listed explicitly to keep this lemma independent of cardinal syntax.

Only one member is needed for each deletion face; repeated indices
are allowed and merely decrease the selected-family size. -/
theorem exists_original_bag_covering_missing_faces
    [Fintype ι]
    (F : ι → Set W) (q : ℕ)
    (hLocal : HasInternalJoinTreeCompletions F q)
    (K : Finset W) (hK : K.Nonempty)
    (hThird :
      ∀ x : W, x ∈ K →
        ∀ y : W, y ∈ K →
          ∃ z : W, z ∈ K ∧ z ≠ x ∧ z ≠ y)
    (faceBag : W → ι)
    (hFace :
      ∀ z : W, z ∈ K →
        ∀ x : W, x ∈ K → x ≠ z → x ∈ F (faceBag z))
    (hBudget : K.card ≤ q) :
    ∃ i : ι, ∀ x : W, x ∈ K → x ∈ F i := by
  classical
  let N : Finset ι := K.image faceBag
  have hN : N.Nonempty := by
    obtain ⟨z, hz⟩ := hK
    exact ⟨faceBag z, Finset.mem_image.mpr ⟨z, hz, rfl⟩⟩
  have hNcard : N.card ≤ q :=
    (Finset.card_image_le).trans hBudget
  obtain ⟨S, hNS, ⟨J⟩⟩ := hLocal N hN hNcard
  obtain ⟨z0, hz0⟩ := hK
  have hS0 : faceBag z0 ∈ S :=
    hNS (Finset.mem_image.mpr ⟨z0, hz0, rfl⟩)
  letI : Nonempty {i : ι // i ∈ S} := ⟨⟨faceBag z0, hS0⟩⟩
  have hS : ∀ z : W, z ∈ K → faceBag z ∈ S := by
    intro z hz
    exact hNS (Finset.mem_image.mpr ⟨z, hz, rfl⟩)
  let faceBagS : W → {i : ι // i ∈ S} :=
    fun z =>
      if hz : z ∈ K then ⟨faceBag z, hS z hz⟩
      else ⟨faceBag z0, hS0⟩
  have hFaceS :
      ∀ z : W, z ∈ (K : Set W) →
        ∀ x : W, x ∈ (K : Set W) → x ≠ z →
          x ∈ F (faceBagS z).1 := by
    intro z hz x hx hn
    have hz' : z ∈ K := hz
    have hx' : x ∈ K := hx
    simpa only [faceBagS, dif_pos hz'] using
      (hFace z hz' x hx' hn)
  have hSet : (K : Set W).Nonempty := by
    exact ⟨z0, hz0⟩
  obtain ⟨i, _hiS, hiK⟩ :=
    joinTreeCompletion_missingFaces_contains
      S J hSet hThird faceBagS hFaceS
  exact ⟨i, fun x hx => hiK hx⟩

end StructuralRamsey.Girth
