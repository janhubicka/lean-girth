import Girth.ForestTraceLocalCompletion
import Girth.FiniteTracePairGraph

/-!
# Conformality of bounded locally tree-completable covers

This gives the direct local-to-conformal step of the small-trace
lemma.  It is proved by strong induction on a finite clique K.
The empty clique is deliberately excluded; one-point cliques are
covered by the stated cover condition and two-point cliques by
their pair edges.  At size >= 3, every deletion face has a
containing original bag by induction.  These <= |K| original
members admit an internal join-tree completion; missing-face
Helly supplies one original bag containing K.

This argument avoids choosing an inclusion-minimal uncovered
clique, giving a particularly direct Lean induction interface.
The remaining chordality / clique-tree construction is separate.
-/

namespace StructuralRamsey.Girth

universe v
variable {W ι : Type v}

/-- Pairwise occurrence of distinct vertices in some original bag. -/
def PairCliqueOn
    (F : ι → Set W) (K : Finset W) : Prop :=
  ∀ x : W, x ∈ K →
    ∀ y : W, y ∈ K → x ≠ y →
      ∃ i : ι, x ∈ F i ∧ y ∈ F i

/-- Every nonempty clique of size at most q is in one original
cover member, provided every nonempty selected family of size
at most q extends INSIDE the cover to a join tree.

The proof never invents a new cover member and does not use the
yet-unproved chordality or clique-tree conclusions. -/
theorem pairCliqueOn_contained_of_local_completion
    [Fintype ι]
    (F : ι → Set W) (q : ℕ)
    (hLocal : HasInternalJoinTreeCompletions F q)
    (K : Finset W) (hK : K.Nonempty)
    (hCover : ∀ x : W, x ∈ K → ∃ i : ι, x ∈ F i)
    (hClique : PairCliqueOn F K)
    (hBudget : K.card ≤ q) :
    ∃ i : ι, ∀ x : W, x ∈ K → x ∈ F i := by
  classical
  suffices hAll :
      ∀ T : Finset W, T.Nonempty →
        (∀ x : W, x ∈ T → ∃ i : ι, x ∈ F i) →
        PairCliqueOn F T →
        T.card ≤ q →
        ∃ i : ι, ∀ x : W, x ∈ T → x ∈ F i from
    hAll K hK hCover hClique hBudget
  intro T
  induction T using Finset.strongInductionOn with
  | H T ih =>
    intro hT hCoverT hCliqueT hBudgetT
    by_cases hOne : T.card = 1
    · obtain ⟨x, hEq⟩ := Finset.card_eq_one.mp hOne
      have hxT : x ∈ T := by simp [hEq]
      obtain ⟨i, hxi⟩ := hCoverT x hxT
      refine ⟨i, ?_⟩
      intro z hz
      have hzx : z = x := by simpa [hEq] using hz
      simpa [hzx] using hxi
    by_cases hTwo : T.card = 2
    · obtain ⟨x, y, hxy, hEq⟩ := Finset.card_eq_two.mp hTwo
      have hxT : x ∈ T := by simp [hEq]
      have hyT : y ∈ T := by simp [hEq]
      obtain ⟨i, hxi, hyi⟩ :=
        hCliqueT x hxT y hyT hxy
      refine ⟨i, ?_⟩
      intro z hz
      have hzx : z = x ∨ z = y := by simpa [hEq] using hz
      rcases hzx with hzx | hzy
      · simpa [hzx] using hxi
      · simpa [hzy] using hyi
    have hPos : 0 < T.card := Finset.card_pos.mpr hT
    have hThree : 3 ≤ T.card := by omega
    have hFaceExists :
        ∀ z : W, z ∈ T →
          ∃ i : ι,
            ∀ x : W, x ∈ T → x ≠ z → x ∈ F i := by
      intro z hz
      have hEraseNonempty : (T.erase z).Nonempty := by
        apply Finset.card_pos.mp
        rw [Finset.card_erase_of_mem hz]
        omega
      have hEraseCover :
          ∀ x : W, x ∈ T.erase z →
            ∃ i : ι, x ∈ F i := by
        intro x hx
        exact hCoverT x (Finset.mem_of_mem_erase hx)
      have hEraseClique : PairCliqueOn F (T.erase z) := by
        intro x hx y hy hxy
        exact hCliqueT x (Finset.mem_of_mem_erase hx)
          y (Finset.mem_of_mem_erase hy) hxy
      have hEraseBudget : (T.erase z).card ≤ q :=
        (Finset.card_le_card (Finset.erase_subset z T)).trans hBudgetT
      obtain ⟨i, hi⟩ :=
        ih (T.erase z) (Finset.erase_ssubset hz)
          hEraseNonempty hEraseCover hEraseClique hEraseBudget
      refine ⟨i, ?_⟩
      intro x hx hne
      exact hi x (Finset.mem_erase.mpr ⟨hne, hx⟩)
    obtain ⟨z0, hz0⟩ := hT
    obtain ⟨i0, _⟩ := hCoverT z0 hz0
    let faceBag : W → ι :=
      fun z => if hz : z ∈ T then
        Classical.choose (hFaceExists z hz)
      else i0
    have hFace :
        ∀ z : W, z ∈ T →
          ∀ x : W, x ∈ T → x ≠ z →
            x ∈ F (faceBag z) := by
      intro z hz x hx hne
      have hAtFace :=
        Classical.choose_spec (hFaceExists z hz) x hx hne
      simpa only [faceBag, dif_pos hz] using hAtFace
    exact exists_original_bag_covering_faces_of_card_ge_three
      F q hLocal T hT hThree faceBag hFace hBudgetT

end StructuralRamsey.Girth
