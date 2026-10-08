import Girth.Forest
import Mathlib.Tactic

/-!
# Finite incidence-mask certificates for the entire join-tree condition

For a family of q named pieces, a vertex x determines only the subset
of labels of the pieces containing x. The induced-occurrence graph of a
proposed join tree depends on x exclusively through that finite mask.

The set of *realised* masks is therefore a complete, finite semantic
certificate for the existence of a running-intersection join tree,
even if the ambient vertex type is infinite. Unlike a dominated-leaf
criterion, this characterises arbitrary join trees, including
non-leaf insertions and cycles in the hypergraph of B-copy carriers.

It does not supply a simultaneous free-ancestral evaluated history
nor show that successor shape maps preserve the mask profile.
-/

namespace StructuralRamsey.Girth

universe v

variable {W ι : Type v} [Fintype ι]

/-- The set of copy labels whose carriers contain the given vertex. -/
noncomputable def forestVertexMask
    (F : ι → HypergraphPiece W) (x : W) : Finset ι := by
  classical
  exact Finset.univ.filter (fun i => x ∈ (F i).carrier)

@[simp] theorem mem_forestVertexMask
    (F : ι → HypergraphPiece W) (x : W) (i : ι) :
    i ∈ forestVertexMask F x ↔ x ∈ (F i).carrier := by
  classical
  simp [forestVertexMask]

/-- A mask is genuinely attained by a vertex in the ambient host. -/
def ForestVertexMaskRealised
    (F : ι → HypergraphPiece W) (mask : Finset ι) : Prop :=
  ∃ x : W, forestVertexMask F x = mask

/-- All realised copy-incidence masks, drawn from a finite alphabet
independently of the ambient host's cardinality. -/
noncomputable def forestVertexMaskPalette
    (F : ι → HypergraphPiece W) : Finset (Finset ι) := by
  classical
  exact Finset.univ.filter (ForestVertexMaskRealised F)

@[simp] theorem mem_forestVertexMaskPalette
    (F : ι → HypergraphPiece W) (mask : Finset ι) :
    mask ∈ forestVertexMaskPalette F ↔
      ForestVertexMaskRealised F mask := by
  classical
  simp [forestVertexMaskPalette]

theorem forestVertexMaskPalette_card_le
    (F : ι → HypergraphPiece W) :
    (forestVertexMaskPalette F).card ≤ Fintype.card (Finset ι) := by
  classical
  calc
    (forestVertexMaskPalette F).card ≤
        (Finset.univ : Finset (Finset ι)).card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    _ = Fintype.card (Finset ι) := Finset.card_univ

/-- The occurrence set of any vertex is its finite incidence mask. -/
theorem forestVertex_occurrence_eq_mask
    (F : ι → HypergraphPiece W) (x : W) :
    {i : ι | x ∈ (F i).carrier} =
      (↑(forestVertexMask F x) : Set ι) := by
  ext i
  simp

/-- A graph has the full running-intersection condition precisely when
its induced graph on each *realised incidence mask* is preconnected.
There are finitely many such masks, even over an infinite host. -/
theorem forestRunning_iff_realisedMasks
    (F : ι → HypergraphPiece W) (T : SimpleGraph ι) :
    (∀ x : W,
      (T.induce {i : ι | x ∈ (F i).carrier}).Preconnected) ↔
    (∀ mask : Finset ι, ForestVertexMaskRealised F mask →
      (T.induce (↑mask : Set ι)).Preconnected) := by
  constructor
  · intro h mask hMask
    obtain ⟨x, hx⟩ := hMask
    have hRun := h x
    rw [forestVertex_occurrence_eq_mask F x, hx] at hRun
    exact hRun
  · intro h x
    rw [forestVertex_occurrence_eq_mask F x]
    exact h (forestVertexMask F x) ⟨x, rfl⟩

/-- A finite mask-based certificate for the existence of a join tree.
The tree need not itself come from any particular vertex ordering. -/
def FiniteJoinTreeMaskCertificate
    (F : ι → HypergraphPiece W) : Prop :=
  ∃ T : SimpleGraph ι, T.IsTree ∧
    ∀ mask : Finset ι, ForestVertexMaskRealised F mask →
      (T.induce (↑mask : Set ι)).Preconnected

/-- The existence of an arbitrary running-intersection join tree is
*equivalent* to the finite incidence-mask certificate. -/
theorem nonempty_joinTree_iff_finiteMasks
    (F : ι → HypergraphPiece W) :
    Nonempty (JoinTree F) ↔ FiniteJoinTreeMaskCertificate F := by
  constructor
  · rintro ⟨J⟩
    exact ⟨J.tree, J.isTree,
      (forestRunning_iff_realisedMasks F J.tree).mp J.running⟩
  · rintro ⟨T, hTree, hMasks⟩
    refine ⟨{ tree := T, isTree := hTree, running := ?_ }⟩
    exact (forestRunning_iff_realisedMasks F T).mpr hMasks

/-- If two finite indexed carrier families have exactly the same
realised incidence masks, they admit join trees simultaneously.
The ambient vertex types may be unrelated. -/
theorem nonempty_joinTree_iff_sameMaskPalette
    {Z : Type v}
    (F : ι → HypergraphPiece W)
    (G : ι → HypergraphPiece Z)
    (hMasks : forestVertexMaskPalette F = forestVertexMaskPalette G) :
    Nonempty (JoinTree F) ↔ Nonempty (JoinTree G) := by
  rw [nonempty_joinTree_iff_finiteMasks,
    nonempty_joinTree_iff_finiteMasks]
  constructor
  · rintro ⟨T, hT, hF⟩
    refine ⟨T, hT, ?_⟩
    intro mask hG
    apply hF mask
    have hm : mask ∈ forestVertexMaskPalette G := by
      exact (mem_forestVertexMaskPalette G mask).mpr hG
    rw [← hMasks] at hm
    exact (mem_forestVertexMaskPalette F mask).mp hm
  · rintro ⟨T, hT, hG⟩
    refine ⟨T, hT, ?_⟩
    intro mask hF
    apply hG mask
    have hm : mask ∈ forestVertexMaskPalette F :=
      (mem_forestVertexMaskPalette F mask).mpr hF
    rw [hMasks] at hm
    exact (mem_forestVertexMaskPalette G mask).mp hm

/-- Together with pairwise allowed intersections, the finite incidence
mask profile determines *full* foresthood, rather than only individual
attachment tests or dominated-leaf sufficiency. -/
theorem forestOfCopies_iff_sameMaskPalette
    {Z : Type v}
    (F : ι → HypergraphPiece W)
    (G : ι → HypergraphPiece Z)
    (hMasks : forestVertexMaskPalette F = forestVertexMaskPalette G)
    (hAllowed : PairwiseAllowed F ↔ PairwiseAllowed G) :
    ForestOfCopies F ↔ ForestOfCopies G := by
  unfold ForestOfCopies
  exact and_congr hAllowed
    (or_congr Iff.rfl (nonempty_joinTree_iff_sameMaskPalette F G hMasks))

end StructuralRamsey.Girth
