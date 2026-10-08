import Girth.BoundaryShortPathRecord
import Mathlib.Tactic

/-!
# A finite ambient witness core for all bounded marked paths

For a finite labelled boundary, retain one old Berge path for each
positive ordered-pair path query. This gives a finite subhypergraph
with the *same* boundary path profile as the whole ambient host.

This is stronger than merely counting when path facts become true:
the chosen witnesses retain previously invisible intermediate edges.
It is a static finite-support theorem, not a successor-shape map.
-/

namespace StructuralRamsey.Girth

universe u v

/-- The edges of one chosen short path between a pair of marked
positions, or the empty family if no such path exists. -/
noncomputable def boundaryPathWitnessEdges
    {I : Type u} {W : Type v}
    (E : Set (Set W)) (vertex : I → W) (m : ℕ) (ij : I × I) :
    Finset (Set W) := by
  classical
  exact if h : MarkedShortBergePath E vertex m ij.1 ij.2 then
    (Finset.univ : Finset (Fin (Classical.choose h).length)).image
      (Classical.choose h).edge
  else ∅

/-- One chosen witness per ordered pair; no finiteness of the ambient
host is required. -/
noncomputable def boundaryPathCore
    {I : Type u} {W : Type v} [Fintype I]
    (E : Set (Set W)) (vertex : I → W) (m : ℕ) :
    Finset (Set W) := by
  classical
  exact (Finset.univ : Finset (I × I)).biUnion
    (boundaryPathWitnessEdges E vertex m)

/-- Every retained edge was already present in the original host. -/
theorem boundaryPathCore_subset
    {I : Type u} {W : Type v} [Fintype I]
    (E : Set (Set W)) (vertex : I → W) (m : ℕ) :
    (↑(boundaryPathCore E vertex m) : Set (Set W)) ⊆ E := by
  classical
  intro a ha
  change a ∈ boundaryPathCore E vertex m at ha
  simp only [boundaryPathCore, Finset.mem_biUnion] at ha
  obtain ⟨ij, _, ha⟩ := ha
  unfold boundaryPathWitnessEdges at ha
  split_ifs at ha with h
  · obtain ⟨i, _, hEq⟩ := Finset.mem_image.mp ha
    rw [← hEq]
    exact (Classical.choose h).edge_mem i
  · simpa using ha

/-- All positive marked-path facts have their entire witness
inside the finite core. -/
theorem boundaryPathCore_complete
    {I : Type u} {W : Type v} [Fintype I]
    (E : Set (Set W)) (vertex : I → W) (m : ℕ) (i j : I)
    (h : MarkedShortBergePath E vertex m i j) :
    MarkedShortBergePath
      (↑(boundaryPathCore E vertex m) : Set (Set W)) vertex m i j := by
  classical
  let p : BergePath E := Classical.choose h
  have hp : p.length < m ∧
      p.vertex 0 = vertex i ∧ p.vertex (Fin.last p.length) = vertex j :=
    Classical.choose_spec h
  have hEdges (t : Fin p.length) :
      p.edge t ∈ (boundaryPathCore E vertex m) := by
    apply Finset.mem_biUnion.mpr
    refine ⟨(i, j), Finset.mem_univ _, ?_⟩
    unfold boundaryPathWitnessEdges
    rw [dif_pos h]
    exact Finset.mem_image.mpr ⟨t, Finset.mem_univ _, rfl⟩
  exact ⟨p.ofEdgeMem (fun t => (Finset.mem_coe).mpr (hEdges t)),
    hp.1, hp.2.1, hp.2.2⟩

/-- The finite core answers every bounded-path query on the marked
boundary exactly as the entire ambient host. -/
theorem boundaryPathCore_profile_iff
    {I : Type u} {W : Type v} [Fintype I]
    (E : Set (Set W)) (vertex : I → W) (m : ℕ) (i j : I) :
    MarkedShortBergePath
      (↑(boundaryPathCore E vertex m) : Set (Set W)) vertex m i j ↔
    MarkedShortBergePath E vertex m i j := by
  constructor
  · exact markedShortBergePath_mono _ E (boundaryPathCore_subset E vertex m)
      vertex m i j
  · exact boundaryPathCore_complete E vertex m i j

/-- A witness for a positive query has fewer than m edges.
One pair therefore consumes at most m old edges. -/
theorem boundaryPathWitnessEdges_card_le
    {I : Type u} {W : Type v}
    (E : Set (Set W)) (vertex : I → W) (m : ℕ) (ij : I × I) :
    (boundaryPathWitnessEdges E vertex m ij).card ≤ m := by
  classical
  unfold boundaryPathWitnessEdges
  split_ifs with h
  · have hp := (Classical.choose_spec h).1
    calc
      (Finset.univ.image (Classical.choose h).edge).card ≤
          (Finset.univ : Finset (Fin (Classical.choose h).length)).card :=
        Finset.card_image_le
      _ = (Classical.choose h).length := by simp
      _ ≤ m := by omega
  · simp

/-- Quantitative finite support: at most |I| squared times m
old edges suffice for all short path questions. -/
theorem boundaryPathCore_card_le
    {I : Type u} {W : Type v} [Fintype I]
    (E : Set (Set W)) (vertex : I → W) (m : ℕ) :
    (boundaryPathCore E vertex m).card ≤
      (Fintype.card I * Fintype.card I) * m := by
  classical
  calc
    (boundaryPathCore E vertex m).card ≤
        ∑ ij ∈ (Finset.univ : Finset (I × I)),
          (boundaryPathWitnessEdges E vertex m ij).card := by
      exact Finset.card_biUnion_le
    _ ≤ ∑ _ij ∈ (Finset.univ : Finset (I × I)), m := by
      apply Finset.sum_le_sum
      intro ij _
      exact boundaryPathWitnessEdges_card_le E vertex m ij
    _ = (Fintype.card I * Fintype.card I) * m := by
      simp [Fintype.card_prod, mul_assoc]

/-- For a single fresh edge with all old contacts through the marked
boundary, replacing the ambient host by the finite witness core
preserves the answer to the girth test. -/
theorem freshEdge_girth_iff_finiteBoundaryCore
    {I : Type u} {W : Type v} [Fintype I]
    (E : Set (Set W)) (vertex : I → W) (S : Set I)
    (e : Set W) (m : ℕ)
    (hOld : GirthGT E m) (hNew : e ∉ E)
    (hContact : ∀ a ∈ E, e ∩ a = (vertex '' S) ∩ a) :
    GirthGT (insert e E) m ↔
      GirthGT (insert e
        (↑(boundaryPathCore E vertex m) : Set (Set W))) m := by
  let F : Set (Set W) :=
    ↑(boundaryPathCore E vertex m)
  have hSub : F ⊆ E := boundaryPathCore_subset E vertex m
  have hGirthF : GirthGT F m := girthGT_of_subset hSub hOld
  have hNewF : e ∉ F := fun he => hNew (hSub he)
  have hContactF : ∀ a ∈ F, e ∩ a = (vertex '' S) ∩ a :=
    fun a ha => hContact a (hSub ha)
  exact freshEdge_girth_iff_of_sameShortPaths
    E F vertex vertex S e e m
    hOld hGirthF hNew hNewF hContact hContactF
    (fun i j => (boundaryPathCore_profile_iff E vertex m i j).symm)

end StructuralRamsey.Girth
