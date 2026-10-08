import Girth.ForestMarkedTransport
import Girth.ForestReplayObstruction
import Girth.ForestObservableEventBound
import Mathlib.Tactic

/-!
# The boundary information needed for fresh support-edge attachments

The marked equality profile alone does not say whether an unmarked ambient
support edge already contains a given pair of marked vertices. That information
is exactly what decides linearity when adding a genuinely fresh edge.

This file proves the exact one-edge extension criterion, its invariance under
boundary-shadow equivalence, and monotonicity of the finite shadow record.
It does not assert pairwise B-cleanliness, arbitrary-girth preservation, or a
successor-tree lifting theorem.
-/

namespace StructuralRamsey.Girth

universe u v w

/-- No ambient edge contains two distinct vertices of the attachment boundary. -/
def BoundaryPairFree {W : Type v} (E : Set (Set W)) (S : Set W) : Prop :=
  ∀ e ∈ E, (S ∩ e).Subsingleton

/-- Adding an edge whose overlap with every old edge is subsingleton preserves
linearity. Freshness is unnecessary for this sufficient direction. -/
theorem linearEdgeSet_insert_of_boundaryPairFree
    {W : Type v} {E : Set (Set W)} {e : Set W}
    (hOld : LinearEdgeSet E) (hCross : BoundaryPairFree E e) :
    LinearEdgeSet (insert e E) := by
  intro a b ha hb hab
  rcases Set.mem_insert_iff.mp ha with rfl | ha
  · rcases Set.mem_insert_iff.mp hb with rfl | hb
    · exact False.elim (hab rfl)
    · exact hCross b hb
  · rcases Set.mem_insert_iff.mp hb with rfl | hb
    · simpa only [Set.inter_comm] using hCross a ha
    · exact hOld ha hb hab

/-- For a genuinely new edge, the boundary criterion is also necessary. -/
theorem linearEdgeSet_insert_iff
    {W : Type v} (E : Set (Set W)) (e : Set W) (hNew : e ∉ E) :
    LinearEdgeSet (insert e E) ↔ LinearEdgeSet E ∧ BoundaryPairFree E e := by
  constructor
  · intro h
    constructor
    · intro a b ha hb hab
      exact h (Set.mem_insert_of_mem e ha) (Set.mem_insert_of_mem e hb) hab
    · intro a ha
      have hea : e ≠ a := by
        intro heq
        exact hNew (heq.symm ▸ ha)
      exact h (Set.mem_insert e E) (Set.mem_insert_of_mem e ha) hea
  · rintro ⟨hOld, hCross⟩
    exact linearEdgeSet_insert_of_boundaryPairFree hOld hCross

/-- The ambient pair-shadow seen on retained vertex positions. Unlike their
own equality profile, this can change when an unmarked edge is added. -/
def markedBoundaryShadow {I : Type u} {W : Type v}
    (E : Set (Set W)) (vertex : I → W) (i j : I) : Prop :=
  vertex i ≠ vertex j ∧ ∃ e ∈ E, vertex i ∈ e ∧ vertex j ∈ e

theorem boundaryPairFree_image_iff {I : Type u} {W : Type v}
    (E : Set (Set W)) (vertex : I → W) (S : Set I) :
    BoundaryPairFree E (vertex '' S) ↔
      ∀ i ∈ S, ∀ j ∈ S, ¬ markedBoundaryShadow E vertex i j := by
  classical
  constructor
  · intro h i hi j hj hij
    obtain ⟨hne, e, he, hie, hje⟩ := hij
    exact hne (h e he ⟨⟨i, hi, rfl⟩, hie⟩ ⟨⟨j, hj, rfl⟩, hje⟩)
  · intro h e he x hx y hy
    rcases hx with ⟨⟨i, hi, rfl⟩, hie⟩
    rcases hy with ⟨⟨j, hj, rfl⟩, hje⟩
    by_contra hne
    exact h i hi j hj ⟨hne, e, he, hie, hje⟩

/-- The same pair-shadow gives the same legal labelled attachment boundaries. -/
theorem boundaryPairFree_iff_of_sameShadow
    {I : Type u} {W : Type v} {Z : Type w}
    (E : Set (Set W)) (E' : Set (Set Z))
    (f : I → W) (g : I → Z)
    (hShadow : ∀ i j, markedBoundaryShadow E f i j ↔ markedBoundaryShadow E' g i j)
    (S : Set I) :
    BoundaryPairFree E (f '' S) ↔ BoundaryPairFree E' (g '' S) := by
  rw [boundaryPairFree_image_iff, boundaryPairFree_image_iff]
  constructor
  · intro h i hi j hj hij
    exact h i hi j hj ((hShadow i j).mpr hij)
  · intro h i hi j hj hij
    exact h i hi j hj ((hShadow i j).mp hij)

/-- Exact extension congruence for fresh edges. The contact equalities mean
that all intersections with old material take place at the named boundary.
They are not assumptions that the new extensions are already linear. -/
theorem freshEdge_linearity_iff_of_sameBoundaryShadow
    {I : Type u} {W : Type v} {Z : Type w}
    (E : Set (Set W)) (E' : Set (Set Z))
    (f : I → W) (g : I → Z) (S : Set I)
    (e : Set W) (e' : Set Z)
    (hOld : LinearEdgeSet E) (hOld' : LinearEdgeSet E')
    (hNew : e ∉ E) (hNew' : e' ∉ E')
    (hContact : ∀ a ∈ E, e ∩ a = (f '' S) ∩ a)
    (hContact' : ∀ a ∈ E', e' ∩ a = (g '' S) ∩ a)
    (hShadow : ∀ i j, markedBoundaryShadow E f i j ↔ markedBoundaryShadow E' g i j) :
    LinearEdgeSet (insert e E) ↔ LinearEdgeSet (insert e' E') := by
  have hBoundary : BoundaryPairFree E e ↔ BoundaryPairFree E (f '' S) := by
    constructor <;> intro h a ha
    · rw [← hContact a ha]
      exact h a ha
    · rw [hContact a ha]
      exact h a ha
  have hBoundary' : BoundaryPairFree E' e' ↔ BoundaryPairFree E' (g '' S) := by
    constructor <;> intro h a ha
    · rw [← hContact' a ha]
      exact h a ha
    · rw [hContact' a ha]
      exact h a ha
  rw [linearEdgeSet_insert_iff E e hNew,
    linearEdgeSet_insert_iff E' e' hNew']
  simp only [hOld, hOld', true_and]
  exact hBoundary.trans
    ((boundaryPairFree_iff_of_sameShadow E E' f g hShadow S).trans hBoundary'.symm)

/-- Marking all ambient pair contacts still uses a finite alphabet. -/
noncomputable def boundaryShadowRecord {I : Type u} {W : Type v} [Fintype I]
    (E : Set (Set W)) (vertex : I → W) : Finset (I × I) := by
  classical
  exact Finset.univ.filter (fun ij => markedBoundaryShadow E vertex ij.1 ij.2)

@[simp] theorem mem_boundaryShadowRecord {I : Type u} {W : Type v} [Fintype I]
    (E : Set (Set W)) (vertex : I → W) (ij : I × I) :
    ij ∈ boundaryShadowRecord E vertex ↔ markedBoundaryShadow E vertex ij.1 ij.2 := by
  classical
  simp [boundaryShadowRecord]

theorem boundaryShadowRecord_mono {I : Type u} {W : Type v} [Fintype I]
    (E E' : Set (Set W)) (hSub : E ⊆ E') (vertex : I → W) :
    boundaryShadowRecord E vertex ⊆ boundaryShadowRecord E' vertex := by
  intro ij hij
  rw [mem_boundaryShadowRecord] at hij ⊢
  obtain ⟨hne, e, he, hi, hj⟩ := hij
  exact ⟨hne, e, hSub he, hi, hj⟩

/-- Unlike equality records, these events include changes caused by external
edges. The bound applies to a nested support process on fixed marked vertices;
it does not silently impose that hypothesis on every train genealogy. -/
theorem boundaryShadowChanges_bound {I : Type u} {W : Type v} [Fintype I]
    (E : ℕ → Set (Set W)) (vertex : I → W) (N : ℕ)
    (active : ℕ → Prop) [DecidablePred active]
    (hMono : ∀ n, n < N → E n ⊆ E (n + 1))
    (hActive : ∀ n, n < N → active n →
      boundaryShadowRecord (E n) vertex ⊂ boundaryShadowRecord (E (n + 1)) vertex) :
    ((Finset.range N).filter active).card ≤ Fintype.card I * Fintype.card I := by
  have h := activeRecordSteps_le
    (fun n => boundaryShadowRecord (E n) vertex) active N
    (fun n hn => boundaryShadowRecord_mono _ _ (hMono n hn) vertex) hActive
  simpa using h

end StructuralRamsey.Girth
