import Girth.BergeFreshEdge
import Girth.ForestObservableEventBound
import Mathlib.Tactic

/-!
# Ambient bounded-path information at a marked attachment boundary

Unlike the pair-shadow, bounded Berge-path data detects even multi-edge
old connections through unmarked vertices. It exactly controls a single
fresh edge's girth, under the explicit contact hypothesis, and admits a
finite monotone record. This does not supply a train-history shape map.
-/

namespace StructuralRamsey.Girth

universe u v w

/-- An old Berge path of length strictly below the forbidden cycle cutoff
between two labelled boundary positions. -/
def markedBoundaryPath {I : Type u} {W : Type v}
    (E : Set (Set W)) (vertex : I → W) (m : ℕ) (i j : I) : Prop :=
  ∃ p : BergePath E, p.length + 1 ≤ m ∧
    p.vertex 0 = vertex i ∧ p.vertex (Fin.last p.length) = vertex j

theorem markedBoundaryPath_mono
    {I : Type u} {W : Type v} {E F : Set (Set W)}
    (hSub : E ⊆ F) (vertex : I → W) (m : ℕ) (i j : I) :
    markedBoundaryPath E vertex m i j →
      markedBoundaryPath F vertex m i j := by
  rintro ⟨p, hLen, hStart, hEnd⟩
  exact ⟨p.ofEdgeMem (fun t => hSub (p.edge_mem t)),
    hLen, hStart, hEnd⟩

/-- A short old path with both endpoints in a named boundary is equivalent
to some positive bounded-path bit between two of its labels. -/
theorem hasShortBergePath_image_iff
    {I : Type u} {W : Type v}
    (E : Set (Set W)) (vertex : I → W) (S : Set I) (m : ℕ) :
    HasShortBergePathThrough E (vertex '' S) m ↔
      ∃ i ∈ S, ∃ j ∈ S, markedBoundaryPath E vertex m i j := by
  constructor
  · rintro ⟨p, hLen, ⟨i, hi, hStart⟩, ⟨j, hj, hEnd⟩⟩
    exact ⟨i, hi, j, hj, p, hLen, hStart.symm, hEnd.symm⟩
  · rintro ⟨i, hi, j, hj, p, hLen, hStart, hEnd⟩
    exact ⟨p, hLen, ⟨i, hi, hStart.symm⟩, ⟨j, hj, hEnd.symm⟩⟩

/-- Equality of all labelled bounded-path bits decides existence of a
short connecting path inside the two corresponding boundary sets. -/
theorem hasShortBergePath_image_congr
    {I : Type u} {W : Type v} {Z : Type w}
    (E : Set (Set W)) (F : Set (Set Z))
    (f : I → W) (g : I → Z) (S : Set I) (m : ℕ)
    (hShadow : ∀ i j,
      markedBoundaryPath E f m i j ↔ markedBoundaryPath F g m i j) :
    HasShortBergePathThrough E (f '' S) m ↔
      HasShortBergePathThrough F (g '' S) m := by
  rw [hasShortBergePath_image_iff, hasShortBergePath_image_iff]
  constructor
  · rintro ⟨i, hi, j, hj, h⟩
    exact ⟨i, hi, j, hj, (hShadow i j).mp h⟩
  · rintro ⟨i, hi, j, hj, h⟩
    exact ⟨i, hi, j, hj, (hShadow i j).mpr h⟩

/-- Every endpoint of a nonempty Berge path belongs to an old edge. -/
theorem BergePath.endpoint_old_edges
    {W : Type v} {E : Set (Set W)} (p : BergePath E) :
    (∃ a ∈ E, p.vertex 0 ∈ a) ∧
      (∃ b ∈ E, p.vertex (Fin.last p.length) ∈ b) := by
  have hpPos : 1 ≤ p.length := p.hlength
  let first : Fin p.length := ⟨0, by omega⟩
  let last : Fin p.length := ⟨p.length - 1, by omega⟩
  have hStart : p.vertex 0 ∈ p.edge first := by
    simpa [first] using p.left_mem first
  have hEq : last.succ = Fin.last p.length := by
    apply Fin.ext
    dsimp [last]
    omega
  have hEnd : p.vertex (Fin.last p.length) ∈ p.edge last := by
    rw [← hEq]
    exact p.right_mem last
  exact ⟨⟨p.edge first, p.edge_mem first, hStart⟩,
    ⟨p.edge last, p.edge_mem last, hEnd⟩⟩

/-- If all old contacts of a new edge run through the named boundary,
the existence of a short old path is unchanged when the proposed edge
is replaced by that boundary. -/
theorem hasShortBergePath_contact_iff
    {I : Type u} {W : Type v}
    (E : Set (Set W)) (vertex : I → W) (S : Set I)
    (e : Set W) (m : ℕ)
    (hContact : ∀ a ∈ E, e ∩ a = (vertex '' S) ∩ a) :
    HasShortBergePathThrough E e m ↔
      HasShortBergePathThrough E (vertex '' S) m := by
  have hContactAt (x : W) (a : Set W) (ha : a ∈ E) (hx : x ∈ a) :
      x ∈ e ↔ x ∈ vertex '' S := by
    have hEquiv : x ∈ e ∩ a ↔ x ∈ (vertex '' S) ∩ a := by
      rw [hContact a ha]
    exact ⟨fun he => (hEquiv.mp ⟨he, hx⟩).1,
      fun hs => (hEquiv.mpr ⟨hs, hx⟩).1⟩
  constructor
  · rintro ⟨p, hLen, hStart, hEnd⟩
    obtain ⟨⟨a, ha, hA⟩, ⟨b, hb, hB⟩⟩ := p.endpoint_old_edges
    exact ⟨p, hLen, (hContactAt _ a ha hA).mp hStart,
      (hContactAt _ b hb hB).mp hEnd⟩
  · rintro ⟨p, hLen, hStart, hEnd⟩
    obtain ⟨⟨a, ha, hA⟩, ⟨b, hb, hB⟩⟩ := p.endpoint_old_edges
    exact ⟨p, hLen, (hContactAt _ a ha hA).mpr hStart,
      (hContactAt _ b hb hB).mpr hEnd⟩

/-- Complete contextual congruence for the girth effect of one *fresh*
edge. In particular all old paths through unmarked ambient vertices
are allowed; only their endpoints have to occur at the named boundary. -/
theorem freshEdge_girth_iff_of_sameBoundaryPathShadow
    {I : Type u} {W : Type v} {Z : Type w}
    (E : Set (Set W)) (F : Set (Set Z))
    (f : I → W) (g : I → Z) (S : Set I)
    (e : Set W) (e' : Set Z) (m : ℕ)
    (hOld : GirthGT E m) (hOld' : GirthGT F m)
    (hNew : e ∉ E) (hNew' : e' ∉ F)
    (hContact : ∀ a ∈ E, e ∩ a = (f '' S) ∩ a)
    (hContact' : ∀ b ∈ F, e' ∩ b = (g '' S) ∩ b)
    (hShadow : ∀ i j,
      markedBoundaryPath E f m i j ↔ markedBoundaryPath F g m i j) :
    GirthGT (insert e E) m ↔ GirthGT (insert e' F) m := by
  have hPath : HasShortBergePathThrough E e m ↔
      HasShortBergePathThrough F e' m :=
    (hasShortBergePath_contact_iff E f S e m hContact).trans
      ((hasShortBergePath_image_congr E F f g S m hShadow).trans
        (hasShortBergePath_contact_iff F g S e' m hContact').symm)
  rw [girthGT_insert_iff_noShortBergePath E e m hNew,
      girthGT_insert_iff_noShortBergePath F e' m hNew']
  simp only [hOld, hOld', true_and]
  exact not_congr hPath

/-- At a fixed cycle cutoff, marked bounded-path facts form a finite
monotone record even when the host has infinitely many edges. -/
noncomputable def boundaryPathRecord
    {I : Type u} {W : Type v} [Fintype I]
    (E : Set (Set W)) (vertex : I → W) (m : ℕ) :
    Finset (I × I) := by
  classical
  exact Finset.univ.filter
    (fun ij => markedBoundaryPath E vertex m ij.1 ij.2)

@[simp] theorem mem_boundaryPathRecord
    {I : Type u} {W : Type v} [Fintype I]
    (E : Set (Set W)) (vertex : I → W) (m : ℕ) (ij : I × I) :
    ij ∈ boundaryPathRecord E vertex m ↔
      markedBoundaryPath E vertex m ij.1 ij.2 := by
  classical
  simp [boundaryPathRecord]

theorem boundaryPathRecord_mono
    {I : Type u} {W : Type v} [Fintype I]
    (E F : Set (Set W)) (hSub : E ⊆ F)
    (vertex : I → W) (m : ℕ) :
    boundaryPathRecord E vertex m ⊆
      boundaryPathRecord F vertex m := by
  intro ij hij
  rw [mem_boundaryPathRecord] at hij ⊢
  exact markedBoundaryPath_mono hSub vertex m ij.1 ij.2 hij

/-- At most |I| squared strictly short-path-record-changing stages.
No claim is made that every essential train step changes this record. -/
theorem boundaryPathChanges_bound
    {I : Type u} {W : Type v} [Fintype I]
    (E : ℕ → Set (Set W)) (vertex : I → W) (m N : ℕ)
    (active : ℕ → Prop) [DecidablePred active]
    (hMono : ∀ n, n < N → E n ⊆ E (n + 1))
    (hActive : ∀ n, n < N → active n →
      boundaryPathRecord (E n) vertex m ⊂
        boundaryPathRecord (E (n + 1)) vertex m) :
    ((Finset.range N).filter active).card ≤
      Fintype.card I * Fintype.card I := by
  have h := activeRecordSteps_le
    (fun n => boundaryPathRecord (E n) vertex m) active N
    (fun n hn => boundaryPathRecord_mono _ _ (hMono n hn) vertex m) hActive
  simpa using h

end StructuralRamsey.Girth
