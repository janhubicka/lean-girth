import Girth.Forest

/-!
# Finite-trace selection: exact vertex and positive-arity tuple adapters

The large local small-trace theorem selects original cover members whose
traces dominate every NONEMPTY trace.  The elementary consequences below
are the two steps required for induced relational extraction: preservation
of vertices and of all nonnullary tuples, including repeated coordinates.

The empty-set case is stated explicitly; it selects no members.
This module does NOT assume a constructed forest or a Ramsey witness.
-/

namespace StructuralRamsey.Girth

universe v
variable {W ι : Type v}

/-- A selected subfamily of the original indexed cover dominates each
nonempty original trace on Z.  Indices are retained even if carriers agree. -/
def CoversNonemptyTraces
    (F : ι → Set W) (Z : Set W) (selected : Set ι) : Prop :=
  ∀ i : ι, (F i ∩ Z).Nonempty →
    ∃ j : ι, j ∈ selected ∧
      F i ∩ Z ⊆ F j ∩ Z

/-- On the empty vertex set the empty selected family suffices.  This
explicitly avoids any demand to cover the empty trace. -/
theorem coversNonemptyTraces_empty
    (F : ι → Set W) :
    CoversNonemptyTraces F ∅ ∅ := by
  intro i h
  obtain ⟨x, hx⟩ := h
  have hFalse : False := by
    simpa using hx.2
  exact hFalse.elim

/-- Selecting dominating nonempty traces preserves all vertices of Z
as soon as the original family covers Z. -/
theorem CoversNonemptyTraces.vertex_coverage
    {F : ι → Set W} {Z : Set W} {selected : Set ι}
    (hSelected : CoversNonemptyTraces F Z selected)
    (hCover : ∀ x : W, x ∈ Z → ∃ i : ι, x ∈ F i)
    {x : W} (hx : x ∈ Z) :
    ∃ j : ι, j ∈ selected ∧ x ∈ F j := by
  obtain ⟨i, hxi⟩ := hCover x hx
  have hTrace : (F i ∩ Z).Nonempty :=
    ⟨x, ⟨hxi, hx⟩⟩
  obtain ⟨j, hj, hSubset⟩ := hSelected i hTrace
  exact ⟨j, hj, (hSubset ⟨hxi, hx⟩).1⟩

/-- A positive-arity tuple in Z, originally lying in one cover member,
also lies in one selected member.  No injectivity of the tuple is used:
repeated coordinates are handled automatically.  The restriction n>0
is essential, since an empty tuple supplies no nonempty trace. -/
theorem CoversNonemptyTraces.tuple_coverage
    {F : ι → Set W} {Z : Set W} {selected : Set ι}
    (hSelected : CoversNonemptyTraces F Z selected)
    {n : ℕ} (hn : 0 < n) (t : Fin n → W)
    (hZ : ∀ k : Fin n, t k ∈ Z)
    (hOriginal : ∃ i : ι, ∀ k : Fin n, t k ∈ F i) :
    ∃ j : ι, j ∈ selected ∧ ∀ k : Fin n, t k ∈ F j := by
  obtain ⟨i, hi⟩ := hOriginal
  let k₀ : Fin n := ⟨0, hn⟩
  have hTrace : (F i ∩ Z).Nonempty :=
    ⟨t k₀, ⟨hi k₀, hZ k₀⟩⟩
  obtain ⟨j, hj, hSubset⟩ := hSelected i hTrace
  refine ⟨j, hj, ?_⟩
  intro k
  exact (hSubset ⟨hi k, hZ k⟩).1

end StructuralRamsey.Girth
