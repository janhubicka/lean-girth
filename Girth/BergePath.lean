import Girth.Berge
import Mathlib.Data.Fin.Tuple.Basic

/-! # Berge paths and closing edges

The mixed-cycle argument in the girth proof repeatedly cuts a Berge cycle at
two separator vertices.  The resulting object is a Berge path.  Appending a
fresh separator edge through the two endpoints closes that path to a Berge
cycle.  Keeping this construction separate avoids repeating finite-index
bookkeeping in the amalgamation proof.
-/

namespace StructuralRamsey.Girth

universe v
variable {W : Type v}

/-- A Berge path with `length` distinct hyperedges and `length + 1`
distinct connector vertices.  Edge `i` contains connectors `i` and
`i+1`. -/
structure BergePath (H : Set (Set W)) where
  length : ℕ
  hlength : 1 ≤ length
  edge : Fin length → Set W
  vertex : Fin (length + 1) → W
  edge_mem : ∀ i, edge i ∈ H
  edge_injective : Function.Injective edge
  vertex_injective : Function.Injective vertex
  left_mem : ∀ i, vertex i.castSucc ∈ edge i
  right_mem : ∀ i, vertex i.succ ∈ edge i

namespace BergePath

/-- Reinterpret a Berge path in any hypergraph containing all of its edges. -/
def ofEdgeMem
    {H K : Set (Set W)} (p : BergePath H)
    (h : ∀ i, p.edge i ∈ K) :
    BergePath K where
  length := p.length
  hlength := p.hlength
  edge := p.edge
  vertex := p.vertex
  edge_mem := h
  edge_injective := p.edge_injective
  vertex_injective := p.vertex_injective
  left_mem := p.left_mem
  right_mem := p.right_mem


/-- A nonempty initial segment of a Berge path is again a Berge path. -/
def initialSegment
    {H : Set (Set W)} (p : BergePath H)
    (r : ℕ) (hrpos : 0 < r) (hrle : r ≤ p.length) :
    BergePath H := by
  let castE : Fin r → Fin p.length :=
    fun i => Fin.castLE hrle i
  let castV : Fin (r + 1) → Fin (p.length + 1) :=
    fun i => Fin.castLE (Nat.add_le_add_right hrle 1) i
  refine {
    length := r
    hlength := hrpos
    edge := fun i => p.edge (castE i)
    vertex := fun i => p.vertex (castV i)
    edge_mem := fun i => p.edge_mem (castE i)
    edge_injective := p.edge_injective.comp
      (Fin.castLE_injective hrle)
    vertex_injective := p.vertex_injective.comp
      (Fin.castLE_injective (Nat.add_le_add_right hrle 1))
    left_mem := ?_
    right_mem := ?_
  }
  · intro i
    simpa [castE, castV] using p.left_mem (castE i)
  · intro i
    simpa [castE, castV] using p.right_mem (castE i)

/-- Close a Berge path by a new hyperedge through its two endpoint
connectors. -/
def close
    {H : Set (Set W)} (p : BergePath H)
    (separator : Set W) (hseparator : separator ∈ H)
    (hnew : ∀ i, p.edge i ≠ separator)
    (hstart : p.vertex 0 ∈ separator)
    (hend : p.vertex (Fin.last p.length) ∈ separator) :
    BergeCycle H := by
  let edges : Fin (p.length + 1) → Set W :=
    Fin.snoc p.edge separator
  let vertices : Fin (p.length + 1) → W :=
    Fin.snoc (fun i : Fin p.length => p.vertex i.succ) (p.vertex 0)
  have hedges : Function.Injective edges := by
    apply Fin.snoc_injective_iff.mpr
    constructor
    · exact p.edge_injective
    · rintro ⟨i, hi⟩
      exact hnew i hi
  have hvertices : Function.Injective vertices := by
    apply Fin.snoc_injective_iff.mpr
    constructor
    · intro i j hij
      apply Fin.succ_injective
      exact p.vertex_injective hij
    · rintro ⟨i, hi⟩
      have hzero : i.succ = (0 : Fin (p.length + 1)) :=
        p.vertex_injective hi
      exact Fin.succ_ne_zero i hzero
  have hp1 := p.hlength
  refine {
    length := p.length + 1
    hlength := by omega
    edge := edges
    vertex := vertices
    edge_mem := ?_
    edge_injective := hedges
    vertex_injective := hvertices
    left_mem := ?_
    right_mem := ?_
  }
  · intro i
    cases i using Fin.lastCases with
    | last =>
        simpa [edges] using hseparator
    | cast i =>
        simpa [edges] using p.edge_mem i
  · intro i
    cases i using Fin.lastCases with
    | last =>
        simpa [edges, vertices] using hstart
    | cast i =>
        simpa [edges, vertices] using p.right_mem i
  · intro i
    obtain ⟨j, rfl⟩ | rfl := i.eq_castSucc_or_eq_last
    · have hvert : vertices j.castSucc = p.vertex j.succ := by
        simp [vertices]
      rw [hvert]
      by_cases hj : j.1 + 1 < p.length
      · let jn : Fin p.length := ⟨j.1 + 1, hj⟩
        have hsucc : cyclicSucc j.castSucc = jn.castSucc := by
          apply Fin.ext
          change (j.1 + 1) % (p.length + 1) = j.1 + 1
          rw [Nat.mod_eq_of_lt (by omega)]
        rw [hsucc]
        simp only [edges, Fin.snoc_castSucc]
        have hv : j.succ = jn.castSucc := by
          apply Fin.ext
          rfl
        rw [hv]
        exact p.left_mem jn
      · have heq : j.1 + 1 = p.length := by omega
        have hsucc :
            cyclicSucc j.castSucc = Fin.last p.length := by
          apply Fin.ext
          change (j.1 + 1) % (p.length + 1) = p.length
          rw [Nat.mod_eq_of_lt (by omega), heq]
        rw [hsucc]
        simp only [edges, Fin.snoc_last]
        have hv : j.succ = Fin.last p.length := by
          apply Fin.ext
          exact heq
        rw [hv]
        exact hend
    · let z : Fin p.length := ⟨0, by omega⟩
      have hvert :
          vertices (Fin.last p.length) = p.vertex 0 := by
        simp [vertices]
      rw [hvert]
      have hsucc :
          cyclicSucc (Fin.last p.length) =
            (0 : Fin (p.length + 1)) := by
        apply Fin.ext
        simp [cyclicSucc]
      rw [hsucc]
      have hz : (0 : Fin (p.length + 1)) = z.castSucc := by
        apply Fin.ext
        rfl
      rw [hz]
      simp only [edges, Fin.snoc_castSucc]
      exact p.left_mem z

end BergePath

end StructuralRamsey.Girth
