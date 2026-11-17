import Girth.FiniteTraceMinimalSeparator
import Mathlib.Combinatorics.SimpleGraph.Metric

/-!
# Shortest paths through a specified component

A shortest path restricted to the component and its prescribed endpoints
has no chords in the full graph. The endpoints are nonadjacent, so it has
at least one internal vertex.
-/

namespace StructuralRamsey.Girth

universe v
variable {V : Type v}

private theorem graphOnRegion_mono (G : SimpleGraph V) {R S : Set V}
    (hRS : R ⊆ S) : graphOnRegion G R ≤ graphOnRegion G S :=
  fun _ _ h => ⟨hRS h.1, hRS h.2.1, h.2.2⟩

private theorem componentIn_reachable {G : SimpleGraph V} {R : Set V}
    {a x : V} (hx : x ∈ componentIn G R a) :
    (graphOnRegion G (componentIn G R a)).Reachable a x := by
  have h := hx.2
  rw [SimpleGraph.reachable_iff_reflTransGen] at h
  induction h with
  | refl => rfl
  | @tail y z hxy hyz ih =>
    have hyR : y ∈ R := hyz.1
    have hy : y ∈ componentIn G R a :=
      ⟨hyR, (SimpleGraph.reachable_iff_reflTransGen a y).mpr hxy⟩
    have hz := mem_componentIn_of_adj hy hyz.2.1 hyz.2.2
    exact (ih hy).trans (SimpleGraph.Adj.reachable ⟨hy, hz, hyz.2.2⟩)

/-- A path from s to t with every internal vertex in C. The index has
bounds only where the value is used. -/
structure InducedPathThrough (G : SimpleGraph V) (C : Set V) (s t : V) where
  length : ℕ
  vertex : ℕ → V
  length_ge_two : 2 ≤ length
  start : vertex 0 = s
  finish : vertex length = t
  injective_on : Set.InjOn vertex {i : ℕ | i ≤ length}
  internal : ∀ i : ℕ, 0 < i → i < length → vertex i ∈ C
  adj_iff : ∀ i j : ℕ, i ≤ length → j ≤ length →
    (G.Adj (vertex i) (vertex j) ↔ i + 1 = j ∨ j + 1 = i)

private theorem shortestWalk_adj_iff {G : SimpleGraph V} {s t : V}
    {p : G.Walk s t} (hp : p.length = G.dist s t) (i j : ℕ)
    (hi : i ≤ p.length) (hj : j ≤ p.length) :
    G.Adj (p.getVert i) (p.getVert j) ↔ i + 1 = j ∨ j + 1 = i := by
  constructor
  · intro h
    have short (i j : ℕ) (hi : i ≤ p.length) (hj : j ≤ p.length)
        (hij : G.Adj (p.getVert i) (p.getVert j)) : j ≤ i + 1 := by
      have hm := G.dist_le (((p.take i).append hij.toWalk).append (p.drop j))
      rw [← hp, SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_append,
        SimpleGraph.Walk.take_length, SimpleGraph.Walk.drop_length,
        min_eq_left hi] at hm
      simp at hm
      omega
    rcases lt_trichotomy i j with hij | rfl | hji
    · exact Or.inl (by have := short i j hi hj h; omega)
    · exact (G.irrefl h).elim
    · exact Or.inr (by have := short j i hj hi h.symm; omega)
  · rintro (h | h)
    · subst j
      exact p.adj_getVert_succ (by omega)
    · subst i
      exact (p.adj_getVert_succ (by omega)).symm

theorem exists_inducedPathThrough_componentIn (G : SimpleGraph V) (R : Set V)
    {a s t : V} (hst : s ≠ t) (hNotAdj : ¬ G.Adj s t)
    (hs : ∃ x ∈ componentIn G R a, G.Adj s x)
    (ht : ∃ y ∈ componentIn G R a, G.Adj t y) :
    Nonempty (InducedPathThrough G (componentIn G R a) s t) := by
  let C := componentIn G R a
  let H := graphOnRegion G (C ∪ ({s, t} : Set V))
  obtain ⟨x, hx, hsx⟩ := hs
  obtain ⟨y, hy, hty⟩ := ht
  have hAx := componentIn_reachable hx
  have hAy := componentIn_reachable hy
  have hxy : H.Reachable x y :=
    (hAx.symm.trans hAy).mono (graphOnRegion_mono G Set.subset_union_left)
  have hS : s ∈ C ∪ ({s, t} : Set V) := Or.inr (by simp)
  have hT : t ∈ C ∪ ({s, t} : Set V) := Or.inr (by simp)
  have hSx : H.Adj s x := ⟨hS, Or.inl hx, hsx⟩
  have hYt : H.Adj y t := ⟨Or.inl hy, hT, hty.symm⟩
  obtain ⟨p, hpPath, hpLen⟩ :=
    (hSx.reachable.trans (hxy.trans hYt.reachable)).exists_path_of_dist
  have hTwo : 2 ≤ p.length := by
    by_contra h
    have hl : p.length = 0 ∨ p.length = 1 := by omega
    rcases hl with hz | ho
    · exact hst (p.getVert_zero.symm.trans (hz ▸ p.getVert_length))
    · have hStep := p.adj_getVert_succ (i := 0) (by omega)
      rw [p.getVert_zero, Nat.zero_add, ← ho, p.getVert_length] at hStep
      exact hNotAdj hStep.2.2
  have memRegion {i : ℕ} (hi : i ≤ p.length) : p.getVert i ∈ C ∪ ({s,t} : Set V) := by
    rcases lt_or_eq_of_le hi with hlt | rfl
    · exact (p.adj_getVert_succ hlt).1
    · simpa only [p.getVert_length] using hT
  refine ⟨⟨p.length, p.getVert, hTwo, p.getVert_zero, p.getVert_length,
    hpPath.getVert_injOn, ?_, ?_⟩⟩
  · intro i hi hlt
    have hiS : p.getVert i ≠ s := by
      intro h
      have := (hpPath.getVert_eq_start_iff hlt.le).mp h
      omega
    have hiT : p.getVert i ≠ t := by
      intro h
      have := (hpPath.getVert_eq_end_iff hlt.le).mp h
      omega
    rcases memRegion hlt.le with hin | he
    · exact hin
    · simp [hiS, hiT] at he
  · intro i j hi hj
    exact (show G.Adj (p.getVert i) (p.getVert j) ↔ H.Adj (p.getVert i) (p.getVert j) from
      ⟨fun h => ⟨memRegion hi, memRegion hj, h⟩, fun h => h.2.2⟩).trans
      (shortestWalk_adj_iff hpLen i j hi hj)

end StructuralRamsey.Girth
