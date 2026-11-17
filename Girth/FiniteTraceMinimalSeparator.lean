import Girth.FiniteTraceDiracInduction
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Order.Minimal

/-!
# Minimal separators and their principal components

The graph on a region retains the ambient vertex type and isolates vertices
outside the region. Distances and reachability then have no subtype casts.
-/

namespace StructuralRamsey.Girth

universe v
variable {V : Type v}

/-- Restriction to a set of vertices, with vertices outside the set isolated. -/
def graphOnRegion (G : SimpleGraph V) (R : Set V) : SimpleGraph V where
  Adj x y := x ∈ R ∧ y ∈ R ∧ G.Adj x y
  symm := ⟨fun _ _ h => ⟨h.2.1, h.1, h.2.2.symm⟩⟩
  loopless := ⟨fun _ h => G.irrefl h.2.2⟩

/-- The part of the reachability component of a lying in R. -/
def componentIn (G : SimpleGraph V) (R : Set V) (a : V) : Set V :=
  {x | x ∈ R ∧ (graphOnRegion G R).Reachable a x}

theorem mem_componentIn_self {G : SimpleGraph V} {R : Set V} {a : V}
    (ha : a ∈ R) : a ∈ componentIn G R a :=
  ⟨ha, SimpleGraph.Reachable.rfl⟩

theorem mem_componentIn_of_adj {G : SimpleGraph V} {R : Set V} {a x y : V}
    (hx : x ∈ componentIn G R a) (hy : y ∈ R) (hxy : G.Adj x y) :
    y ∈ componentIn G R a :=
  ⟨hy, hx.2.trans (SimpleGraph.Adj.reachable ⟨hx.1, hy, hxy⟩)⟩

theorem separate_componentsIn {G : SimpleGraph V} {R : Set V} {a b : V}
    (hSep : ¬ (graphOnRegion G R).Reachable a b)
    {x y : V} (hx : x ∈ componentIn G R a) (hy : y ∈ componentIn G R b) :
    x ≠ y ∧ ¬ G.Adj x y := by
  refine ⟨?_, ?_⟩
  · rintro rfl
    exact hSep (hx.2.trans hy.2.symm)
  · intro hxy
    exact hSep ((mem_componentIn_of_adj hx hy.1 hxy).2.trans hy.2.symm)

/-- A finite subset of T separating two vertices of T that it excludes. -/
def SeparatesIn (G : SimpleGraph V) (T : Finset V) (a b : V) (S : Finset V) : Prop :=
  S ⊆ T ∧ a ∉ S ∧ b ∉ S ∧
    ¬ (graphOnRegion G ((T : Set V) \ (S : Set V))).Reachable a b

theorem exists_minimal_separatorIn (G : SimpleGraph V) (T : Finset V) {a b : V}
    (hab : a ≠ b) (hNotAdj : ¬ G.Adj a b) :
    ∃ S : Finset V, MinimalFor (SeparatesIn G T a b) Finset.card S := by
  classical
  apply exists_minimalFor_of_wellFoundedLT
  let S := (T.erase a).erase b
  refine ⟨S, Finset.Subset.trans (Finset.erase_subset _ _) (Finset.erase_subset _ _),
    by simp [S], by simp [S], ?_⟩
  have endpointOnly {x : V} (hx : x ∈ (T : Set V) \ (S : Set V)) : x = a ∨ x = b := by
    by_cases hxa : x = a
    · exact Or.inl hxa
    · right
      by_contra hxb
      exact hx.2 (Finset.mem_erase.mpr ⟨hxb, Finset.mem_erase.mpr ⟨hxa, hx.1⟩⟩)
  intro h
  rw [SimpleGraph.reachable_iff_reflTransGen] at h
  have stay {y : V} (hr : Relation.ReflTransGen
      (graphOnRegion G ((T : Set V) \ (S : Set V))).Adj a y) : a = y := by
    induction hr with
    | refl => rfl
    | tail _ he ih =>
      subst ih
      rcases endpointOnly he.2.1 with rfl | rfl
      · exact (G.irrefl he.2.2).elim
      · exact (hNotAdj he.2.2).elim
  exact hab (stay h)

/-- Every separator vertex has a neighbour in the component of either
specified endpoint. Otherwise that component stays separated even when
the vertex is restored, contradicting minimality. -/
theorem MinimalFor.neighbour_in_separator_component
    (G : SimpleGraph V) (T : Finset V) {a b : V} {S : Finset V}
    (hMin : MinimalFor (SeparatesIn G T a b) Finset.card S)
    (ha : a ∈ T) {s : V} (hs : s ∈ S) :
    ∃ x ∈ componentIn G ((T : Set V) \ (S : Set V)) a, G.Adj s x := by
  classical
  let A := componentIn G ((T : Set V) \ (S : Set V)) a
  have hSep := hMin.prop
  have hReach : (graphOnRegion G ((T : Set V) \ ((S.erase s : Finset V) : Set V))).Reachable a b := by
    by_contra h
    have hSmall : SeparatesIn G T a b (S.erase s) :=
      ⟨(Finset.erase_subset s S).trans hSep.1,
        fun h' => hSep.2.1 (Finset.mem_of_mem_erase h'),
        fun h' => hSep.2.2.1 (Finset.mem_of_mem_erase h'), h⟩
    exact (not_le_of_gt (Finset.card_erase_lt_of_mem hs)) (hMin.le hSmall)
  by_contra hNone
  rw [SimpleGraph.reachable_iff_reflTransGen] at hReach
  have stay {y : V} (hr : Relation.ReflTransGen
      (graphOnRegion G ((T : Set V) \ ((S.erase s : Finset V) : Set V))).Adj a y) : y ∈ A := by
    induction hr with
    | refl => exact mem_componentIn_self ⟨ha, hSep.2.1⟩
    | @tail x y _ hxy hx =>
      have hyNotS : y ∉ S := by
        intro hyS
        have hEq : y = s := by
          by_contra hNe
          exact hxy.2.1.2 (Finset.mem_erase.mpr ⟨hNe, hyS⟩)
        subst y
        exact hNone ⟨x, hx, hxy.2.2.symm⟩
      exact mem_componentIn_of_adj hx ⟨hxy.2.1.1, hyNotS⟩ hxy.2.2
  exact hSep.2.2.2 (stay hReach).2

theorem SeparatesIn.symm {G : SimpleGraph V} {T S : Finset V} {a b : V}
    (h : SeparatesIn G T a b S) : SeparatesIn G T b a S :=
  ⟨h.1, h.2.2.1, h.2.1, fun h' => h.2.2.2 h'.symm⟩

theorem MinimalFor.separator_symm
    {G : SimpleGraph V} {T S : Finset V} {a b : V}
    (h : MinimalFor (SeparatesIn G T a b) Finset.card S) :
    MinimalFor (SeparatesIn G T b a) Finset.card S :=
  ⟨h.prop.symm, fun _ h' hle => h.2 h'.symm hle⟩

/-- Once the separator is shown to be a clique, its two principal
components provide all data for the finite Dirac induction. -/
theorem inducedCliqueSeparation_of_minimal_separator
    (G : SimpleGraph V) (T : Finset V) {a b : V} {S : Finset V}
    (ha : a ∈ T) (hb : b ∈ T) (hSep : SeparatesIn G T a b S)
    (hClique : G.IsClique (S : Set V)) :
    Nonempty (InducedCliqueSeparation G T) := by
  classical
  let R := (T : Set V) \ (S : Set V)
  let A := componentIn G R a
  let B := componentIn G R b
  let A' := T.filter (· ∈ A)
  let B' := T.filter (· ∈ B)
  have hA {x : V} : x ∈ A' ↔ x ∈ A :=
    ⟨fun hx => (Finset.mem_filter.mp hx).2,
      fun hx => Finset.mem_filter.mpr ⟨hx.1.1, hx⟩⟩
  have hB {x : V} : x ∈ B' ↔ x ∈ B :=
    ⟨fun hx => (Finset.mem_filter.mp hx).2,
      fun hx => Finset.mem_filter.mpr ⟨hx.1.1, hx⟩⟩
  refine ⟨⟨S, A', B', hSep.1, Finset.filter_subset _ _, Finset.filter_subset _ _, hClique,
    ⟨a, hA.mpr (mem_componentIn_self ⟨ha, hSep.2.1⟩), hSep.2.1⟩,
    ⟨b, hB.mpr (mem_componentIn_self ⟨hb, hSep.2.2.1⟩), hSep.2.2.1⟩,
    fun x hx y hy => separate_componentsIn hSep.2.2.2 (hA.mp hx) (hB.mp hy), ?_, ?_⟩⟩
  · intro x hx y hy hxy
    by_cases hyS : y ∈ S
    · exact Or.inr hyS
    · exact Or.inl (hA.mpr (mem_componentIn_of_adj (hA.mp hx) ⟨hy, hyS⟩ hxy))
  · intro x hx y hy hxy
    by_cases hyS : y ∈ S
    · exact Or.inr hyS
    · exact Or.inl (hB.mpr (mem_componentIn_of_adj (hB.mp hx) ⟨hy, hyS⟩ hxy))

end StructuralRamsey.Girth
