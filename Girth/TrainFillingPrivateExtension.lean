import Girth.TrainDesignatedSubcopyLocalSupreme

set_option Elab.async false

/-!
# Private first-wagon extensions construct the scattering geometry

The old vertices of first wagon p are placed injectively in a common local
hypergraph X. A local vertex at an old position is identified with that old
vertex; every other local vertex is tagged by p. The private vertex type
contains only positions not identified with old vertices.

From LOCAL strong inducedness and pointwise coverage of the old positions
we construct the three fields of ComponentTargetGeometry at any cut whose
parent is a function of the first-wagon label. No output intersection,
output coverage, output supremeness or output girth is an input.

This constructs one expanded choice component from its local embeddings.
Choosing X, its ordered embeddings and the disjoint union over all choices
remain separate. The theorem does not assert a bound at the universal top.
-/

namespace StructuralRamsey.Girth

universe v

structure PrivateWagonInput (V P X : Type v) where
  oldCarrier : P → Set V
  coordinate : (p : P) → ({x : V // x ∈ oldCarrier p} ↪ X)
  templateEdges : Set (Set X)
  selectedEdges : P → Set {a : Set X // a ∈ templateEdges}
  selected_inside : ∀ p a, a ∈ selectedEdges p →
    a.1 ⊆ Set.range (coordinate p)
  local_strong : ∀ p (a : {a : Set X // a ∈ templateEdges}) x y,
    x ≠ y → x ∈ a.1 → y ∈ a.1 →
    x ∈ Set.range (coordinate p) → y ∈ Set.range (coordinate p) →
    a ∈ selectedEdges p
  local_cover : ∀ p (x : {x : V // x ∈ oldCarrier p}),
    ∃ a, a ∈ selectedEdges p ∧ coordinate p x ∈ a.1

namespace PrivateWagonInput

variable {V P X : Type v} (U : PrivateWagonInput V P X)

abbrev LocalEdge := {a : Set X // a ∈ U.templateEdges}
abbrev Edge := P × U.LocalEdge
abbrev PrivateVertex := {z : P × X // z.2 ∉ Set.range (U.coordinate z.1)}
abbrev Vertex := V ⊕ U.PrivateVertex

/-- Identify exactly the old local positions; all other positions are private. -/
noncomputable def place (p : P) (x : X) : U.Vertex := by
  classical
  exact if h : x ∈ Set.range (U.coordinate p) then
    Sum.inl (Classical.choose h).1
  else Sum.inr ⟨(p, x), h⟩

@[simp] theorem place_old (p : P) (x : {x : V // x ∈ U.oldCarrier p}) :
    U.place p (U.coordinate p x) = Sum.inl x.1 := by
  classical
  have h : U.coordinate p x ∈ Set.range (U.coordinate p) := ⟨x, rfl⟩
  have hChoice : Classical.choose h = x :=
    (U.coordinate p).injective (Classical.choose_spec h)
  simp only [place, dif_pos h, hChoice]

/-- A local position is old precisely when it is one of the specified old positions. -/
theorem place_eq_old_iff (p : P) (x : X) (y : V) :
    U.place p x = Sum.inl y ↔
      ∃ z : {z : V // z ∈ U.oldCarrier p}, z.1 = y ∧ U.coordinate p z = x := by
  classical
  constructor
  · intro hEq
    by_cases h : x ∈ Set.range (U.coordinate p)
    · refine ⟨Classical.choose h, ?_, Classical.choose_spec h⟩
      exact Sum.inl.inj (by simpa only [place, dif_pos h] using hEq)
    · simp only [place, dif_neg h] at hEq
      cases hEq
  · rintro ⟨z, rfl, rfl⟩
    exact U.place_old p z

/-- Private positions remember their first-wagon owner. -/
theorem place_eq_private_owner (p : P) (x : X) (z : U.PrivateVertex)
    (hEq : U.place p x = Sum.inr z) : p = z.1.1 := by
  classical
  by_cases h : x ∈ Set.range (U.coordinate p)
  · simp only [place, dif_pos h] at hEq
    cases hEq
  · have hz : (⟨(p, x), h⟩ : U.PrivateVertex) = z :=
      Sum.inr.inj (by simpa only [place, dif_neg h] using hEq)
    exact congrArg (fun w : U.PrivateVertex => w.1.1) hz

/-- Each expanded first wagon is an actual copy, not a quotient of X. -/
theorem place_injective (p : P) : Function.Injective (U.place p) := by
  classical
  intro x y hEq
  by_cases hx : x ∈ Set.range (U.coordinate p)
  · by_cases hy : y ∈ Set.range (U.coordinate p)
    · have hVal : (Classical.choose hx).1 = (Classical.choose hy).1 :=
        Sum.inl.inj (by simpa only [place, dif_pos hx, dif_pos hy] using hEq)
      exact (Classical.choose_spec hx).symm.trans
        ((congrArg (U.coordinate p) (Subtype.ext hVal)).trans
          (Classical.choose_spec hy))
    · simp only [place, dif_pos hx, dif_neg hy] at hEq
      cases hEq
  · by_cases hy : y ∈ Set.range (U.coordinate p)
    · simp only [place, dif_neg hx, dif_pos hy] at hEq
      cases hEq
    · have hPrivate : (⟨(p, x), hx⟩ : U.PrivateVertex) = ⟨(p, y), hy⟩ :=
        Sum.inr.inj (by simpa only [place, dif_neg hx, dif_neg hy] using hEq)
      exact congrArg (fun z : U.PrivateVertex => z.1.2) hPrivate

noncomputable def placement (p : P) : X ↪ U.Vertex :=
  ⟨U.place p, U.place_injective p⟩

@[simp] theorem old_mem_range (p : P) (x : V) :
    Sum.inl x ∈ Set.range (U.place p) ↔ x ∈ U.oldCarrier p := by
  constructor
  · rintro ⟨y, hy⟩
    obtain ⟨z, hz, _⟩ := (U.place_eq_old_iff p y x).mp hy
    simpa only [hz] using z.2
  · intro hx
    exact ⟨U.coordinate p ⟨x, hx⟩, U.place_old p ⟨x, hx⟩⟩

/-- Two different expanded first wagons meet only at their old shared vertices. -/
theorem shared_vertex_old (p q : P) (hpq : p ≠ q) (z : U.Vertex)
    (hp : z ∈ Set.range (U.place p)) (hq : z ∈ Set.range (U.place q)) :
    ∃ x : V, z = Sum.inl x ∧ x ∈ U.oldCarrier p ∧ x ∈ U.oldCarrier q := by
  cases z with
  | inl x => exact ⟨x, rfl, (U.old_mem_range p x).mp hp, (U.old_mem_range q x).mp hq⟩
  | inr z =>
      obtain ⟨x, hx⟩ := hp
      obtain ⟨y, hy⟩ := hq
      exact False.elim (hpq ((U.place_eq_private_owner p x z hx).trans
        (U.place_eq_private_owner q y z hy).symm))

/-- Exact intersection identity: adding private vertices creates no old or new
cross-wagon incidences. This is stronger than containment in the target. -/
theorem range_inter (p q : P) (hpq : p ≠ q) :
    Set.range (U.place p) ∩ Set.range (U.place q) =
      (Sum.inl : V → U.Vertex) '' (U.oldCarrier p ∩ U.oldCarrier q) := by
  ext z
  constructor
  · rintro ⟨hp, hq⟩
    obtain ⟨x, rfl, hxp, hxq⟩ := U.shared_vertex_old p q hpq z hp hq
    exact ⟨x, ⟨hxp, hxq⟩, rfl⟩
  · rintro ⟨x, ⟨hp, hq⟩, rfl⟩
    exact ⟨(U.old_mem_range p x).mpr hp, (U.old_mem_range q x).mpr hq⟩

/-- Every local edge is retained in every expanded first wagon. -/
noncomputable def edgeCarrier (e : U.Edge) : Set U.Vertex := U.place e.1 '' e.2.1

/-- The original target consists exactly of the chosen old local edges. -/
def targetEdges : Set U.Edge := {e | e.2 ∈ U.selectedEdges e.1}

noncomputable def data {Q : Type v} (parent : P → Q) :
    OrderOneData U.Vertex U.Edge PUnit.{v+1} Q where
  edgeCarrier := U.edgeCarrier
  copyCarrier := fun _ => Set.range (Sum.inl : V → U.Vertex)
  copyEdges := fun _ => U.targetEdges
  parent := fun e => parent e.1

/-- The target edge images really lie in the old target carrier. -/
theorem selected_carrier_old (e : U.Edge) (he : e ∈ U.targetEdges) :
    U.edgeCarrier e ⊆ Set.range (Sum.inl : V → U.Vertex) := by
  rintro z ⟨x, hx, rfl⟩
  obtain ⟨y, hy⟩ := U.selected_inside e.1 e.2 he hx
  exact ⟨y.1, by rw [← hy, U.place_old]⟩

/-- The private extension CONSTRUCTS the three scattering conditions at every
parent map constant on each first wagon. Only local target data are inputs. -/
noncomputable def componentGeometry {Q : Type v} (parent : P → Q) :
    (U.data parent).ComponentTargetGeometry PUnit.unit where
  componentEdges := Set.univ
  inter_wagon_intersections := by
    intro e _ f _ hParent z hzE hzF
    obtain ⟨x, hx, hxz⟩ := hzE
    obtain ⟨y, hy, hyz⟩ := hzF
    have hFirst : e.1 ≠ f.1 := fun h => hParent (congrArg parent h)
    obtain ⟨w, hzw, _, _⟩ := U.shared_vertex_old e.1 f.1 hFirst z
      ⟨x, hxz⟩ ⟨y, hyz⟩
    exact ⟨w, hzw.symm⟩
  strong_target := by
    intro e _ z w hne hzE hwE hzT hwT
    obtain ⟨x, hx, hxz⟩ := hzE
    obtain ⟨y, hy, hyw⟩ := hwE
    obtain ⟨a, ha⟩ := hzT
    obtain ⟨b, hb⟩ := hwT
    obtain ⟨a', _, hax⟩ := (U.place_eq_old_iff e.1 x a).mp (hxz.trans ha.symm)
    obtain ⟨b', _, hby⟩ := (U.place_eq_old_iff e.1 y b).mp (hyw.trans hb.symm)
    apply U.local_strong e.1 e.2 x y
    · intro hxy
      exact hne (hxz.symm.trans ((congrArg (U.place e.1) hxy).trans hyw))
    · exact hx
    · exact hy
    · exact ⟨a', hax⟩
    · exact ⟨b', hby⟩
  pointwise_cover := by
    intro e _ z hzE hzT
    obtain ⟨x, hx, hxz⟩ := hzE
    obtain ⟨a, ha⟩ := hzT
    obtain ⟨a', hVal, hCoord⟩ :=
      (U.place_eq_old_iff e.1 x a).mp (hxz.trans ha.symm)
    obtain ⟨f, hf, hxf⟩ := U.local_cover e.1 a'
    refine ⟨(e.1, f), hf, rfl, ?_⟩
    exact ⟨U.coordinate e.1 a', hxf, by rw [hCoord]; exact hxz⟩

end PrivateWagonInput
end StructuralRamsey.Girth
