import Girth.TrainIncidenceData
import Girth.TrainCycleWeights
import Girth.LabelledBergeCore
import Mathlib.Tactic

/-!
# Weighted contact graphs for the 26 November manuscript

The old incidence record OrderOneData is reused, but no acceptable-cycle,
supreme-copy or replacement-word theorem is imported.  Vertex, wagon,
edge and designated-copy labels remain separate.

The actual invariant is G1--G4 of regular-tree-girth/paper/10-cycle-conditions.tex.
Weights are doubled.  The abstract shared-chord condition is also stated;
its equivalence with G4 still requires the polygon splitting proof.
-/

namespace StructuralRamsey.Girth

universe v
variable {V E I P J : Type v}

/-- The old connector-kind arithmetic is independent of cycle words. -/
def contactKind : V ⊕ P → CycleConnectorKind
  | .inl _ => .vertex
  | .inr _ => .wagon

/-- Twice the weight on a contact edge. On the diagonal this is not a
metric, so use contactDistance for the metric extension. -/
def contactWeight (x y : V ⊕ P) : ℕ :=
  twiceOccurrenceWeight (contactKind x) (contactKind y)

theorem contactWeight_triangle (x y z : V ⊕ P) :
    contactWeight x z ≤ contactWeight x y + contactWeight y z :=
  twiceOccurrenceWeight_join_le _ _ _

theorem contactWeight_positive (x y : V ⊕ P) :
    1 ≤ contactWeight x y :=
  twiceOccurrenceWeight_one_le _ _

theorem contactWeight_le_two (x y : V ⊕ P) :
    contactWeight x y ≤ 2 :=
  twiceOccurrenceWeight_le_two _ _

/-- The genuine metric extension, with zero on the diagonal. -/
noncomputable def contactDistance (x y : V ⊕ P) : ℕ := by
  classical
  exact if x = y then 0 else contactWeight x y

theorem contactDistance_triangle (x y z : V ⊕ P) :
    contactDistance x z ≤ contactDistance x y + contactDistance y z := by
  classical
  by_cases hxy : x = y
  · subst y
    simp [contactDistance]
  by_cases hyz : y = z
  · subst z
    simp [contactDistance]
  by_cases hxz : x = z
  · simp [contactDistance, hxz]
  · simpa [contactDistance, hxy, hyz, hxz] using
      (contactWeight_triangle x y z)

/-- Subdivision of a vertex--vertex side through a wagon preserves weight. -/
theorem contactWeight_subdivide (x y : V) (p : P) :
    contactWeight (Sum.inl x : V ⊕ P) (Sum.inl y) =
      contactWeight (Sum.inl x) (Sum.inr p) +
      contactWeight (Sum.inr p) (Sum.inl y) := by
  rfl

/-- The two-section adjacency, without quotienting repeated clique labels. -/
def contactAdjacent (K : J → Set (V ⊕ P)) (x y : V ⊕ P) : Prop :=
  x ≠ y ∧ ∃ j, x ∈ K j ∧ y ∈ K j

/-- An injectively indexed simple polygon. Actual sides are a separate
predicate, so the same polygon can be compared in different graphs. -/
structure ContactPolygon (V P : Type v) where
  length : ℕ
  hlength : 3 ≤ length
  vertex : Fin length → V ⊕ P
  vertex_injective : Function.Injective vertex

namespace ContactPolygon

variable (C : ContactPolygon V P)

def IsCycle (K : J → Set (V ⊕ P)) : Prop :=
  ∀ i, contactAdjacent K (C.vertex i) (C.vertex (cyclicSucc i))

def twiceWeight : ℕ :=
  ∑ i : Fin C.length, contactWeight (C.vertex i) (C.vertex (cyclicSucc i))

def Nonconsecutive (i j : Fin C.length) : Prop :=
  i ≠ j ∧ cyclicSucc i ≠ j ∧ cyclicSucc j ≠ i

def Covered (K : J → Set (V ⊕ P)) : Prop :=
  ∃ k, ∀ i, C.vertex i ∈ K k

def HasChord (K : J → Set (V ⊕ P)) : Prop :=
  ∃ i j, C.Nonconsecutive i j ∧ contactAdjacent K (C.vertex i) (C.vertex j)

def HasSharedChord (K : J → Set (V ⊕ P)) : Prop :=
  ∃ i j, C.Nonconsecutive i j ∧
    ∃ a b, a ≠ b ∧
      C.vertex i ∈ K a ∧ C.vertex j ∈ K a ∧
      C.vertex i ∈ K b ∧ C.vertex j ∈ K b

end ContactPolygon

/-- Exactly the weighted chordality and covered-triangle clauses of G4. -/
def ContactG4 (K : J → Set (V ⊕ P)) (q : ℕ) : Prop :=
  ∀ C : ContactPolygon V P, C.IsCycle K → C.twiceWeight ≤ 2 * q →
    (C.length = 3 → C.Covered K) ∧
    (4 ≤ C.length → C.HasChord K)

/-- The alternative in the manuscript's shared-chord observation.
Equivalence with ContactG4 is not assumed in ContactSystemGirthGT. -/
def ContactSharedChordBound (K : J → Set (V ⊕ P)) (q : ℕ) : Prop :=
  ∀ C : ContactPolygon V P, C.IsCycle K → C.twiceWeight ≤ 2 * q →
    C.Covered K ∨ C.HasSharedChord K

namespace OrderOneData

variable (D : OrderOneData V E I P)

def contactWagonCarrier (p : P) : Set V :=
  {x | ∃ e, D.parent e = p ∧ x ∈ D.edgeCarrier e}

def contactMeets (i : I) (p : P) : Prop :=
  ∃ e, e ∈ D.copyEdges i ∧ D.parent e = p

def contactCopyClique (i : I) : Set (V ⊕ P) :=
  {z | match z with
    | .inl x => x ∈ D.copyCarrier i
    | .inr p => D.contactMeets i p}

def contactWagonClique (p : P) : Set (V ⊕ P) :=
  {z | match z with
    | .inl x => x ∈ D.contactWagonCarrier p
    | .inr q => q = p}

def contactClique : I ⊕ P → Set (V ⊕ P)
  | .inl i => D.contactCopyClique i
  | .inr p => D.contactWagonClique p

def ContactLinear : Prop :=
  (∀ e f : E, e ≠ f → (D.edgeCarrier e ∩ D.edgeCarrier f).Subsingleton) ∧
  (∀ p q : P, p ≠ q →
    (D.contactWagonCarrier p ∩ D.contactWagonCarrier q).Subsingleton)

/-- Well-formed subcopies, strong inducedness and the incidence
requirement of G1. The first field is part of being a subhypergraph. -/
structure ContactG1 : Prop where
  edge_subset : ∀ i e, e ∈ D.copyEdges i → D.edgeCarrier e ⊆ D.copyCarrier i
  strong : ∀ i e, (D.edgeCarrier e ∩ D.copyCarrier i).Nontrivial →
    e ∈ D.copyEdges i
  bridge : ∀ i p,
    (D.contactMeets i p ∨
      (D.copyCarrier i ∩ D.contactWagonCarrier p).Nontrivial) →
    ∀ x, x ∈ D.copyCarrier i → x ∈ D.contactWagonCarrier p →
      ∃ e, e ∈ D.copyEdges i ∧ D.parent e = p ∧ x ∈ D.edgeCarrier e

def ContactG2 : Prop :=
  ∀ i j : I, i ≠ j →
    (D.contactCopyClique i ∩ D.contactCopyClique j).Nontrivial →
    ∃ p, D.contactCopyClique i ∩ D.contactCopyClique j ⊆ D.contactWagonClique p

/-- The new invariant. In particular, G3 is the labelled, not the
unlabelled, wagon girth. G4 is not replaced by a stronger oracle. -/
structure ContactSystemGirthGT (q : ℕ) : Prop where
  linear : D.ContactLinear
  g1 : D.ContactG1
  g2 : D.ContactG2
  g3 : LabelledGirthGT D.contactWagonCarrier q
  g4 : ContactG4 D.contactClique q

theorem contactSystemGirthGT_mono {q r : ℕ}
    (h : D.ContactSystemGirthGT q) (hr : r ≤ q) :
    D.ContactSystemGirthGT r := by
  refine ⟨h.linear, h.g1, h.g2, ?_, ?_⟩
  · rintro ⟨c, hc⟩
    exact h.g3 ⟨c, hc.trans hr⟩
  · intro C hCycle hWeight
    apply h.g4 C hCycle
    omega

/-- G2 also controls intersections of arbitrary generating cliques. -/
theorem contact_shared_pair_in_wagon (h : D.ContactG2)
    {a b : I ⊕ P} (hab : a ≠ b)
    {x y : V ⊕ P} (hxy : x ≠ y)
    (hxa : x ∈ D.contactClique a) (hya : y ∈ D.contactClique a)
    (hxb : x ∈ D.contactClique b) (hyb : y ∈ D.contactClique b) :
    ∃ p, x ∈ D.contactWagonClique p ∧ y ∈ D.contactWagonClique p := by
  cases a with
  | inr p => exact ⟨p, hxa, hya⟩
  | inl i =>
    cases b with
    | inr p => exact ⟨p, hxb, hyb⟩
    | inl j =>
      have hij : i ≠ j := by
        intro he
        subst j
        exact hab rfl
      obtain ⟨p, hp⟩ := h i j hij
        ⟨x, ⟨hxa, hxb⟩, y, ⟨hya, hyb⟩, hxy⟩
      exact ⟨p, hp ⟨hxa, hxb⟩, hp ⟨hya, hyb⟩⟩

/-- A shared pair determines its wagon uniquely. -/
theorem contact_wagon_unique_of_pair (h : D.ContactLinear)
    {p q : P} {x y : V ⊕ P} (hxy : x ≠ y)
    (hxp : x ∈ D.contactWagonClique p) (hyp : y ∈ D.contactWagonClique p)
    (hxq : x ∈ D.contactWagonClique q) (hyq : y ∈ D.contactWagonClique q) :
    p = q := by
  cases x with
  | inr a =>
    exact (show a = p from hxp).symm.trans (show a = q from hxq)
  | inl a =>
    cases y with
    | inr b =>
      exact (show b = p from hyp).symm.trans (show b = q from hyq)
    | inl b =>
      by_contra hpq
      apply hxy
      exact congrArg Sum.inl (h.2 p q hpq ⟨hxp, hxq⟩ ⟨hyp, hyq⟩)

/-- Two distinct copies cannot meet two distinct common wagons. -/
theorem contact_two_common_wagons_eq (h : D.ContactG2)
    {i j : I} (hij : i ≠ j) {p q : P}
    (hip : D.contactMeets i p) (hiq : D.contactMeets i q)
    (hjp : D.contactMeets j p) (hjq : D.contactMeets j q) : p = q := by
  by_contra hpq
  have hne : (Sum.inr p : V ⊕ P) ≠ Sum.inr q := by
    intro he
    exact hpq (Sum.inr.inj he)
  obtain ⟨w, hw, hw'⟩ := D.contact_shared_pair_in_wagon h
    (a := Sum.inl i) (b := Sum.inl j)
    (by intro he; exact hij (Sum.inl.inj he)) hne hip hiq hjp hjq
  exact hpq ((show p = w from hw).trans (show q = w from hw').symm)

/-- Shared mixed contact gives actual incident edges on both sides.
This is the contact-graph replacement of the old order-one argument. -/
theorem contact_bridges_of_shared_mixed (h1 : D.ContactG1) (h2 : D.ContactG2)
    {i j : I} (hij : i ≠ j) {p : P} {x : V}
    (hxi : x ∈ D.copyCarrier i) (hxj : x ∈ D.copyCarrier j)
    (hip : D.contactMeets i p) (hjp : D.contactMeets j p) :
    D.Bridge (.inl i) x p ∧ D.Bridge (.inl j) x p := by
  obtain ⟨w, hw, hw'⟩ := D.contact_shared_pair_in_wagon h2
    (a := Sum.inl i) (b := Sum.inl j)
    (by intro he; exact hij (Sum.inl.inj he))
    (x := Sum.inl x) (y := Sum.inr p) (by intro he; cases he)
    hxi hip hxj hjp
  have hp : p = w := hw'
  subst w
  have hx : x ∈ D.contactWagonCarrier p := hw
  exact ⟨h1.bridge i p (Or.inl hip) x hxi hx,
    h1.bridge j p (Or.inl hjp) x hxj hx⟩

end OrderOneData

end StructuralRamsey.Girth
