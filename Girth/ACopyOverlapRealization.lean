import Mathlib.Data.Set.Function
import Mathlib.Logic.Equiv.Basic
import Mathlib.Logic.Embedding.Basic

/-!
# Point realization of coherent binary copy overlaps

This is the point-set part of manuscript Lemma `binaryrealization`.
`CoherentOverlap` presents each partial bijection by its graph. Its hypotheses
are exactly the diagonal, reversal, and composition coherence laws. In
particular, neither functionality nor injectivity of the quotient charts is
assumed: both follow from coherence. `overlapEquiv` recovers the partial
bijection as an equivalence between its domain and range.

The quotient has exactly the prescribed overlaps, and linear overlap diagrams
give carriers with at most one point in common. Conversely, actual injective
charts recover their ambient point union, and recover the whole ambient point
type when jointly surjective. If the coordinate type has at least two points,
linearity also identifies nodes bijectively with their specified carrier sets.

Scope: coordinates and point equality only. This file does not assert that
arbitrary relational decorations survive gluing as induced embeddings, that
unsupported chart occurrences have been retained, or that all actual physical
copies are the specified nodes. Those are separate faithfulness obligations.
-/

namespace StructuralRamsey.Girth

universe u v w

/-- Binary overlap graphs with the manuscript's three coherence identities. -/
structure CoherentOverlap (Ω : Type u) (K : Type v) where
  Rel : Ω → Ω → K → K → Prop
  diagonal : ∀ e a b, Rel e e a b ↔ a = b
  reverse : ∀ {e f a b}, Rel e f a b → Rel f e b a
  compose : ∀ {e f g a b c}, Rel e f a b → Rel f g b c → Rel e g a c

namespace CoherentOverlap

variable {Ω : Type u} {K : Type v} (D : CoherentOverlap Ω K)

theorem refl (e : Ω) (a : K) : D.Rel e e a a :=
  (D.diagonal e a a).mpr rfl

theorem reverse_iff {e f : Ω} {a b : K} :
    D.Rel e f a b ↔ D.Rel f e b a :=
  ⟨D.reverse, D.reverse⟩

/-- Every pair label is the graph of a partial function. -/
theorem right_unique {e f : Ω} {a b c : K}
    (hab : D.Rel e f a b) (hac : D.Rel e f a c) : b = c :=
  (D.diagonal f b c).mp (D.compose (D.reverse hab) hac)

/-- The inverse pair label is also the graph of a partial function. -/
theorem left_unique {e f : Ω} {a b c : K}
    (hac : D.Rel e f a c) (hbc : D.Rel e f b c) : a = b :=
  (D.diagonal e a b).mp (D.compose hac (D.reverse hbc))

def domain (e f : Ω) : Set K := {a | ∃ b, D.Rel e f a b}

def range (e f : Ω) : Set K := {b | ∃ a, D.Rel e f a b}

/-- Explicit recovery of a partial bijection from its coherent graph. -/
noncomputable def overlapEquiv (e f : Ω) : D.domain e f ≃ D.range e f where
  toFun a := ⟨Classical.choose a.property,
    ⟨a.val, Classical.choose_spec a.property⟩⟩
  invFun b := ⟨Classical.choose b.property,
    ⟨b.val, Classical.choose_spec b.property⟩⟩
  left_inv a := by
    apply Subtype.ext
    exact D.left_unique (Classical.choose_spec
      (show ∃ a', D.Rel e f a' (Classical.choose a.property) from
        ⟨a.val, Classical.choose_spec a.property⟩))
      (Classical.choose_spec a.property)
  right_inv b := by
    apply Subtype.ext
    exact D.right_unique (Classical.choose_spec
      (show ∃ b', D.Rel e f (Classical.choose b.property) b' from
        ⟨b.val, Classical.choose_spec b.property⟩))
      (Classical.choose_spec b.property)

theorem overlapEquiv_rel (e f : Ω) (a : D.domain e f) :
    D.Rel e f a.val (D.overlapEquiv e f a).val :=
  Classical.choose_spec a.property

theorem overlapEquiv_eq_iff (e f : Ω)
    (a : D.domain e f) (b : D.range e f) :
    D.overlapEquiv e f a = b ↔ D.Rel e f a.val b.val := by
  constructor
  · intro h
    rw [← h]
    exact D.overlapEquiv_rel e f a
  · intro h
    apply Subtype.ext
    exact D.right_unique (D.overlapEquiv_rel e f a) h

/-- The occurrence relation is already an equivalence: no transitive closure
can introduce additional identifications. -/
def occurrenceSetoid : Setoid (Ω × K) where
  r p q := D.Rel p.1 q.1 p.2 q.2
  iseqv := {
    refl := fun p => D.refl p.1 p.2
    symm := fun h => D.reverse h
    trans := fun h₁ h₂ => D.compose h₁ h₂ }

def Point := Quotient D.occurrenceSetoid

def nodePoint (e : Ω) (a : K) : D.Point :=
  Quotient.mk D.occurrenceSetoid (e, a)

/-- Quotient equality is exactly a declared binary overlap, in both directions. -/
theorem nodePoint_eq_iff {e f : Ω} {a b : K} :
    D.nodePoint e a = D.nodePoint f b ↔ D.Rel e f a b := by
  constructor
  · exact Quotient.exact
  · intro h
    exact Quotient.sound h

/-- Coherence prevents folding two coordinates of a single node. -/
theorem nodePoint_injective (e : Ω) : Function.Injective (D.nodePoint e) := by
  intro a b h
  exact (D.diagonal e a b).mp (D.nodePoint_eq_iff.mp h)

def nodeEmbedding (e : Ω) : K ↪ D.Point :=
  ⟨D.nodePoint e, D.nodePoint_injective e⟩

def carrier (e : Ω) : Set D.Point := Set.range (D.nodePoint e)

/-- A point of one node lies in another exactly when its overlap map is defined. -/
theorem nodePoint_mem_carrier_iff (e f : Ω) (a : K) :
    D.nodePoint e a ∈ D.carrier f ↔ a ∈ D.domain e f := by
  constructor
  · rintro ⟨b, hb⟩
    exact ⟨b, D.nodePoint_eq_iff.mp hb.symm⟩
  · rintro ⟨b, hab⟩
    exact ⟨b, (D.nodePoint_eq_iff.mpr hab).symm⟩

/-- The full intersection is precisely the image of the prescribed domain. -/
theorem carrier_inter (e f : Ω) :
    D.carrier e ∩ D.carrier f = D.nodePoint e '' D.domain e f := by
  ext x
  constructor
  · rintro ⟨⟨a, rfl⟩, hf⟩
    exact ⟨a, (D.nodePoint_mem_carrier_iff e f a).mp hf, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨⟨a, rfl⟩, (D.nodePoint_mem_carrier_iff e f a).mpr ha⟩

/-- Every realized point is supported by at least one node. -/
theorem point_covered (x : D.Point) : ∃ e, x ∈ D.carrier e := by
  induction x using Quotient.inductionOn with
  | h p => exact ⟨p.1, p.2, rfl⟩

/-- Cardinality at most one for each off-diagonal overlap domain, without
requiring finite coordinate types. -/
def Linear : Prop :=
  ∀ e f, e ≠ f → (D.domain e f).Subsingleton

theorem linear_carrier_inter (hD : D.Linear) (e f : Ω) (hef : e ≠ f) :
    (D.carrier e ∩ D.carrier f).Subsingleton := by
  intro x hx y hy
  rw [D.carrier_inter e f] at hx hy
  rcases hx with ⟨a, ha, rfl⟩
  rcases hy with ⟨b, hb, rfl⟩
  exact congrArg (D.nodePoint e) (hD e f hef ha hb)

/-- Linearity is an exact property of the realized node carriers. -/
theorem linear_iff_carrier_inter : D.Linear ↔
    ∀ e f, e ≠ f → (D.carrier e ∩ D.carrier f).Subsingleton := by
  constructor
  · exact D.linear_carrier_inter
  · intro h e f hef a ha b hb
    apply D.nodePoint_injective e
    apply h e f hef
    · exact ⟨⟨a, rfl⟩, (D.nodePoint_mem_carrier_iff e f a).mpr ha⟩
    · exact ⟨⟨b, rfl⟩, (D.nodePoint_mem_carrier_iff e f b).mpr hb⟩

/-- When the physical type has at least two points, linearity forbids two
different nodes from having equal realized carriers. -/
theorem carrier_injective_of_linear [Nontrivial K] (hD : D.Linear) :
    Function.Injective D.carrier := by
  classical
  intro e f hef
  by_contra hne
  obtain ⟨a, b, hab⟩ := exists_pair_ne K
  have hmem (c : K) : D.nodePoint e c ∈ D.carrier e ∩ D.carrier f := by
    constructor
    · exact ⟨c, rfl⟩
    · rw [← hef]
      exact ⟨c, rfl⟩
  exact hab (D.nodePoint_injective e
    (D.linear_carrier_inter hD e f hne (hmem a) (hmem b)))

theorem carrier_eq_iff_of_linear [Nontrivial K] (hD : D.Linear) (e f : Ω) :
    D.carrier e = D.carrier f ↔ e = f :=
  (D.carrier_injective_of_linear hD).eq_iff

/-- Nodes are exactly the specified realized hyperedges. The codomain is the
range of the carrier map, not a type of all relational copies. -/
noncomputable def carrierRangeEquiv [Nontrivial K] (hD : D.Linear) :
    Ω ≃ Set.range D.carrier :=
  Equiv.ofBijective (fun e => ⟨D.carrier e, ⟨e, rfl⟩⟩) (by
    constructor
    · intro e f h
      exact D.carrier_injective_of_linear hD (congrArg Subtype.val h)
    · rintro ⟨c, e, rfl⟩
      exact ⟨e, rfl⟩)

@[simp] theorem carrierRangeEquiv_val [Nontrivial K] (hD : D.Linear) (e : Ω) :
    (D.carrierRangeEquiv hD e).val = D.carrier e := rfl

section ActualCharts

variable {V : Type w} (chart : Ω → K ↪ V)

/-- Encode actual injective charts by equality of their ambient points. -/
def ofCharts : CoherentOverlap Ω K where
  Rel e f a b := chart e a = chart f b
  diagonal e _ _ := (chart e).injective.eq_iff
  reverse h := h.symm
  compose h₁ h₂ := h₁.trans h₂

/-- Evaluation of a realized occurrence in the original ambient point type. -/
def toAmbient : (ofCharts chart).Point → V :=
  Quotient.lift (fun p : Ω × K => chart p.1 p.2) (fun _ _ h => h)

@[simp] theorem toAmbient_nodePoint (e : Ω) (a : K) :
    toAmbient chart ((ofCharts chart).nodePoint e a) = chart e a := rfl

/-- Recording every actual overlap makes the evaluation map injective. -/
theorem toAmbient_injective : Function.Injective (toAmbient chart) := by
  intro x y
  induction x using Quotient.inductionOn with
  | h p =>
    induction y using Quotient.inductionOn with
    | h q =>
      intro hpq
      exact Quotient.sound hpq

/-- Evaluation recovers precisely the union of the given charts. -/
theorem mem_range_toAmbient_iff (x : V) :
    x ∈ Set.range (toAmbient chart) ↔ ∃ e a, chart e a = x := by
  constructor
  · rintro ⟨q, hq⟩
    induction q using Quotient.inductionOn with
    | h p => exact ⟨p.1, p.2, hq⟩
  · rintro ⟨e, a, rfl⟩
    exact ⟨(ofCharts chart).nodePoint e a, rfl⟩

theorem toAmbient_surjective_iff : Function.Surjective (toAmbient chart) ↔
    ∀ x, ∃ e a, chart e a = x := by
  constructor
  · intro h x
    exact (mem_range_toAmbient_iff chart x).mp (h x)
  · intro h x
    exact (mem_range_toAmbient_iff chart x).mpr (h x)

/-- Covered actual injective charts reconstruct the ambient point type. -/
noncomputable def ambientEquiv
    (covered : ∀ x, ∃ e a, chart e a = x) : (ofCharts chart).Point ≃ V :=
  Equiv.ofBijective (toAmbient chart)
    ⟨toAmbient_injective chart, (toAmbient_surjective_iff chart).mpr covered⟩

@[simp] theorem ambientEquiv_nodePoint
    (covered : ∀ x, ∃ e a, chart e a = x) (e : Ω) (a : K) :
    ambientEquiv chart covered ((ofCharts chart).nodePoint e a) = chart e a := rfl

end ActualCharts

/-- Re-encoding the quotient's node charts returns exactly the original
binary labels; realization did not complete them with any extra overlaps. -/
theorem of_nodeEmbeddings_rel_iff (e f : Ω) (a b : K) :
    (ofCharts D.nodeEmbedding).Rel e f a b ↔ D.Rel e f a b :=
  D.nodePoint_eq_iff

end CoherentOverlap
end StructuralRamsey.Girth
