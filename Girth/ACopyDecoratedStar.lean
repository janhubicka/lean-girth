import Girth.ACopyPointStar
import Girth.ACopyLayeredStar

set_option autoImplicit false

/-!
# Points and actual nodes in one generated decorated star

Point presentations retain every source point, including arbitrary chart
records not carried by any node. Records are not assumed distinct from node
coordinates. The point and node quotients have separate generators; shared
node coordinates commute with their point contacts. Wagon carriers are derived
from actual quotient nodes, not postulated independently.

No relational inducedness, linearity, or completeness of relational A-copies
is claimed. In particular the supported overlap realization embeds into the
full point quotient, and need not exhaust the retained chart records.
-/

namespace StructuralRamsey.Girth.ACopyDecoratedStar

open ACopyExactStar
open ACopyLayeredStar

universe v
variable {C I K PC : Type v} {S Q PS PQ : I → Type v}

/-- Point source presentations over an independently generated node hierarchy.
The shared point presentation can include an entire induced gluing domain,
not just the coordinates of its shared nodes. -/
structure Data (N : Diagram C I S Q) (K PC : Type v)
    (PS PQ : I → Type v) where
  coreEq : Setoid PC
  sourceEq : (i : I) → Setoid (PS i)
  alpha : (i : I) → PQ i → PC
  beta : (i : I) → PQ i → PS i
  compatible : ∀ i p q,
    coreEq (alpha i p) (alpha i q) ↔ sourceEq i (beta i p) (beta i q)
  coreCoord : C → K → PC
  sourceCoord : (i : I) → S i → K → PS i
  core_coord_eq : ∀ e a b, coreEq (coreCoord e a) (coreCoord e b) ↔ a = b
  source_coord_eq : ∀ i e a b,
    sourceEq i (sourceCoord i e a) (sourceCoord i e b) ↔ a = b
  sharedCoord : (i : I) → Q i → K → PQ i
  shared_core : ∀ i s a, alpha i (sharedCoord i s a) = coreCoord (N.alpha i s) a
  shared_source : ∀ i s a, beta i (sharedCoord i s a) = sourceCoord i (N.beta i s) a

namespace Data

variable {N : Diagram C I S Q} (D : Data N K PC PS PQ)

abbrev PointStep := SourceStar.Step D.coreEq D.sourceEq D.alpha D.beta
abbrev Point := Quot D.PointStep

/-- All source records are retained, whether supported or unsupported. -/
def coreRecord (p : PC) : D.Point := Quot.mk _ (.inl p)
def sourceRecord (i : I) (p : PS i) : D.Point := Quot.mk _ (.inr ⟨i, p⟩)

def coreMap : Quotient D.coreEq → D.Point := fun p =>
  SourceStar.classToQuotient D.coreEq D.sourceEq D.alpha D.beta (.inl p)
def sourceMap (i : I) : Quotient (D.sourceEq i) → D.Point := fun p =>
  SourceStar.classToQuotient D.coreEq D.sourceEq D.alpha D.beta (.inr ⟨i, p⟩)

@[simp] theorem coreMap_mk (p : PC) :
    D.coreMap (Quotient.mk _ p) = D.coreRecord p := rfl
@[simp] theorem sourceMap_mk (i : I) (p : PS i) :
    D.sourceMap i (Quotient.mk _ p) = D.sourceRecord i p := rfl

theorem coreMap_injective : Function.Injective D.coreMap :=
  SourceStar.core_classMap_injective _ _ _ _ D.compatible
theorem sourceMap_injective (i : I) : Function.Injective (D.sourceMap i) :=
  SourceStar.source_classMap_injective _ _ _ _ D.compatible i

/-- Exactness includes arbitrary retained records, not only node coordinates. -/
theorem coreRecord_eq_iff (p q : PC) :
    D.coreRecord p = D.coreRecord q ↔ D.coreEq p q := by
  change Quot.mk D.PointStep _ = Quot.mk D.PointStep _ ↔ _
  rw [Quot.eq]
  exact SourceStar.generated_core_iff _ _ _ _ D.compatible p q

theorem sourceRecord_eq_iff (i : I) (p q : PS i) :
    D.sourceRecord i p = D.sourceRecord i q ↔ D.sourceEq i p q := by
  change Quot.mk D.PointStep _ = Quot.mk D.PointStep _ ↔ _
  rw [Quot.eq]
  exact SourceStar.generated_source_iff _ _ _ _ D.compatible i p q

theorem sourceRecord_eq_coreRecord_iff (i : I) (p : PS i) (q : PC) :
    D.sourceRecord i p = D.coreRecord q ↔
      ∃ s : PQ i, D.sourceEq i (D.beta i s) p ∧ D.coreEq (D.alpha i s) q := by
  change Quot.mk D.PointStep _ = Quot.mk D.PointStep _ ↔ _
  rw [Quot.eq]
  exact SourceStar.generated_source_core_iff _ _ _ _ D.compatible i p q

def coreImage : Set D.Point := Set.range D.coreRecord
def sourceImage (i : I) : Set D.Point := Set.range (D.sourceRecord i)
def sharedImage (i : I) : Set D.Point := Set.range (fun p => D.coreRecord (D.alpha i p))

/-- Exact source/core intersection for the full point presentations, including
all retained records in the shared induced domain. -/
theorem sourceImage_inter_coreImage (i : I) :
    D.sourceImage i ∩ D.coreImage = D.sharedImage i := by
  ext x
  constructor
  · rintro ⟨⟨p, rfl⟩, q, hq⟩
    obtain ⟨s, hs, _⟩ := (D.sourceRecord_eq_coreRecord_iff i p q).mp hq.symm
    refine ⟨s, ?_⟩
    have hshared : D.sourceRecord i (D.beta i s) = D.coreRecord (D.alpha i s) :=
      Quot.sound (SourceStar.Step.shared i s)
    exact hshared.symm.trans ((D.sourceRecord_eq_iff i _ _).mpr hs)
  · rintro ⟨s, rfl⟩
    exact ⟨⟨D.beta i s, Quot.sound (SourceStar.Step.shared i s)⟩, D.alpha i s, rfl⟩

/-- Distinct full source point spaces meet precisely through their shared
images in the core; neither space is assumed covered by nodes. -/
theorem distinct_sourceImage_inter (i j : I) (hij : i ≠ j) :
    D.sourceImage i ∩ D.sourceImage j = D.sharedImage i ∩ D.sharedImage j := by
  ext x
  constructor
  · intro h
    obtain ⟨p, hp⟩ := h.1
    obtain ⟨q, hq⟩ := h.2
    obtain ⟨c, hc, _⟩ :=
      (SourceStar.generated_distinct_sources_iff D.coreEq D.sourceEq D.alpha D.beta
        D.compatible i j hij p q).mp (Quot.eqvGen_exact (hp.trans hq.symm))
    have hcore : x ∈ D.coreImage := ⟨c, (Quot.eqvGen_sound hc).symm.trans hp⟩
    exact ⟨D.sourceImage_inter_coreImage i ▸ ⟨h.1, hcore⟩,
      D.sourceImage_inter_coreImage j ▸ ⟨h.2, hcore⟩⟩
  · intro h
    have hi : x ∈ D.sourceImage i ∩ D.coreImage := D.sourceImage_inter_coreImage i ▸ h.1
    have hj : x ∈ D.sourceImage j ∩ D.coreImage := D.sourceImage_inter_coreImage j ▸ h.2
    exact ⟨hi.1, hj.1⟩

def corePoint (e : C) (a : K) : D.Point := D.coreRecord (D.coreCoord e a)
def sourcePoint (i : I) (e : S i) (a : K) : D.Point :=
  D.sourceRecord i (D.sourceCoord i e a)

theorem sharedPoint_eq (i : I) (s : Q i) (a : K) :
    D.sourcePoint i (N.beta i s) a = D.corePoint (N.alpha i s) a := by
  have h : D.sourceRecord i (D.beta i (D.sharedCoord i s a)) =
      D.coreRecord (D.alpha i (D.sharedCoord i s a)) :=
    Quot.sound (SourceStar.Step.shared i (D.sharedCoord i s a))
  simpa only [D.shared_core, D.shared_source, corePoint, sourcePoint] using h

def rawNodePoint : ACopyLayeredStar.Raw (Core := C) (Source := S) → K → D.Point
  | .inl e => D.corePoint e
  | .inr ⟨i, e⟩ => D.sourcePoint i e

/-- Coordinates descend through exactly the shared-node quotient. -/
def nodePoint : Node N → K → D.Point := Quot.lift D.rawNodePoint (by
  intro x y h
  cases h with
  | core e f h =>
      have hef := (N.core_zero e f).mp h
      subst f
      rfl
  | source i e f h =>
      have hef := (N.source_zero i e f).mp h
      subst f
      rfl
  | shared i s =>
      funext a
      exact D.sharedPoint_eq i s a)

@[simp] theorem nodePoint_core (e : C) (a : K) :
    D.nodePoint (nodeCore N e) a = D.corePoint e a := rfl
@[simp] theorem nodePoint_source (i : I) (e : S i) (a : K) :
    D.nodePoint (nodeSource N i e) a = D.sourcePoint i e a := rfl

theorem nodePoint_injective (e : Node N) : Function.Injective (D.nodePoint e) := by
  refine Quot.inductionOn e ?_
  intro x a b hab
  cases x with
  | inl e =>
      exact (D.core_coord_eq e a b).mp
        ((D.coreRecord_eq_iff _ _).mp hab)
  | inr t =>
      rcases t with ⟨i, e⟩
      exact (D.source_coord_eq i e a b).mp
        ((D.sourceRecord_eq_iff i _ _).mp hab)

def nodeEmbedding (e : Node N) : K ↪ D.Point :=
  ⟨D.nodePoint e, D.nodePoint_injective e⟩

/-- Source overlap graphs are read from their original point equivalences. -/
def coreDiagram : CoherentOverlap C K := CoherentOverlap.ofCharts
  (fun e => ⟨fun a => Quotient.mk D.coreEq (D.coreCoord e a), by
    intro a b h
    exact (D.core_coord_eq e a b).mp (Quotient.exact h)⟩)

def sourceDiagram (i : I) : CoherentOverlap (S i) K := CoherentOverlap.ofCharts
  (fun e => ⟨fun a => Quotient.mk (D.sourceEq i) (D.sourceCoord i e a), by
    intro a b h
    exact (D.source_coord_eq i e a b).mp (Quotient.exact h)⟩)

def output : CoherentOverlap (Node N) K := CoherentOverlap.ofCharts D.nodeEmbedding

theorem output_rel_core_iff (e f : C) (a b : K) :
    D.output.Rel (nodeCore N e) (nodeCore N f) a b ↔ D.coreDiagram.Rel e f a b := by
  change D.coreRecord (D.coreCoord e a) = D.coreRecord (D.coreCoord f b) ↔
    Quotient.mk D.coreEq (D.coreCoord e a) = Quotient.mk D.coreEq (D.coreCoord f b)
  rw [D.coreRecord_eq_iff, Quotient.eq]

theorem output_rel_source_iff (i : I) (e f : S i) (a b : K) :
    D.output.Rel (nodeSource N i e) (nodeSource N i f) a b ↔
      (D.sourceDiagram i).Rel e f a b := by
  change D.sourceRecord i (D.sourceCoord i e a) =
      D.sourceRecord i (D.sourceCoord i f b) ↔
    Quotient.mk (D.sourceEq i) (D.sourceCoord i e a) =
      Quotient.mk (D.sourceEq i) (D.sourceCoord i f b)
  rw [D.sourceRecord_eq_iff, Quotient.eq]

/-- These use the same diagram-embedding interface as the supported point star. -/
def coreDiagramEmbedding : ACopyPointStar.DiagramEmbedding D.coreDiagram D.output where
  node := ⟨nodeCore N, nodeCore_injective N⟩
  rel_iff := D.output_rel_core_iff

def sourceDiagramEmbedding (i : I) :
    ACopyPointStar.DiagramEmbedding (D.sourceDiagram i) D.output where
  node := ⟨nodeSource N i, nodeSource_injective N i⟩
  rel_iff := D.output_rel_source_iff i

def supportedPoint : D.output.Point → D.Point :=
  CoherentOverlap.toAmbient D.nodeEmbedding

theorem supportedPoint_injective : Function.Injective D.supportedPoint :=
  CoherentOverlap.toAmbient_injective D.nodeEmbedding

theorem supportedPoint_range_iff (p : D.Point) :
    p ∈ Set.range D.supportedPoint ↔ ∃ e a, D.nodePoint e a = p :=
  CoherentOverlap.mem_range_toAmbient_iff D.nodeEmbedding p

/-- Every output point has a retained source record, without claiming it is
supported by a node. -/
theorem point_has_record (p : D.Point) :
    (∃ q, D.coreRecord q = p) ∨ ∃ i q, D.sourceRecord i q = p := by
  refine Quot.inductionOn p ?_
  intro x
  cases x with
  | inl q => exact Or.inl ⟨q, rfl⟩
  | inr q => exact Or.inr ⟨q.1, q.2, rfl⟩

/-- A wagon contains precisely the coordinates of its actual descendant nodes.
Unsupported records are not inserted into this set. -/
def wagonCarrier (n : ℕ) (w : Wagon N n) : Set D.Point :=
  {p | ∃ e : Node N, ∃ a : K,
    parent N (Nat.zero_le n) e = w ∧ D.nodePoint e a = p}

def coreCarrier (n : ℕ) (c : Quotient (N.coreEq n)) : Set D.Point :=
  {p | ∃ e a, Quotient.mk (N.coreEq n) e = c ∧ D.corePoint e a = p}

def sourceCarrier (n : ℕ) (i : I) (s : Quotient (N.sourceEq n i)) : Set D.Point :=
  {p | ∃ e a, Quotient.mk (N.sourceEq n i) e = s ∧ D.sourcePoint i e a = p}

/-- Derived core-wagon carrier: its own source nodes and every contacting
source class, with the original labels and all of their node coordinates. -/
theorem mem_core_wagonCarrier_iff (n : ℕ) (c : Quotient (N.coreEq n)) (p : D.Point) :
    p ∈ D.wagonCarrier n (ACopyLayeredStar.coreMap N n c) ↔
      p ∈ D.coreCarrier n c ∨
      ∃ i s, contact N n i s = some c ∧ p ∈ D.sourceCarrier n i s := by
  constructor
  · rintro ⟨e, a, he, hp⟩
    revert he hp
    refine Quot.inductionOn e ?_
    intro raw he hp
    cases raw with
    | inl e =>
        exact Or.inl ⟨e, a, ACopyLayeredStar.coreMap_injective N n he, hp⟩
    | inr t =>
        rcases t with ⟨i, e⟩
        exact Or.inr ⟨i, Quotient.mk _ e,
          (sourceMap_eq_coreMap_iff N n i _ c).mp he, e, a, rfl, hp⟩
  · rintro (⟨e, a, he, hp⟩ | ⟨i, s, hs, e, a, he, hp⟩)
    · refine ⟨nodeCore N e, a, ?_, hp⟩
      change ACopyLayeredStar.coreMap N n (Quotient.mk _ e) = _
      rw [he]
    · refine ⟨nodeSource N i e, a, ?_, hp⟩
      change ACopyLayeredStar.sourceMap N n i (Quotient.mk _ e) = _
      rw [he]
      exact (sourceMap_eq_coreMap_iff N n i s c).mpr hs

theorem core_wagonCarrier (n : ℕ) (c : Quotient (N.coreEq n)) :
    D.wagonCarrier n (ACopyLayeredStar.coreMap N n c) =
      D.coreCarrier n c ∪
        {p | ∃ i s, contact N n i s = some c ∧ p ∈ D.sourceCarrier n i s} := by
  ext p
  exact D.mem_core_wagonCarrier_iff n c p

/-- A class with no shared node cannot equal a wagon of another source.
This is a statement about labels, not disjointness of their point carriers. -/
theorem private_sourceMap_ne_other (n : ℕ) (i j : I) (hji : j ≠ i)
    (s : Quotient (N.sourceEq n i)) (hPrivate : contact N n i s = none)
    (t : Quotient (N.sourceEq n j)) :
    ACopyLayeredStar.sourceMap N n j t ≠ ACopyLayeredStar.sourceMap N n i s := by
  obtain ⟨a, rfl⟩ := Quotient.exists_rep s
  obtain ⟨b, rfl⟩ := Quotient.exists_rep t
  intro heq
  obtain ⟨c, _, hc⟩ :=
    (SourceStar.generated_distinct_sources_iff (N.coreEq n) (N.sourceEq n)
      N.alpha N.beta (N.compatible n) j i hji b a).mp (Quot.eqvGen_exact heq)
  have hContact := (sourceMap_eq_coreMap_iff N n i
    (Quotient.mk _ a) (Quotient.mk _ c)).mp (Quot.eqvGen_sound hc)
  rw [hPrivate] at hContact
  cases hContact

/-- A private wagon's carrier is exactly the image of its own source class.
It may still meet core points, since different wagons may share vertices. -/
theorem private_wagonCarrier (n : ℕ) (i : I) (s : Quotient (N.sourceEq n i))
    (hPrivate : contact N n i s = none) :
    D.wagonCarrier n (ACopyLayeredStar.sourceMap N n i s) = D.sourceCarrier n i s := by
  ext p
  constructor
  · rintro ⟨e, a, he, hp⟩
    revert he hp
    refine Quot.inductionOn e ?_
    intro raw he hp
    cases raw with
    | inl e =>
        have hContact := (sourceMap_eq_coreMap_iff N n i s (Quotient.mk _ e)).mp he.symm
        rw [hPrivate] at hContact
        cases hContact
    | inr t =>
        rcases t with ⟨j, e⟩
        by_cases hji : j = i
        · subst j
          exact ⟨e, a, ACopyLayeredStar.sourceMap_injective N n i he, hp⟩
        · exact (private_sourceMap_ne_other (N := N) n i j hji s hPrivate
            (Quotient.mk _ e) he).elim
  · rintro ⟨e, a, he, hp⟩
    refine ⟨nodeSource N i e, a, ?_, hp⟩
    change ACopyLayeredStar.sourceMap N n i (Quotient.mk _ e) = _
    rw [he]

/-- Parent maps increase actual carriers by retaining every descendant node. -/
theorem wagonCarrier_mono {m n : ℕ} (hmn : m ≤ n) (w : Wagon N m) :
    D.wagonCarrier m w ⊆ D.wagonCarrier n (parent N hmn w) := by
  rintro p ⟨e, a, he, hp⟩
  refine ⟨e, a, ?_, hp⟩
  rw [← parent_comp N (Nat.zero_le m) hmn, he]

end Data
end StructuralRamsey.Girth.ACopyDecoratedStar
