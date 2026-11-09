import Girth.TrainFillingPrivateUniform

set_option Elab.async false

/-!
# Direct private extension from the disjoint sum of the first wagons

The compact cutoff-two proof uses W = Σ p, F_p, rather than replacing
each F_p by a copy of W.  A strong copy of W in X restricts to a strong
copy of each summand: a template edge meeting that summand twice first
comes from some summand by global strongness, and one common point then
identifies the summand label.  This file proves that missing restriction
step and constructs the existing private-extension input from it.

Neither equal wagon sizes nor equivalences F_p ≃ W are required.  No
intersection, coverage, or strongness of the output extension is assumed.
-/

namespace StructuralRamsey.Girth.CompactPrivateExtension

universe u v

variable {V P X : Type v}

abbrev Wagon (oldCarrier : P → Set V) (p : P) :=
  {x : V // x ∈ oldCarrier p}

abbrev WagonSum (oldCarrier : P → Set V) := Σ p, Wagon oldCarrier p

/-- Actual edges of the disjoint wagon sum, retaining the summand tag. -/
def sumEdges (oldCarrier : P → Set V)
    (wagonEdges : ∀ p, Set (Set (Wagon oldCarrier p))) :
    Set (Set (WagonSum oldCarrier)) :=
  {a | ∃ p, ∃ e ∈ wagonEdges p, a = Sigma.mk p '' e}

/-- Restrict the selected strong W-copy to one of its summands. -/
def coordinate (oldCarrier : P → Set V)
    (T : UniformPrivateTemplate (WagonSum oldCarrier) X) (p : P) :
    Wagon oldCarrier p ↪ X where
  toFun x := T.star ⟨p, x⟩
  inj' := by
    intro x y h
    exact eq_of_heq (Sigma.mk.inj_iff.mp (T.star.injective h)).2

/-- The selected edge set in wagon p consists only of p's summand edges. -/
def selectedEdges (oldCarrier : P → Set V)
    (wagonEdges : ∀ p, Set (Set (Wagon oldCarrier p)))
    (T : UniformPrivateTemplate (WagonSum oldCarrier) X) (p : P) :
    Set {a : Set X // a ∈ T.templateEdges} :=
  {a | ∃ e ∈ wagonEdges p, a.1 = coordinate oldCarrier T p '' e}

/-- Global strongness of the disjoint sum implies strongness of every
restricted summand, with the correct selected local edge labels. -/
theorem restricted_strong
    (oldCarrier : P → Set V)
    (wagonEdges : ∀ p, Set (Set (Wagon oldCarrier p)))
    (T : UniformPrivateTemplate (WagonSum oldCarrier) X)
    (hEdges : T.localEdges = sumEdges oldCarrier wagonEdges)
    (p : P) (a : {a : Set X // a ∈ T.templateEdges}) (x y : X)
    (hxy : x ≠ y) (hx : x ∈ a.1) (hy : y ∈ a.1)
    (hxRange : x ∈ Set.range (coordinate oldCarrier T p))
    (hyRange : y ∈ Set.range (coordinate oldCarrier T p)) :
    a ∈ selectedEdges oldCarrier wagonEdges T p := by
  obtain ⟨xp, hxp⟩ := hxRange
  obtain ⟨yp, hyp⟩ := hyRange
  obtain ⟨b, hb⟩ := T.strong a x y hxy hx hy
    ⟨⟨p, xp⟩, hxp⟩ ⟨⟨p, yp⟩, hyp⟩
  have hbEdges : b.1 ∈ sumEdges oldCarrier wagonEdges := by
    rw [← hEdges]
    exact b.2
  obtain ⟨q, e, he, hbe⟩ := hbEdges
  have hxImage : x ∈ T.star '' (Sigma.mk q '' e) := by
    rw [← hbe, ← hb]
    exact hx
  obtain ⟨_, ⟨z, hz, rfl⟩, hzx⟩ := hxImage
  have hqp : q = p := congrArg Sigma.fst
    (T.star.injective (hzx.trans hxp.symm))
  subst q
  refine ⟨e, he, ?_⟩
  rw [hb, hbe, Set.image_image]
  rfl

/-- A covered disjoint sum and its chosen strong copy construct the
private-extension input directly, even when wagon vertex counts differ. -/
noncomputable def toPrivateWagonInput
    (oldCarrier : P → Set V)
    (wagonEdges : ∀ p, Set (Set (Wagon oldCarrier p)))
    (hCovered : ∀ p (x : Wagon oldCarrier p),
      ∃ e ∈ wagonEdges p, x ∈ e)
    (T : UniformPrivateTemplate (WagonSum oldCarrier) X)
    (hEdges : T.localEdges = sumEdges oldCarrier wagonEdges) :
    PrivateWagonInput V P X where
  oldCarrier := oldCarrier
  coordinate := coordinate oldCarrier T
  templateEdges := T.templateEdges
  selectedEdges := selectedEdges oldCarrier wagonEdges T
  selected_inside := by
    intro p a ha x hx
    obtain ⟨e, _, he⟩ := ha
    rw [he] at hx
    obtain ⟨z, _, hzx⟩ := hx
    exact ⟨z, hzx⟩
  local_strong := restricted_strong oldCarrier wagonEdges T hEdges
  local_cover := by
    intro p x
    obtain ⟨e, he, hx⟩ := hCovered p x
    have hSum : Sigma.mk p '' e ∈ T.localEdges := by
      rw [hEdges]
      exact ⟨p, e, he, rfl⟩
    let b : {b : Set (WagonSum oldCarrier) // b ∈ T.localEdges} :=
      ⟨Sigma.mk p '' e, hSum⟩
    have hMap : coordinate oldCarrier T p '' e ∈ T.templateEdges := by
      change (fun x => T.star ⟨p, x⟩) '' e ∈ T.templateEdges
      simpa only [b, Set.image_image] using T.map_edge b
    exact ⟨⟨coordinate oldCarrier T p '' e, hMap⟩,
      ⟨e, he, rfl⟩, ⟨x, hx, rfl⟩⟩

/-- This is the literal restricted map c|F_p used in the compact proof. -/
@[simp] theorem toPrivateWagonInput_coordinate
    (oldCarrier : P → Set V)
    (wagonEdges : ∀ p, Set (Set (Wagon oldCarrier p)))
    (hCovered : ∀ p (x : Wagon oldCarrier p),
      ∃ e ∈ wagonEdges p, x ∈ e)
    (T : UniformPrivateTemplate (WagonSum oldCarrier) X)
    (hEdges : T.localEdges = sumEdges oldCarrier wagonEdges)
    (p : P) (x : Wagon oldCarrier p) :
    (toPrivateWagonInput oldCarrier wagonEdges hCovered T hEdges).coordinate p x =
      T.star ⟨p, x⟩ := rfl

/-- A selected summand edge becomes precisely its original physical edge
on the old vertices; no extra old or private points are introduced. -/
theorem selected_edge_carrier
    (oldCarrier : P → Set V)
    (wagonEdges : ∀ p, Set (Set (Wagon oldCarrier p)))
    (hCovered : ∀ p (x : Wagon oldCarrier p),
      ∃ e ∈ wagonEdges p, x ∈ e)
    (T : UniformPrivateTemplate (WagonSum oldCarrier) X)
    (hEdges : T.localEdges = sumEdges oldCarrier wagonEdges)
    (p : P) (e : Set (Wagon oldCarrier p))
    (a : {a : Set X // a ∈ T.templateEdges})
    (ha : a.1 = coordinate oldCarrier T p '' e) :
    let U := toPrivateWagonInput oldCarrier wagonEdges hCovered T hEdges
    U.edgeCarrier (p, a) = (Sum.inl : V → U.Vertex) '' (Subtype.val '' e) := by
  let U := toPrivateWagonInput oldCarrier wagonEdges hCovered T hEdges
  change U.place p '' a.1 = (Sum.inl : V → U.Vertex) '' (Subtype.val '' e)
  rw [ha, Set.image_image, Set.image_image]
  apply Set.image_congr
  intro x _
  exact U.place_old p x

/-- The private construction now supplies all three scattering fields. -/
noncomputable def componentGeometry
    (oldCarrier : P → Set V)
    (wagonEdges : ∀ p, Set (Set (Wagon oldCarrier p)))
    (hCovered : ∀ p (x : Wagon oldCarrier p),
      ∃ e ∈ wagonEdges p, x ∈ e)
    (T : UniformPrivateTemplate (WagonSum oldCarrier) X)
    (hEdges : T.localEdges = sumEdges oldCarrier wagonEdges)
    {Q : Type v} (parent : P → Q) :
    OrderOneData.ComponentTargetGeometry
      ((toPrivateWagonInput oldCarrier wagonEdges hCovered T hEdges).data parent)
      PUnit.unit :=
  PrivateWagonInput.componentGeometry
    (toPrivateWagonInput oldCarrier wagonEdges hCovered T hEdges) parent

/-- Its actual private copies have exactly the old cross-wagon intersection. -/
theorem range_inter
    (oldCarrier : P → Set V)
    (wagonEdges : ∀ p, Set (Set (Wagon oldCarrier p)))
    (hCovered : ∀ p (x : Wagon oldCarrier p),
      ∃ e ∈ wagonEdges p, x ∈ e)
    (T : UniformPrivateTemplate (WagonSum oldCarrier) X)
    (hEdges : T.localEdges = sumEdges oldCarrier wagonEdges)
    (p q : P) (hpq : p ≠ q) :
    let U := toPrivateWagonInput oldCarrier wagonEdges hCovered T hEdges
    Set.range (U.place p) ∩ Set.range (U.place q) =
      (Sum.inl : V → U.Vertex) '' (oldCarrier p ∩ oldCarrier q) :=
  PrivateWagonInput.range_inter
    (toPrivateWagonInput oldCarrier wagonEdges hCovered T hEdges) p q hpq

open StructuralRamsey.RelStructure

variable {L : RelLanguage.{u}} {UA : Type v}

/-- Coverage of the summands covers the relational disjoint-sum target
whenever its actual support family is the tagged summand family. -/
theorem sum_support_covered
    (oldCarrier : P → Set V)
    (wagonEdges : ∀ p, Set (Set (Wagon oldCarrier p)))
    (hCovered : ∀ p (x : Wagon oldCarrier p),
      ∃ e ∈ wagonEdges p, x ∈ e)
    (A : RelStructure L UA) (W : RelStructure L (WagonSum oldCarrier))
    (hSupport : supportCopies A W = sumEdges oldCarrier wagonEdges) :
    ∀ w : WagonSum oldCarrier, ∃ a : Embedding A W, w ∈ copyCarrier a := by
  rintro ⟨p, x⟩
  obtain ⟨e, he, hx⟩ := hCovered p x
  have hSum : Sigma.mk p '' e ∈ supportCopies A W := by
    rw [hSupport]
    exact ⟨p, e, he, rfl⟩
  obtain ⟨a, ha⟩ := hSum
  refine ⟨a, ?_⟩
  rw [← ha]
  exact ⟨x, hx, rfl⟩

/-- Relational endpoint: an actual A-strong embedding of the disjoint
wagon sum supplies the direct private extension, without uniformization.
The support identity records what it means for W to be this disjoint sum;
it is not an output geometry assumption. -/
noncomputable def ofStrongEmbedding
    (oldCarrier : P → Set V)
    (wagonEdges : ∀ p, Set (Set (Wagon oldCarrier p)))
    (hCovered : ∀ p (x : Wagon oldCarrier p),
      ∃ e ∈ wagonEdges p, x ∈ e)
    (A : RelStructure L UA) (W : RelStructure L (WagonSum oldCarrier))
    (R : RelStructure L X)
    (hSupport : supportCopies A W = sumEdges oldCarrier wagonEdges)
    (c : Embedding W R) (hStrong : AStrong A R (copyCarrier c)) :
    PrivateWagonInput V P X :=
  toPrivateWagonInput oldCarrier wagonEdges hCovered
    (UniformPrivateTemplate.ofStrongEmbedding A W R c hStrong
      (sum_support_covered oldCarrier wagonEdges hCovered A W hSupport))
    hSupport

/-- The relational constructor uses precisely the restriction of c. -/
@[simp] theorem ofStrongEmbedding_coordinate
    (oldCarrier : P → Set V)
    (wagonEdges : ∀ p, Set (Set (Wagon oldCarrier p)))
    (hCovered : ∀ p (x : Wagon oldCarrier p),
      ∃ e ∈ wagonEdges p, x ∈ e)
    (A : RelStructure L UA) (W : RelStructure L (WagonSum oldCarrier))
    (R : RelStructure L X)
    (hSupport : supportCopies A W = sumEdges oldCarrier wagonEdges)
    (c : Embedding W R) (hStrong : AStrong A R (copyCarrier c))
    (p : P) (x : Wagon oldCarrier p) :
    (ofStrongEmbedding oldCarrier wagonEdges hCovered A W R hSupport c hStrong).coordinate
      p x = c ⟨p, x⟩ := rfl

end StructuralRamsey.Girth.CompactPrivateExtension
