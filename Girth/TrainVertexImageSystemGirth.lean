import Girth.TrainSupremePlanTransport
import Girth.TrainInteriorParentQuotientBridge

set_option Elab.async false

/-!
# System girth under an injective change of vertex representation

Embedding the vertices changes neither the physical edge labels nor their
designated ownership and wagon parents. Every vertex connector of an image
cycle lies in the image, because it is incident with a labelled carrier.
Thus every image cycle pulls back, with exactly the same order and A1--A3.
The existing physical-map theorem then transports the entire simultaneous
replacement word, including its genuine resulting BigCycle.

Unused vertices outside the image cause no problem. No nonempty vertex
type, finite support, extra cycle bound or output linearity is assumed.
This supplies intrinsic core-witness hypotheses for the actual attachment;
it is not a theorem about replacing or combining different physical copies.
-/

namespace StructuralRamsey.Girth
namespace OrderOneData

universe v
variable {V W E I P : Type v} (D : OrderOneData V E I P)
variable (φ : V ↪ W)

/-- Change only the vertex representation. All three sorts of physical
labels, edge ownership and quotient parents remain literal. -/
def vertexImage : OrderOneData W E I P where
  edgeCarrier := fun e => φ '' D.edgeCarrier e
  copyCarrier := fun i => φ '' D.copyCarrier i
  copyEdges := D.copyEdges
  parent := D.parent

private theorem image_carrier (a : I ⊕ E) :
    (D.vertexImage φ).carrier a = φ '' D.carrier a := by
  cases a <;> rfl

private theorem mem_image_carrier (a : I ⊕ E) (x : V) :
    φ x ∈ (D.vertexImage φ).carrier a ↔ x ∈ D.carrier a := by
  rw [image_carrier]
  constructor
  · rintro ⟨y, hy, hyx⟩
    exact (φ.injective hyx) ▸ hy
  · intro hx
    exact ⟨x, hx, rfl⟩

private theorem image_meets (a : I ⊕ E) (p : P) :
    (D.vertexImage φ).Meets a p ↔ D.Meets a p := by
  cases a <;> rfl

private theorem image_incident (a : I ⊕ E) (z : V ⊕ P) :
    (D.vertexImage φ).Incident a (Sum.map φ id z) ↔ D.Incident a z := by
  cases z with
  | inl x => exact mem_image_carrier D φ a x
  | inr p => exact image_meets D φ a p

private theorem image_wagon (p : P) (x : V) :
    (D.vertexImage φ).WagonVertex p (φ x) ↔ D.WagonVertex p x := by
  simp only [WagonVertex, vertexImage, Set.mem_image,
    φ.injective.eq_iff, exists_eq_right]

private theorem image_pair (x y : V) :
    (D.vertexImage φ).PairEdge (φ x) (φ y) ↔ D.PairEdge x y := by
  simp only [PairEdge, vertexImage, Set.mem_image,
    φ.injective.eq_iff, exists_eq_right]

/-- The exact vertex-image construction is a literal physical map.
Pair-edge reflection follows from injectivity, with no strongness input. -/
def vertexImage_physicalMap : LiteralPhysicalMap D (D.vertexImage φ) where
  vertex := φ
  edge := Function.Embedding.refl E
  designated := Function.Embedding.refl I
  wagon := Function.Embedding.refl P
  incident := by
    intro a z hz
    have h := (image_incident D φ a z).mpr hz
    cases a <;> cases z <;> exact h
  source_edge := by
    intro a e he
    cases a <;> exact he
  parent := fun _ => rfl
  no_new_pair := fun x y _ => (image_pair D φ x y).mp

private theorem map_label (a : I ⊕ E) :
    (D.vertexImage_physicalMap φ).mapLabel a = a := by
  cases a <;> rfl

private theorem map_connector (z : V ⊕ P) :
    (D.vertexImage_physicalMap φ).mapConnector z = Sum.map φ id z := by
  cases z <;> rfl

private theorem connector_kind_image (z : V ⊕ P) :
    connectorKind (Sum.map φ id z) = connectorKind z := by
  cases z <;> rfl

private theorem pull_cycle {n : ℕ}
    (C : (D.vertexImage φ).BigCycle n) :
    ∃ Z : D.BigCycle n,
      (∀ j, Z.label j = C.label j) ∧
      (∀ j, Sum.map φ id (Z.connector j) = C.connector j) := by
  classical
  have hRange : ∀ j : Fin n,
      ∃ z : V ⊕ P, Sum.map φ id z = C.connector j := by
    intro j
    cases hz : C.connector j with
    | inr p => exact ⟨.inr p, rfl⟩
    | inl x =>
        have hx := C.left_incident j
        rw [hz] at hx
        change x ∈ (D.vertexImage φ).carrier (C.label j) at hx
        rw [image_carrier] at hx
        obtain ⟨y, _, rfl⟩ := hx
        exact ⟨.inl y, rfl⟩
  choose g hg using hRange
  let Z : D.BigCycle n := {
    length_ge_two := C.length_ge_two
    label := C.label
    connector := g
    adjacent_ne := C.adjacent_ne
    connector_injective := by
      intro j k h
      apply C.connector_injective
      rw [← hg j, ← hg k, h]
    left_incident := by
      intro j
      apply (image_incident D φ (C.label j) (g j)).mp
      rw [hg j]
      exact C.left_incident j
    right_incident := by
      intro j
      apply (image_incident D φ (C.label (cyclicSucc j)) (g j)).mp
      rw [hg j]
      exact C.right_incident j }
  exact ⟨Z, fun _ => rfl, hg⟩

private theorem order_pull {n : ℕ}
    (Z : D.BigCycle n) (C : (D.vertexImage φ).BigCycle n)
    (hc : ∀ j, Sum.map φ id (Z.connector j) = C.connector j) :
    Z.twiceOrder = C.twiceOrder := by
  unfold BigCycle.twiceOrder
  apply Finset.sum_congr rfl
  intro j _
  rw [← hc j, ← hc (cyclicSucc j),
    connector_kind_image, connector_kind_image]

private theorem inWagon_image {n : ℕ}
    (Z : D.BigCycle n) (C : (D.vertexImage φ).BigCycle n)
    (hc : ∀ j, Sum.map φ id (Z.connector j) = C.connector j)
    (p : P) (j : Fin n) :
    Z.InWagonAt p j ↔ C.InWagonAt p j := by
  constructor
  · rintro ⟨x, hx, hp⟩
    refine ⟨φ x, ?_, (image_wagon D φ p x).mpr hp⟩
    rw [← hc j, hx]
    rfl
  · rintro ⟨x, hx, hp⟩
    cases hz : Z.connector j with
    | inl y =>
        have heq : φ y = x := by
          have hh := hc j
          rw [hz, hx] at hh
          exact Sum.inl.inj hh
        subst x
        exact ⟨y, hz, (image_wagon D φ p y).mp hp⟩
    | inr q =>
        have hh := hc j
        rw [hz, hx] at hh
        cases hh

private theorem wagon_connector_iff {n : ℕ}
    (Z : D.BigCycle n) (C : (D.vertexImage φ).BigCycle n)
    (hc : ∀ j, Sum.map φ id (Z.connector j) = C.connector j)
    (j : Fin n) (p : P) :
    Z.connector j = Sum.inr p ↔ C.connector j = Sum.inr p := by
  rw [← hc j]
  cases Z.connector j <;> simp

private theorem acceptable_pull {n : ℕ}
    (Z : D.BigCycle n) (C : (D.vertexImage φ).BigCycle n)
    (hl : ∀ j, Z.label j = C.label j)
    (hc : ∀ j, Sum.map φ id (Z.connector j) = C.connector j)
    (h : C.Acceptable) : Z.Acceptable := by
  refine ⟨?_, ⟨?_, ?_⟩, ?_⟩
  · intro ho
    obtain ⟨j, hj⟩ := h.1 ((order_pull D φ Z C hc).symm.trans ho)
    refine ⟨j, ?_⟩
    rw [hl j]
    exact hj
  · intro i p hi j hj
    exact h.2.1.1 i p ((wagon_connector_iff D φ Z C hc i p).mp hi)
      j ((inWagon_image D φ Z C hc p j).mp hj)
  · intro i p x y hi hx hy hne hpx hpy hpair
    have hx' : C.connector (trainCyclicPred i) = Sum.inl (φ x) := by
      rw [← hc (trainCyclicPred i), hx]
      rfl
    have hy' : C.connector (cyclicSucc i) = Sum.inl (φ y) := by
      rw [← hc (cyclicSucc i), hy]
      rfl
    exact h.2.1.2 i p (φ x) (φ y)
      ((wagon_connector_iff D φ Z C hc i p).mp hi) hx' hy' hne
      ((image_wagon D φ p x).mpr hpx)
      ((image_wagon D φ p y).mpr hpy)
      ((image_pair D φ x y).mpr hpair)
  · intro p hp
    obtain ⟨i, hi⟩ := h.2.2 p (fun j hj =>
      hp j ((wagon_connector_iff D φ Z C hc j p).mpr hj))
    exact ⟨i, fun j hj => hi j ((inWagon_image D φ Z C hc p j).mp hj)⟩

private theorem image_cycle_eq {n : ℕ}
    (Z : D.BigCycle n) (C : (D.vertexImage φ).BigCycle n)
    (hl : ∀ j, Z.label j = C.label j)
    (hc : ∀ j, Sum.map φ id (Z.connector j) = C.connector j) :
    (D.vertexImage_physicalMap φ).mapBigCycle Z = C := by
  have hl' : ((D.vertexImage_physicalMap φ).mapBigCycle Z).label =
      C.label := by
    funext j
    change (D.vertexImage_physicalMap φ).mapLabel (Z.label j) = C.label j
    rw [map_label, hl j]
  have hc' : ((D.vertexImage_physicalMap φ).mapBigCycle Z).connector =
      C.connector := by
    funext j
    change (D.vertexImage_physicalMap φ).mapConnector (Z.connector j) =
      C.connector j
    rw [map_connector, hc j]
  generalize (D.vertexImage_physicalMap φ).mapBigCycle Z = K at *
  cases K
  cases C
  cases hl'
  cases hc'
  rfl

/-- Injective vertex images preserve both physical edge linearity and
complete wagon linearity. No label is identified by carrier equality. -/
theorem vertexImage_linearPretrain (h : D.LinearPretrain) :
    (D.vertexImage φ).LinearPretrain := by
  constructor
  · intro e f hef x hx y hy
    obtain ⟨a, hae, rfl⟩ := hx.1
    obtain ⟨b, hbe, rfl⟩ := hy.1
    have haf : a ∈ D.edgeCarrier f :=
      (mem_image_carrier D φ (.inr f) a).mp hx.2
    have hbf : b ∈ D.edgeCarrier f :=
      (mem_image_carrier D φ (.inr f) b).mp hy.2
    exact congrArg φ (h.1 e f hef ⟨hae, haf⟩ ⟨hbe, hbf⟩)
  · intro p q hpq x hx y hy
    obtain ⟨e, hep, a, hae, rfl⟩ := hx.1
    obtain ⟨f, hfp, b, hbf, rfl⟩ := hy.1
    have hap : D.WagonVertex p a := ⟨e, hep, hae⟩
    have hbp : D.WagonVertex p b := ⟨f, hfp, hbf⟩
    have haq : D.WagonVertex q a := (image_wagon D φ q a).mp hx.2
    have hbq : D.WagonVertex q b := (image_wagon D φ q b).mp hy.2
    exact congrArg φ (h.2 p q hpq ⟨hap, haq⟩ ⟨hbp, hbq⟩)

/-- Intrinsic full system girth supplies full system girth on the image.
The proof pulls back each acceptable cycle and maps its entire globally
legal supreme plan, retaining the exact cutoff and all physical labels. -/
theorem vertexImage_fullSystemGirth {q : ℕ} (h : D.FullSystemGirthGT q) :
    (D.vertexImage φ).FullSystemGirthGT q := by
  refine ⟨D.vertexImage_linearPretrain φ h.1, ?_⟩
  intro n C ha ho
  obtain ⟨Z, hl, hc⟩ := pull_cycle D φ C
  have hs : Z.HasSimultaneousSupreme :=
    h.2 n Z (acceptable_pull D φ Z C hl hc ha)
      (by rw [order_pull D φ Z C hc]; exact ho)
  have hMapped := (D.vertexImage_physicalMap φ).hasSimultaneousSupreme_map Z hs
  rw [image_cycle_eq D φ Z C hl hc] at hMapped
  exact hMapped

end OrderOneData

universe v

private theorem sharedWitness_vertexImage_eq
    {V W E I S : Type v} {m : ℕ}
    (T : EdgeTrainLevels E m) (μ : Fin (m + 1))
    (inCore : I → S ↪ E) (edge : E → Set V) (φ : V ↪ W) :
    sharedWitnessOrderOneData T μ inCore (fun e => φ '' edge e) =
      (sharedWitnessOrderOneData T μ inCore edge).vertexImage φ := by
  unfold sharedWitnessOrderOneData OrderOneData.vertexImage
  congr 1
  funext i
  ext x
  constructor
  · rintro ⟨s, y, hy, rfl⟩
    exact ⟨y, ⟨s, hy⟩, rfl⟩
  · rintro ⟨y, ⟨s, hy⟩, rfl⟩
    exact ⟨s, y, hy, rfl⟩

/-- The intrinsic shared-witness linearity premise transports to its
injective vertex image with exactly the same edge and wagon labels. -/
theorem sharedWitnessOrderOneData_linearPretrain_vertexImage
    {V W E I S : Type v} {m : ℕ}
    (T : EdgeTrainLevels E m) (μ : Fin (m + 1))
    (inCore : I → S ↪ E) (edge : E → Set V) (φ : V ↪ W)
    (h : (sharedWitnessOrderOneData T μ inCore edge).LinearPretrain) :
    (sharedWitnessOrderOneData T μ inCore
      (fun e => φ '' edge e)).LinearPretrain := by
  rw [sharedWitness_vertexImage_eq]
  exact OrderOneData.vertexImage_linearPretrain _ φ h

/-- Full intrinsic shared-witness system girth transports to the actual
core-image representation, at the identical numerical cutoff. -/
theorem sharedWitnessOrderOneData_fullSystemGirth_vertexImage
    {V W E I S : Type v} {m : ℕ}
    (T : EdgeTrainLevels E m) (μ : Fin (m + 1))
    (inCore : I → S ↪ E) (edge : E → Set V) (φ : V ↪ W)
    {q : ℕ}
    (h : (sharedWitnessOrderOneData T μ inCore edge).FullSystemGirthGT q) :
    (sharedWitnessOrderOneData T μ inCore
      (fun e => φ '' edge e)).FullSystemGirthGT q := by
  rw [sharedWitness_vertexImage_eq]
  exact OrderOneData.vertexImage_fullSystemGirth _ φ h

end StructuralRamsey.Girth
