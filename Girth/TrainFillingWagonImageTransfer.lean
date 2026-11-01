import Girth.TrainSupremePlanTransport
import Girth.TrainFreshLocalSupreme
import Girth.TrainOptionalFreshnessConverse

set_option Elab.async false

/-!
# Full system girth reflects through a faithful renaming of wagon labels

Only the wagon sort changes. Vertices, ambient edges, designated labels,
carriers and edge ownership are literal. An injective wagon map is enough:
unused labels in its codomain have empty carriers, so their A3 obligations
are vacuous. Surjectivity and nonempty edge carriers are NOT needed.

Map an acceptable source cycle into the old-labelled system, use its full
system bound, and reflect every chosen physical piece. The wagon of a long
piece is in the image because it is the parent of its first actual edge.
The OLD globally legal word supplies freshness; the checked source-side
assembler then constructs a genuine global supreme plan.

This is the missing representation step between the generic filling theorem
and the actual quotient-wagon cuts of the restored train. It does not
construct any new Ramsey witness or assert a bound above its universal top.
-/

namespace StructuralRamsey.Girth.OrderOneData

universe v
variable {V E I P Q : Type v} (D : OrderOneData V E I P) (φ : P ↪ Q)

/-- Retain every physical datum and inject only the wagon names. -/
def wagonImage : OrderOneData V E I Q where
  edgeCarrier := D.edgeCarrier
  copyCarrier := D.copyCarrier
  copyEdges := D.copyEdges
  parent := fun e => φ (D.parent e)

/-- Wagon renaming does not change which labels are designated. -/
private theorem wagonImage_designated (a : I ⊕ E) :
    (D.wagonImage φ).designated a ↔ D.designated a := by
  cases a <;> rfl

/-- Physical edge ownership is literal even though the wagon sort changes. -/
private theorem wagonImage_edges (a : I ⊕ E) :
    (D.wagonImage φ).edges a = D.edges a := by
  cases a <;> rfl

private theorem wagonImage_vertex (p : P) (x : V) :
    (D.wagonImage φ).WagonVertex (φ p) x ↔ D.WagonVertex p x := by
  simp only [WagonVertex, wagonImage, φ.injective.eq_iff]

private theorem wagonImage_incident (a : I ⊕ E) (z : V ⊕ P) :
    (D.wagonImage φ).Incident a (Sum.map id φ z) ↔ D.Incident a z := by
  cases a <;> cases z <;>
    simp [Incident, carrier, Meets, edges, wagonImage, φ.injective.eq_iff]

/-- The faithful parent renaming is a literal physical map, not an
identification of distinct wagons with equal vertex carriers. -/
def wagonImage_physicalMap : LiteralPhysicalMap D (D.wagonImage φ) where
  vertex := Function.Embedding.refl V
  edge := Function.Embedding.refl E
  designated := Function.Embedding.refl I
  wagon := φ
  incident := by
    intro a z hz
    have h := (wagonImage_incident D φ a z).mpr hz
    cases a <;> cases z <;> exact h
  source_edge := by
    intro a e he
    cases a <;> exact he
  parent := fun _ => rfl
  no_new_pair := fun _ _ _ h => h

private theorem imageCycle_label {n : ℕ} (C : D.BigCycle n) (j : Fin n) :
    ((D.wagonImage_physicalMap φ).mapBigCycle C).label j = C.label j := by
  change Sum.map id id (C.label j) = C.label j
  cases C.label j <;> rfl

private theorem imageCycle_vertex {n : ℕ} (C : D.BigCycle n) (j : Fin n) (x : V) :
    ((D.wagonImage_physicalMap φ).mapBigCycle C).connector j = Sum.inl x ↔
      C.connector j = Sum.inl x := by
  change Sum.map id φ (C.connector j) = Sum.inl x ↔ _
  cases C.connector j <;> simp

private theorem imageCycle_wagon {n : ℕ} (C : D.BigCycle n) (j : Fin n) (p : P) :
    ((D.wagonImage_physicalMap φ).mapBigCycle C).connector j = Sum.inr (φ p) ↔
      C.connector j = Sum.inr p := by
  change Sum.map id φ (C.connector j) = Sum.inr (φ p) ↔ _
  cases C.connector j <;> simp [φ.injective.eq_iff]

private theorem imageCycle_inWagonAt {n : ℕ} (C : D.BigCycle n) (j : Fin n) (p : P) :
    ((D.wagonImage_physicalMap φ).mapBigCycle C).InWagonAt (φ p) j ↔
      C.InWagonAt p j := by
  simp only [BigCycle.InWagonAt, imageCycle_vertex, wagonImage_vertex]

/-- Faithful wagon renaming retains the exact connector-kind word. -/
theorem wagonImage_cycle_twiceOrder {n : ℕ} (C : D.BigCycle n) :
    ((D.wagonImage_physicalMap φ).mapBigCycle C).twiceOrder = C.twiceOrder := by
  unfold BigCycle.twiceOrder
  apply Finset.sum_congr rfl
  intro j _
  change twiceOccurrenceWeight (connectorKind (Sum.map id φ (C.connector j)))
      (connectorKind (Sum.map id φ (C.connector (cyclicSucc j)))) = _
  cases C.connector j <;> cases C.connector (cyclicSucc j) <;> rfl

/-- A1--A3 are preserved even with unused codomain wagon labels.
Every contact with a codomain wagon supplies an actual parent preimage. -/
theorem wagonImage_cycle_acceptable {n : ℕ} (C : D.BigCycle n)
    (h : C.Acceptable) :
    ((D.wagonImage_physicalMap φ).mapBigCycle C).Acceptable := by
  refine ⟨?_, ⟨?_, ?_⟩, ?_⟩
  · intro ho
    obtain ⟨j, hj⟩ := h.1 ((D.wagonImage_cycle_twiceOrder φ C).symm.trans ho)
    refine ⟨j, ?_⟩
    rw [imageCycle_label]
    exact hj
  · intro i q hi j hj
    change Sum.map id φ (C.connector i) = Sum.inr q at hi
    cases hz : C.connector i with
    | inl x => rw [hz] at hi; cases hi
    | inr p =>
        rw [hz] at hi
        have hp : φ p = q := Sum.inr.inj hi
        subst q
        exact h.2.1.1 i p hz j ((imageCycle_inWagonAt D φ C j p).mp hj)
  · intro i q x y hi hx hy hne hqx hqy hpair
    change Sum.map id φ (C.connector i) = Sum.inr q at hi
    cases hz : C.connector i with
    | inl z => rw [hz] at hi; cases hi
    | inr p =>
        rw [hz] at hi
        have hp : φ p = q := Sum.inr.inj hi
        subst q
        exact h.2.1.2 i p x y hz
          ((imageCycle_vertex D φ C _ x).mp hx)
          ((imageCycle_vertex D φ C _ y).mp hy) hne
          ((wagonImage_vertex D φ p x).mp hqx)
          ((wagonImage_vertex D φ p y).mp hqy) hpair
  · intro q hq
    by_cases hRange : ∃ p : P, φ p = q
    · obtain ⟨p, rfl⟩ := hRange
      obtain ⟨i, hi⟩ := h.2.2 p (fun j hj =>
        hq j ((imageCycle_wagon D φ C j p).mpr hj))
      exact ⟨i, fun j hj => hi j ((imageCycle_inWagonAt D φ C j p).mp hj)⟩
    · refine ⟨⟨0, by have := C.length_ge_two; omega⟩, ?_⟩
      rintro j ⟨x, _hx, e, hep, _hxe⟩
      exact False.elim (hRange ⟨D.parent e, hep⟩)

private theorem linearPretrain_of_wagonImage
    (h : (D.wagonImage φ).LinearPretrain) : D.LinearPretrain := by
  refine ⟨h.1, ?_⟩
  intro p q hpq x hx y hy
  apply h.2 (φ p) (φ q) (fun heq => hpq (φ.injective heq))
  · exact ⟨(wagonImage_vertex D φ p x).mpr hx.1,
      (wagonImage_vertex D φ q x).mpr hx.2⟩
  · exact ⟨(wagonImage_vertex D φ p y).mpr hy.1,
      (wagonImage_vertex D φ q y).mpr hy.2⟩

/-- A full bound on the faithfully renamed system yields a full bound
on the original wagon sort. Global source supremeness is constructed;
no surjectivity, nonempty-edge or output-plan hypothesis is used. -/
theorem fullSystemGirth_of_wagonImage {q : ℕ}
    (h : (D.wagonImage φ).FullSystemGirthGT q) : D.FullSystemGirthGT q := by
  have hLinear : D.LinearPretrain := linearPretrain_of_wagonImage D φ h.1
  refine ⟨hLinear, ?_⟩
  intro n C hAccept hOrder
  let Z := (D.wagonImage_physicalMap φ).mapBigCycle C
  obtain ⟨k, hk, pieces, hPlan, m, B, hWord⟩ :=
    h.2 n Z (D.wagonImage_cycle_acceptable φ C hAccept)
      (by rw [D.wagonImage_cycle_twiceOrder φ C]; exact hOrder)
  have hFresh := Z.longWagons_fresh_of_literalBigCycle (D.wagonImage φ) B pieces hWord
  have hkD : D.designated (C.label k) := by
    simpa only [Z, imageCycle_label, wagonImage_designated] using hk
  apply C.hasSimultaneousSupreme_of_hasSupremeAt D k
  apply C.hasSupremeAt_of_fresh_local_witnesses D hAccept hLinear k hkD
  intro j hNe
  have hZNe : Z.label j ≠ Z.label k := by
    simpa only [Z, imageCycle_label] using hNe
  have hj := (hPlan j).2 hZNe
  cases hp : pieces j with
  | keep => simp only [hp] at hj
  | short e =>
      have hs : Z.ShortValid (D.wagonImage φ) k j e := by
        simpa only [hp] using hj
      left
      refine ⟨e, ?_, ?_, ?_⟩
      · simpa only [Z, imageCycle_label, wagonImage_edges] using hs.1
      · exact (wagonImage_incident D φ (.inr e) _).mp hs.2.1
      · exact (wagonImage_incident D φ (.inr e) _).mp hs.2.2
  | long e p f =>
      have hl : Z.LongValid (D.wagonImage φ) k j e p f := by
        simpa only [hp] using hj
      obtain ⟨x, y, hx, hy, he, hf, hef, hep, hfp, hxe, hyf, hPair⟩ := hl
      have hParent : D.parent f = D.parent e := φ.injective (hfp.trans hep.symm)
      right
      refine ⟨e, f, D.parent e, ?_, ?_⟩
      · refine ⟨x, y,
          (imageCycle_vertex D φ C _ x).mp hx,
          (imageCycle_vertex D φ C _ y).mp hy, ?_, ?_, hef, rfl, hParent,
          hxe, hyf, hPair⟩
        · simpa only [Z, imageCycle_label, wagonImage_edges] using he
        · simpa only [Z, imageCycle_label, wagonImage_edges] using hf
      · intro t ht
        apply hFresh j e p f hp t
        change Sum.map id φ (C.connector t) = Sum.inr p
        rw [ht]
        exact congrArg Sum.inr hep

end StructuralRamsey.Girth.OrderOneData
