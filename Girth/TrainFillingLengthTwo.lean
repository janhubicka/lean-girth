import Girth.TrainFillingPieceLift
import Girth.TrainFreshLocalSupreme

/-!
# Track C: full simultaneous supremeness for two-occurrence filled cycles

An acceptable two-occurrence cycle in an edge-linear pretrain contains a
real designated label. Consequently projection by the filling cover cannot
identify its adjacent labels. A2 and A3 are automatic at length two, so
projection needs neither contraction nor the false unrestricted reverse
pair-edge implication.

Apply the old system bound to the actual projected cycle. Its local pieces
lift by TrainFillingPieceLift. Any lifted long piece has both original
connectors as vertices, hence its wagon is absent from the entire source.
The checked all-length fresh-local assembly supplies a genuine global
supreme plan, not just a list of local pieces.

No source-length-three contraction or freshness argument is claimed here.
No appendix, new axioms, admissions, or changes to the ambient edge family.
-/

namespace StructuralRamsey.Girth
namespace OrderOneData

universe v
variable {V E I P : Type v} (D : OrderOneData V E I P)

/-- Edge linearity and A1 exclude every edge-only acceptable cycle of
length two. The vertex/vertex case uses linearity; a wagon/wagon edge
would have two different parents; mixed connectors have order one. -/
theorem BigCycle.two_has_designated_of_edge_linear
    (C : D.BigCycle 2) (hAccept : C.Acceptable)
    (hEdges : ∀ e f : E, e ≠ f →
      (D.edgeCarrier e ∩ D.edgeCarrier f).Subsingleton) :
    ∃ k : Fin 2, D.designated (C.label k) := by
  classical
  by_contra hNone
  have edgeLabel (k : Fin 2) : ∃ e : E, C.label k = Sum.inr e := by
    cases h : C.label k with
    | inl i =>
        exact False.elim (hNone ⟨k, by simp [designated, h]⟩)
    | inr e => exact ⟨e, rfl⟩
  obtain ⟨e, he⟩ := edgeLabel 0
  obtain ⟨f, hf⟩ := edgeLabel 1
  have hef : e ≠ f := by
    intro h
    apply C.adjacent_ne 0
    simpa [cyclicSucc, he, hf, h]
  have h00 : D.Incident (Sum.inr e) (C.connector 0) := by
    simpa only [he] using C.left_incident 0
  have h01 : D.Incident (Sum.inr e) (C.connector 1) := by
    simpa [cyclicSucc, he] using C.right_incident 1
  have h10 : D.Incident (Sum.inr f) (C.connector 0) := by
    simpa [cyclicSucc, hf] using C.right_incident 0
  have h11 : D.Incident (Sum.inr f) (C.connector 1) := by
    simpa only [hf] using C.left_incident 1
  cases hq0 : C.connector 0 with
  | inl x =>
      cases hq1 : C.connector 1 with
      | inl y =>
          have hxy : x ≠ y := by
            intro h
            have hIndex : (0 : Fin 2) = 1 :=
              C.connector_injective (by simp [hq0, hq1, h])
            exact (by decide : (0 : Fin 2) ≠ 1) hIndex
          apply hxy
          apply hEdges e f hef
          · exact ⟨by simpa [hq0, Incident, carrier] using h00,
              by simpa [hq0, Incident, carrier] using h10⟩
          · exact ⟨by simpa [hq1, Incident, carrier] using h01,
              by simpa [hq1, Incident, carrier] using h11⟩
      | inr p =>
          apply hNone
          apply hAccept.1
          simp [BigCycle.twiceOrder, Fin.sum_univ_two, cyclicSucc,
            hq0, hq1, connectorKind, twiceOccurrenceWeight]
  | inr p =>
      cases hq1 : C.connector 1 with
      | inl x =>
          apply hNone
          apply hAccept.1
          simp [BigCycle.twiceOrder, Fin.sum_univ_two, cyclicSucc,
            hq0, hq1, connectorKind, twiceOccurrenceWeight]
      | inr q =>
          have hp : D.Meets (Sum.inr e) p := by
            simpa only [hq0, Incident] using h00
          have hq : D.Meets (Sum.inr e) q := by
            simpa only [hq1, Incident] using h01
          obtain ⟨a, ha, hap⟩ := hp
          obtain ⟨b, hb, hbq⟩ := hq
          have hae : a = e := ha
          have hbe : b = e := hb
          subst a
          subst b
          have hpq : p = q := hap.symm.trans hbq
          have hIndex : (0 : Fin 2) = 1 :=
            C.connector_injective (by simp [hq0, hq1, hpq])
          exact (by decide : (0 : Fin 2) ≠ 1) hIndex

/-- At length two, a long piece's vertex boundaries exhaust the source
connector list. Every wagon is therefore fresh for that source. -/
theorem BigCycle.two_wagon_fresh_of_vertex_boundaries
    (C : D.BigCycle 2) (j : Fin 2) (x y : V)
    (hLeft : C.connector (trainCyclicPred j) = Sum.inl x)
    (hRight : C.connector j = Sum.inl y) (p : P) :
    ∀ t : Fin 2, C.connector t ≠ Sum.inr p := by
  intro t
  have ht : t = j ∨ t = trainCyclicPred j := by
    fin_cases t <;> fin_cases j <;> simp [trainCyclicPred]
  rcases ht with ht | ht
  · rw [ht, hRight]
    simp
  · rw [ht, hLeft]
    simp

end OrderOneData

namespace TrainFilling

universe v
variable {V I P : Type v} (F : TrainFilling V)
variable (copyCarrier : I → Set V)
variable (copyEdges : I → Set F.OldEdge) (parent : F.OldEdge → P)

local notation "Old" => F.oldData copyCarrier copyEdges parent
local notation "New" => F.filledData copyCarrier copyEdges parent

/-- Filling preserves the carrier of EVERY old wagon, not only that
of a single old edge. The parent labels are unchanged. -/
theorem filled_wagonVertex_iff (p : P) (x : V) :
    (New).WagonVertex p x ↔ (Old).WagonVertex p x := by
  constructor
  · rintro ⟨e, hp, hx⟩
    exact ⟨F.cover e, hp, F.contained e hx⟩
  · rintro ⟨f, hp, hx⟩
    obtain ⟨e, he, hxe⟩ := F.covering f x hx
    refine ⟨e, ?_, hxe⟩
    change parent (F.cover e) = p
    rw [he]
    exact hp

/-- Full filled pretrain linearity follows from new edge linearity and
old wagon linearity. No cycle-bound assumption on the output is used. -/
theorem filled_linearPretrain
    (hOld : (Old).LinearPretrain)
    (hEdges : ∀ e f : F.NewEdge, e ≠ f → (e.1 ∩ f.1).Subsingleton) :
    (New).LinearPretrain := by
  refine ⟨hEdges, ?_⟩
  intro p q hpq x hx y hy
  apply hOld.2 p q hpq
  · exact ⟨(F.filled_wagonVertex_iff copyCarrier copyEdges parent p x).mp hx.1,
      (F.filled_wagonVertex_iff copyCarrier copyEdges parent q x).mp hx.2⟩
  · exact ⟨(F.filled_wagonVertex_iff copyCarrier copyEdges parent p y).mp hy.1,
      (F.filled_wagonVertex_iff copyCarrier copyEdges parent q y).mp hy.2⟩

/-- Projection keeps designated indices and maps each physical edge to
its prescribed old cover; it never identifies the two sorts. -/
def projectLabel (a : I ⊕ F.NewEdge) : I ⊕ F.OldEdge :=
  Sum.map id F.cover a

theorem projectLabel_eq_designated_iff (a : I ⊕ F.NewEdge) (i : I) :
    F.projectLabel a = Sum.inl i ↔ a = Sum.inl i := by
  cases a <;> simp [projectLabel]

theorem projectLabel_ne_of_designated (a b : I ⊕ F.NewEdge)
    (hne : a ≠ b) (hDes : (New).designated a ∨ (New).designated b) :
    F.projectLabel a ≠ F.projectLabel b := by
  cases a <;> cases b <;>
    simp_all [projectLabel, OrderOneData.designated]

/-- Both kinds of actual incidence project; the reverse pair-edge
implication is deliberately absent. -/
theorem projectLabel_incident (a : I ⊕ F.NewEdge) (q : V ⊕ P)
    (h : (New).Incident a q) : (Old).Incident (F.projectLabel a) q := by
  cases a with
  | inl i =>
      cases q with
      | inl x => exact h
      | inr p =>
          obtain ⟨e, he, hp⟩ := h
          exact ⟨F.cover e, he, hp⟩
  | inr e =>
      cases q with
      | inl x => exact F.contained e h
      | inr p =>
          obtain ⟨f, hf, hp⟩ := h
          have hfe : f = e := hf
          subst f
          exact ⟨F.cover e, rfl, hp⟩

/-- A two-occurrence cycle containing a designated label projects to
an actual old BigCycle with exactly the same connector word. -/
def projectTwoCycle (C : (New).BigCycle 2)
    (hDes : ∃ k : Fin 2, (New).designated (C.label k)) : (Old).BigCycle 2 where
  length_ge_two := C.length_ge_two
  label := fun j => F.projectLabel (C.label j)
  connector := C.connector
  adjacent_ne := by
    intro j
    apply F.projectLabel_ne_of_designated copyCarrier copyEdges parent
      (C.label j) (C.label (cyclicSucc j)) (C.adjacent_ne j)
    obtain ⟨k, hk⟩ := hDes
    have hkpos : k = j ∨ k = cyclicSucc j := by
      fin_cases k <;> fin_cases j <;> simp [cyclicSucc]
    rcases hkpos with hkpos | hkpos
    · exact Or.inl (by simpa only [hkpos] using hk)
    · exact Or.inr (by simpa only [hkpos] using hk)
  connector_injective := C.connector_injective
  left_incident := fun j => F.projectLabel_incident copyCarrier copyEdges parent
    (C.label j) (C.connector j) (C.left_incident j)
  right_incident := fun j => F.projectLabel_incident copyCarrier copyEdges parent
    (C.label (cyclicSucc j)) (C.connector j) (C.right_incident j)

theorem projectTwoCycle_twiceOrder (C : (New).BigCycle 2)
    (hDes : ∃ k : Fin 2, (New).designated (C.label k)) :
    (F.projectTwoCycle copyCarrier copyEdges parent C hDes).twiceOrder =
      C.twiceOrder := rfl

/-- At length two A2 and A3 need no pair-edge reflection. A retained
designated occurrence gives A1 independently of the connector kinds. -/
theorem projectTwoCycle_acceptable (C : (New).BigCycle 2)
    (hDes : ∃ k : Fin 2, (New).designated (C.label k)) :
    (F.projectTwoCycle copyCarrier copyEdges parent C hDes).Acceptable := by
  let Z := F.projectTwoCycle copyCarrier copyEdges parent C hDes
  refine ⟨?_, (Old).twoCycle_A2 Z, (Old).twoCycle_A3 Z⟩
  intro _
  obtain ⟨k, hk⟩ := hDes
  refine ⟨k, ?_⟩
  cases hLabel : C.label k with
  | inl i =>
      simp [Z, projectTwoCycle, projectLabel, OrderOneData.designated, hLabel]
  | inr e => exact False.elim (by simpa [OrderOneData.designated, hLabel] using hk)

/-- Every acceptable two-occurrence filled cycle under the old cutoff
has a genuine simultaneous supreme plan. No projected cycle, replacement
plan, inserted-wagon freshness or output cycle is assumed. -/
theorem filled_two_supreme_of_fullSystemGirth
    {q : ℕ} (hOld : (Old).FullSystemGirthGT q)
    (hEdges : ∀ e f : F.NewEdge, e ≠ f → (e.1 ∩ f.1).Subsingleton)
    (C : (New).BigCycle 2) (hAccept : C.Acceptable)
    (hOrder : C.twiceOrder ≤ 2 * q) : C.HasSimultaneousSupreme := by
  have hNewLinear : (New).LinearPretrain :=
    F.filled_linearPretrain copyCarrier copyEdges parent hOld.1 hEdges
  have hDes : ∃ k : Fin 2, (New).designated (C.label k) :=
    C.two_has_designated_of_edge_linear New hAccept hEdges
  let Z := F.projectTwoCycle copyCarrier copyEdges parent C hDes
  have hZAccept : Z.Acceptable :=
    F.projectTwoCycle_acceptable copyCarrier copyEdges parent C hDes
  have hZOrder : Z.twiceOrder ≤ 2 * q := hOrder
  have hSup := hOld.2 2 Z hZAccept hZOrder
  obtain ⟨k, hk, hLocal⟩ := Z.localSupreme_of_simultaneous Old hSup
  have hSource : ∃ i : I, C.label k = Sum.inl i := by
    cases hLabel : C.label k with
    | inl i => exact ⟨i, rfl⟩
    | inr e =>
        exact False.elim (by
          simpa [Z, projectTwoCycle, projectLabel,
            OrderOneData.designated, hLabel] using hk)
  obtain ⟨i, hki⟩ := hSource
  have hkNew : (New).designated (C.label k) := by
    simp [OrderOneData.designated, hki]
  have hAt : C.HasSupremeAt New k := by
    apply C.hasSupremeAt_of_fresh_local_witnesses New hAccept hNewLinear k hkNew
    intro j hNe
    have hZNe : Z.label j ≠ Z.label k := by
      change F.projectLabel (C.label j) ≠ F.projectLabel (C.label k)
      rw [hki]
      intro hEq
      apply hNe
      exact ((F.projectLabel_eq_designated_iff (C.label j) i).mp hEq).trans hki.symm
    have hPiece :
        (Old).ShortPiece (.inl i) (C.connector (trainCyclicPred j)) (C.connector j) ∨
        (Old).LongPiece (.inl i) (C.connector (trainCyclicPred j)) (C.connector j) := by
      simpa [Z, projectTwoCycle, hki, projectLabel]
        using hLocal j hZNe
    have hBoundaryNe : C.connector (trainCyclicPred j) ≠ C.connector j := by
      intro h
      have hj := C.connector_injective h
      have hn : trainCyclicPred j ≠ j := by fin_cases j <;> decide
      exact hn hj
    have hLift :
        (New).ShortPiece (.inl i) (C.connector (trainCyclicPred j)) (C.connector j) ∨
        (New).LongPiece (.inl i) (C.connector (trainCyclicPred j)) (C.connector j) := by
      rcases hPiece with hs | hl
      · exact F.shortPiece_lift copyCarrier copyEdges parent hOld.1.1 i
          _ _ hBoundaryNe hs
      · exact Or.inr (F.longPiece_lift copyCarrier copyEdges parent i _ _ hl)
    rcases hLift with ⟨e, he, hl, hr⟩ | hLong
    · left
      refine ⟨e, ?_, hl, hr⟩
      simpa only [hki] using he
    · obtain ⟨x, y, p, e, f, hl, hr, he, hf, hef, hep, hfp, hx, hy, hPair⟩ := hLong
      right
      refine ⟨e, f, p, ?_, ?_⟩
      · refine ⟨x, y, hl, hr, ?_, ?_, hef, hep, hfp, hx, hy, hPair⟩
        · simpa only [hki] using he
        · simpa only [hki] using hf
      · exact C.two_wagon_fresh_of_vertex_boundaries New j x y hl hr p
  exact C.hasSimultaneousSupreme_of_hasSupremeAt New k hAt

end TrainFilling
end StructuralRamsey.Girth
