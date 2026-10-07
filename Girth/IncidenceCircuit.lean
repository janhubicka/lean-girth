import Girth.ForestIncidenceAcyclic
import Mathlib.Data.List.ChainOfFn
import Mathlib.Logic.Equiv.Fin.Basic

/-! # Circuits from cyclic incidence data

After compressing maximal runs of a Berge cycle through standard pictures, the
circulation proof obtains a cyclic sequence of local-copy labels and connector
vertices. Connector vertices are distinct and the labels on the two sides of
each connector differ. This already gives a nonempty trail in the labelled
incidence graph; no shortest-subwalk minimization is needed.
-/

namespace StructuralRamsey.Girth

universe v
variable {W E : Type v}

/-- Cyclic incidence data. Label `i` and its cyclic successor both contain
connector `i`. Labels themselves may repeat nonconsecutively. -/
structure CyclicIncidenceData (edge : E → Set W) where
  length : ℕ
  hlength : 2 ≤ length
  label : Fin length → E
  connector : Fin length → W
  connector_injective : Function.Injective connector
  label_ne_succ : ∀ i, label i ≠ label (cyclicSucc i)
  left_mem : ∀ i, connector i ∈ edge (label i)
  right_mem : ∀ i, connector i ∈ edge (label (cyclicSucc i))

namespace CyclicIncidenceData

variable {edge : E → Set W}

/-- First and last cyclic indices, made explicit so we never rely on a
`NeZero` instance inferred from inequalities. -/
theorem length_pos (d : CyclicIncidenceData edge) : 0 < d.length :=
  lt_of_lt_of_le (by decide) d.hlength

theorem dartLength_pos (d : CyclicIncidenceData edge) :
    0 < d.length * 2 :=
  Nat.mul_pos d.length_pos (by decide)

def zeroIndex (d : CyclicIncidenceData edge) : Fin d.length :=
  ⟨0, d.length_pos⟩

def lastIndex (d : CyclicIncidenceData edge) : Fin d.length :=
  ⟨d.length - 1, Nat.sub_lt d.length_pos (by decide)⟩

def zeroDartIndex (d : CyclicIncidenceData edge) : Fin (d.length * 2) :=
  ⟨0, d.dartLength_pos⟩

def lastDartIndex (d : CyclicIncidenceData edge) : Fin (d.length * 2) :=
  ⟨d.length * 2 - 1,
    Nat.sub_lt d.dartLength_pos (by decide)⟩

/-- The first incidence dart at connector `i`: label `i` to connector
`i`. -/
def leftDart (d : CyclicIncidenceData edge) (i : Fin d.length) :
    (boundaryIncidenceGraph edge).Dart :=
  ⟨(Sum.inl (d.label i), Sum.inr (d.connector i)),
    (boundaryIncidenceGraph_adj_left_right
      edge (d.label i) (d.connector i)).2 (d.left_mem i)⟩

/-- The second incidence dart at connector `i`: connector `i` to the
cyclic successor label. -/
def rightDart (d : CyclicIncidenceData edge) (i : Fin d.length) :
    (boundaryIncidenceGraph edge).Dart :=
  ⟨(Sum.inr (d.connector i), Sum.inl (d.label (cyclicSucc i))),
    (boundaryIncidenceGraph_adj_right_left
      edge (d.label (cyclicSucc i)) (d.connector i)).2 (d.right_mem i)⟩

/-- Flatten the two incidence darts at each connector in cyclic order. -/
def alternatingDart
    (d : CyclicIncidenceData edge)
    (k : Fin (d.length * 2)) :
    (boundaryIncidenceGraph edge).Dart :=
  let q : Fin d.length × Fin 2 :=
    (finProdFinEquiv (m := d.length) (n := 2)).symm k
  if q.2.1 = 0 then leftDart d q.1 else rightDart d q.1

@[simp]
theorem alternatingDart_pair_zero
    (d : CyclicIncidenceData edge) (i : Fin d.length) :
    alternatingDart d
        (finProdFinEquiv (m := d.length) (n := 2)
          (i, (0 : Fin 2))) =
      leftDart d i := by
  simp [alternatingDart]

@[simp]
theorem alternatingDart_pair_one
    (d : CyclicIncidenceData edge) (i : Fin d.length) :
    alternatingDart d
        (finProdFinEquiv (m := d.length) (n := 2)
          (i, (1 : Fin 2))) =
      rightDart d i := by
  simp [alternatingDart]

/-- Consecutive flattened darts join. -/
theorem alternatingDarts_chain
    (d : CyclicIncidenceData edge) :
    (List.ofFn (alternatingDart d)).IsChain
      (boundaryIncidenceGraph edge).DartAdj := by
  rw [List.isChain_ofFn]
  intro k hk
  let k0 : Fin (d.length * 2) := ⟨k, by omega⟩
  let k1 : Fin (d.length * 2) := ⟨k + 1, hk⟩
  let q : Fin d.length × Fin 2 :=
    (finProdFinEquiv (m := d.length) (n := 2)).symm k0
  have hq :
      finProdFinEquiv (m := d.length) (n := 2) q = k0 :=
    Equiv.apply_symm_apply _ k0
  have hqval :
      q.2.1 + 2 * q.1.1 = k := by
    have h := congrArg Fin.val hq
    simpa [q, k0, finProdFinEquiv] using h
  by_cases hzero : q.2.1 = 0
  · have hq0 : q.2 = (0 : Fin 2) := Fin.ext hzero
    have hk0 :
        k0 =
          finProdFinEquiv (m := d.length) (n := 2)
            (q.1, (0 : Fin 2)) := by
      apply Fin.ext
      simp [k0, finProdFinEquiv]
      omega
    have hk1 :
        k1 =
          finProdFinEquiv (m := d.length) (n := 2)
            (q.1, (1 : Fin 2)) := by
      apply Fin.ext
      simp [k1, finProdFinEquiv]
      omega
    change
      (boundaryIncidenceGraph edge).DartAdj
        (alternatingDart d k0) (alternatingDart d k1)
    rw [hk0, hk1, alternatingDart_pair_zero, alternatingDart_pair_one]
    rfl
  · have hone : q.2.1 = 1 := by omega
    have hq1 : q.2 = (1 : Fin 2) := Fin.ext hone
    have hi1 : q.1.1 + 1 < d.length := by
      omega
    let i1 : Fin d.length := ⟨q.1.1 + 1, hi1⟩
    have hk0 :
        k0 =
          finProdFinEquiv (m := d.length) (n := 2)
            (q.1, (1 : Fin 2)) := by
      apply Fin.ext
      simp [k0, finProdFinEquiv]
      omega
    have hk1 :
        k1 =
          finProdFinEquiv (m := d.length) (n := 2)
            (i1, (0 : Fin 2)) := by
      apply Fin.ext
      simp [k1, i1, finProdFinEquiv]
      omega
    have hsucc : cyclicSucc q.1 = i1 := by
      apply Fin.ext
      change (q.1.1 + 1) % d.length = q.1.1 + 1
      rw [Nat.mod_eq_of_lt hi1]
    change
      (boundaryIncidenceGraph edge).DartAdj
        (alternatingDart d k0) (alternatingDart d k1)
    rw [hk0, hk1, alternatingDart_pair_one, alternatingDart_pair_zero]
    change Sum.inl (d.label (cyclicSucc q.1)) = Sum.inl (d.label i1)
    rw [hsucc]

/-- A flattened index remembers its connector number and whether it is the
left or right incidence dart. -/
def dartCoordinates
    (d : CyclicIncidenceData edge)
    (k : Fin (d.length * 2)) : Fin d.length × Fin 2 :=
  (finProdFinEquiv (m := d.length) (n := 2)).symm k

theorem alternatingDart_eq_left_of_coord_zero
    (d : CyclicIncidenceData edge)
    (k : Fin (d.length * 2))
    (h : (d.dartCoordinates k).2.1 = 0) :
    alternatingDart d k =
      leftDart d (d.dartCoordinates k).1 := by
  unfold alternatingDart dartCoordinates at h ⊢
  dsimp
  rw [if_pos h]

theorem alternatingDart_eq_right_of_coord_ne_zero
    (d : CyclicIncidenceData edge)
    (k : Fin (d.length * 2))
    (h : (d.dartCoordinates k).2.1 ≠ 0) :
    alternatingDart d k =
      rightDart d (d.dartCoordinates k).1 := by
  unfold alternatingDart dartCoordinates at h ⊢
  dsimp
  rw [if_neg h]

/-- The flattened incidence darts have pairwise distinct underlying graph
edges. Distinct connectors rule out repetitions at different cyclic
positions, while `label_ne_succ` rules out traversing the same edge out and
back at one connector. -/
theorem alternatingDart_edge_injective
    (d : CyclicIncidenceData edge) :
    Function.Injective
      (fun k : Fin (d.length * 2) => (alternatingDart d k).edge) := by
  intro k l hkl
  let qk := d.dartCoordinates k
  let ql := d.dartCoordinates l
  by_cases hk0 : qk.2.1 = 0
  · by_cases hl0 : ql.2.1 = 0
    · have hkD : alternatingDart d k = leftDart d qk.1 := by
        simpa [qk] using d.alternatingDart_eq_left_of_coord_zero k hk0
      have hlD : alternatingDart d l = leftDart d ql.1 := by
        simpa [ql] using d.alternatingDart_eq_left_of_coord_zero l hl0
      change
        (alternatingDart d k).edge =
          (alternatingDart d l).edge at hkl
      rw [hkD, hlD] at hkl
      change
        s(Sum.inl (d.label qk.1), Sum.inr (d.connector qk.1)) =
        s(Sum.inl (d.label ql.1), Sum.inr (d.connector ql.1)) at hkl
      rcases Sym2.eq_iff.mp hkl with h | h
      · have hc : d.connector qk.1 = d.connector ql.1 :=
          Sum.inr.inj h.2
        have hi : qk.1 = ql.1 := d.connector_injective hc
        have hk2 : qk.2 = (0 : Fin 2) := Fin.ext hk0
        have hl2 : ql.2 = (0 : Fin 2) := Fin.ext hl0
        have hq : qk = ql := by
          apply Prod.ext
          · exact hi
          · exact hk2.trans hl2.symm
        apply (finProdFinEquiv (m := d.length) (n := 2)).symm.injective
        simpa [qk, ql, dartCoordinates] using hq
      · exact (Sum.noConfusion h.1)
    · have hkD : alternatingDart d k = leftDart d qk.1 := by
        simpa [qk] using d.alternatingDart_eq_left_of_coord_zero k hk0
      have hlD : alternatingDart d l = rightDart d ql.1 := by
        simpa [ql] using d.alternatingDart_eq_right_of_coord_ne_zero l hl0
      change
        (alternatingDart d k).edge =
          (alternatingDart d l).edge at hkl
      rw [hkD, hlD] at hkl
      change
        s(Sum.inl (d.label qk.1), Sum.inr (d.connector qk.1)) =
        s(Sum.inr (d.connector ql.1),
          Sum.inl (d.label (cyclicSucc ql.1))) at hkl
      rcases Sym2.eq_iff.mp hkl with h | h
      · exact (Sum.noConfusion h.1)
      · have hc : d.connector qk.1 = d.connector ql.1 :=
          Sum.inr.inj h.2
        have hi : qk.1 = ql.1 := d.connector_injective hc
        have hlabel :
            d.label qk.1 = d.label (cyclicSucc ql.1) :=
          Sum.inl.inj h.1
        exfalso
        apply d.label_ne_succ qk.1
        simpa [hi] using hlabel
  · by_cases hl0 : ql.2.1 = 0
    · have hkD : alternatingDart d k = rightDart d qk.1 := by
        simpa [qk] using d.alternatingDart_eq_right_of_coord_ne_zero k hk0
      have hlD : alternatingDart d l = leftDart d ql.1 := by
        simpa [ql] using d.alternatingDart_eq_left_of_coord_zero l hl0
      change
        (alternatingDart d k).edge =
          (alternatingDart d l).edge at hkl
      rw [hkD, hlD] at hkl
      change
        s(Sum.inr (d.connector qk.1),
          Sum.inl (d.label (cyclicSucc qk.1))) =
        s(Sum.inl (d.label ql.1), Sum.inr (d.connector ql.1)) at hkl
      rcases Sym2.eq_iff.mp hkl with h | h
      · exact (Sum.noConfusion h.1)
      · have hc : d.connector qk.1 = d.connector ql.1 :=
          Sum.inr.inj h.1
        have hi : qk.1 = ql.1 := d.connector_injective hc
        have hlabel :
            d.label (cyclicSucc qk.1) = d.label ql.1 :=
          Sum.inl.inj h.2
        exfalso
        apply d.label_ne_succ qk.1
        simpa [hi] using hlabel.symm
    · have hkD : alternatingDart d k = rightDart d qk.1 := by
        simpa [qk] using d.alternatingDart_eq_right_of_coord_ne_zero k hk0
      have hlD : alternatingDart d l = rightDart d ql.1 := by
        simpa [ql] using d.alternatingDart_eq_right_of_coord_ne_zero l hl0
      change
        (alternatingDart d k).edge =
          (alternatingDart d l).edge at hkl
      rw [hkD, hlD] at hkl
      change
        s(Sum.inr (d.connector qk.1),
          Sum.inl (d.label (cyclicSucc qk.1))) =
        s(Sum.inr (d.connector ql.1),
          Sum.inl (d.label (cyclicSucc ql.1))) at hkl
      rcases Sym2.eq_iff.mp hkl with h | h
      · have hc : d.connector qk.1 = d.connector ql.1 :=
          Sum.inr.inj h.1
        have hi : qk.1 = ql.1 := d.connector_injective hc
        have hk2 : qk.2 = (1 : Fin 2) := by
          apply Fin.ext
          omega
        have hl2 : ql.2 = (1 : Fin 2) := by
          apply Fin.ext
          omega
        have hq : qk = ql := by
          apply Prod.ext
          · exact hi
          · exact hk2.trans hl2.symm
        apply (finProdFinEquiv (m := d.length) (n := 2)).symm.injective
        simpa [qk, ql, dartCoordinates] using hq
      · exact (Sum.noConfusion h.1)

/-- The ordered list of the two incidence darts contributed by every
connector. -/
def incidenceDarts
    (d : CyclicIncidenceData edge) :
    List (boundaryIncidenceGraph edge).Dart :=
  List.ofFn (alternatingDart d)

theorem incidenceDarts_ne_nil
    (d : CyclicIncidenceData edge) :
    d.incidenceDarts ≠ [] := by
  rw [← List.length_pos_iff]
  simp [incidenceDarts]
  exact d.dartLength_pos

theorem incidenceDarts_chain
    (d : CyclicIncidenceData edge) :
    d.incidenceDarts.IsChain
      (boundaryIncidenceGraph edge).DartAdj := by
  simpa [incidenceDarts] using alternatingDarts_chain d

theorem zeroDartIndex_eq_pair
    (d : CyclicIncidenceData edge) :
    d.zeroDartIndex =
      finProdFinEquiv (m := d.length) (n := 2)
        (d.zeroIndex, (0 : Fin 2)) := by
  apply Fin.ext
  simp [zeroDartIndex, zeroIndex, finProdFinEquiv]

theorem lastDartIndex_eq_pair
    (d : CyclicIncidenceData edge) :
    d.lastDartIndex =
      finProdFinEquiv (m := d.length) (n := 2)
        (d.lastIndex, (1 : Fin 2)) := by
  apply Fin.ext
  simp [lastDartIndex, lastIndex, finProdFinEquiv]
  have := d.hlength
  omega

theorem cyclicSucc_lastIndex
    (d : CyclicIncidenceData edge) :
    cyclicSucc d.lastIndex = d.zeroIndex := by
  apply Fin.ext
  change ((d.length - 1) + 1) % d.length = 0
  rw [Nat.sub_add_cancel ((by decide : 1 ≤ 2).trans d.hlength)]
  exact Nat.mod_self d.length

theorem incidenceDarts_head_fst
    (d : CyclicIncidenceData edge) :
    (d.incidenceDarts.head d.incidenceDarts_ne_nil).fst =
      Sum.inl (d.label d.zeroIndex) := by
  rw [List.head_eq_getElem_zero]
  simp only [incidenceDarts, List.getElem_ofFn]
  have hidx :
      (⟨0, d.dartLength_pos⟩ : Fin (d.length * 2)) =
        d.zeroDartIndex := by rfl
  rw [hidx, d.zeroDartIndex_eq_pair, alternatingDart_pair_zero]
  rfl

theorem incidenceDarts_last_snd
    (d : CyclicIncidenceData edge) :
    (d.incidenceDarts.getLast d.incidenceDarts_ne_nil).snd =
      Sum.inl (d.label d.zeroIndex) := by
  rw [List.getLast_eq_getElem d.incidenceDarts_ne_nil]
  simp only [incidenceDarts, List.length_ofFn, List.getElem_ofFn]
  have hidx :
      (⟨d.length * 2 - 1, d.lastDartIndex.isLt⟩ :
        Fin (d.length * 2)) = d.lastDartIndex := by
    rfl
  rw [hidx, d.lastDartIndex_eq_pair, alternatingDart_pair_one]
  change
    Sum.inl (d.label (cyclicSucc d.lastIndex)) =
      Sum.inl (d.label d.zeroIndex)
  rw [d.cyclicSucc_lastIndex]

/-- Raw walk before changing its definitionally computed endpoints to the
common starting label. -/
noncomputable def incidenceRawWalk
    (d : CyclicIncidenceData edge) :=
  SimpleGraph.Walk.ofDarts
    d.incidenceDarts d.incidenceDarts_ne_nil d.incidenceDarts_chain

theorem incidenceRawWalk_isTrail
    (d : CyclicIncidenceData edge) :
    d.incidenceRawWalk.IsTrail := by
  classical
  refine ⟨?_⟩
  unfold incidenceRawWalk
  rw [SimpleGraph.Walk.edges_ofDarts]
  rw [incidenceDarts, List.map_ofFn]
  simpa only [Function.comp_apply] using
    (List.nodup_ofFn.mpr (alternatingDart_edge_injective d))

@[simp]
theorem incidenceRawWalk_length
    (d : CyclicIncidenceData edge) :
    d.incidenceRawWalk.length = d.length * 2 := by
  classical
  unfold incidenceRawWalk
  rw [SimpleGraph.Walk.length_ofDarts]
  simp [incidenceDarts]

/-- The cyclic incidence data determines a nonempty closed walk in the
boundary incidence graph. -/
noncomputable def incidenceCircuit
    (d : CyclicIncidenceData edge) :
    (boundaryIncidenceGraph edge).Walk
      (Sum.inl (d.label d.zeroIndex))
      (Sum.inl (d.label d.zeroIndex)) :=
  d.incidenceRawWalk.copy
    d.incidenceDarts_head_fst d.incidenceDarts_last_snd

/-- The constructed closed walk is a circuit. -/
theorem incidenceCircuit_isCircuit
    (d : CyclicIncidenceData edge) :
    (d.incidenceCircuit).IsCircuit := by
  classical
  have htrail : (d.incidenceCircuit).IsTrail := by
    exact
      (SimpleGraph.Walk.isTrail_copy
        d.incidenceRawWalk
        d.incidenceDarts_head_fst
        d.incidenceDarts_last_snd).2
        d.incidenceRawWalk_isTrail
  refine ⟨htrail, ?_⟩
  intro hnil
  have hzero : d.incidenceCircuit.length = 0 := by
    rw [hnil]
    rfl
  have hlen : d.incidenceCircuit.length = d.length * 2 := by
    rw [incidenceCircuit, SimpleGraph.Walk.length_copy,
      d.incidenceRawWalk_length]
  have := d.hlength
  omega

/-- Acyclic incidence graphs forbid cyclic incidence data. -/
theorem no_cyclicIncidenceData_of_acyclic
    (hAcyc : (boundaryIncidenceGraph edge).IsAcyclic)
    (d : CyclicIncidenceData edge) :
    False := by
  classical
  exact
    hAcyc (d.incidenceCircuit.cycleBypass)
      d.incidenceCircuit_isCircuit.isCycle_cycleBypass

/-- Direct endpoint for the circulation proof. A forest restricted to a set
meeting every common support edge subsingletonly cannot carry cyclic
copy-label/connector data. -/
theorem no_cyclicIncidenceData_of_forest_restriction
    {ι : Type v}
    {F : ι → HypergraphPiece W}
    [Fintype ι] [Nonempty ι]
    (hForest : ForestOfCopies F)
    (P : Set W)
    (hEdgePart :
      ∀ ⦃i j : ι⦄, i ≠ j → ∀ ⦃e : Set W⦄,
        e ∈ (F i).edges → e ∈ (F j).edges →
          (e ∩ P).Subsingleton)
    (d : CyclicIncidenceData
      (fun i => ((F i).restrictCarrier P).carrier)) :
    False :=
  no_cyclicIncidenceData_of_acyclic
    (boundaryIncidenceGraph_isAcyclic_of_forest_restriction
      hForest P hEdgePart)
    d

/-- One-part specialization of
`no_cyclicIncidenceData_of_forest_restriction`. -/
theorem no_cyclicIncidenceData_of_forest_part
    {ι : Type v}
    {F : ι → HypergraphPiece W}
    [Fintype ι] [Nonempty ι]
    (hForest : ForestOfCopies F)
    (P : Set W)
    (hPart : EdgesMeetPartAtMostOne F P)
    (d : CyclicIncidenceData
      (fun i => ((F i).restrictCarrier P).carrier)) :
    False :=
  no_cyclicIncidenceData_of_acyclic
    (boundaryIncidenceGraph_isAcyclic_of_forest_part
      hForest P hPart)
    d

end CyclicIncidenceData

end StructuralRamsey.Girth
