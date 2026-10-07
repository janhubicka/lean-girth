import Girth.ForestIncidenceAcyclic
import Mathlib.Data.List.ChainOfFn
import Mathlib.Data.List.FinRange
import Mathlib.Logic.Equiv.Fin.Basic

/-! # Circuits from cyclic incidence data

After compressing maximal runs of a Berge cycle through standard pictures, the
circulation proof obtains a cyclic sequence of local-copy labels and connector
vertices.  Connector vertices are distinct and the labels on the two sides of
each connector differ.  This already gives a nonempty trail in the labelled
incidence graph; no shortest-subwalk minimization is needed.
-/

namespace StructuralRamsey.Girth

universe v
variable {W E : Type v}

/-- Cyclic incidence data.  Label `i` and its cyclic successor both contain
connector `i`.  Labels themselves may repeat nonconsecutively. -/
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
  Fin.cases
    (leftDart d q.1)
    (fun _ : Fin 1 => rightDart d q.1)
    q.2

@[simp]
theorem alternatingDart_pair_zero
    (d : CyclicIncidenceData edge) (i : Fin d.length) :
    alternatingDart d
        (finProdFinEquiv (m := d.length) (n := 2) (i, 0)) =
      leftDart d i := by
  simp [alternatingDart]

@[simp]
theorem alternatingDart_pair_one
    (d : CyclicIncidenceData edge) (i : Fin d.length) :
    alternatingDart d
        (finProdFinEquiv (m := d.length) (n := 2) (i, 1)) =
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
  have hside : q.2 = 0 ∨ q.2 = 1 := by
    fin_cases q.2 <;> simp
  rcases hside with hzero | hone
  · have hk0 :
        k0 =
          finProdFinEquiv (m := d.length) (n := 2)
            (q.1, (0 : Fin 2)) := by
      rw [← hq]
      congr
      exact Prod.ext rfl hzero.symm
    have hk1 :
        k1 =
          finProdFinEquiv (m := d.length) (n := 2)
            (q.1, (1 : Fin 2)) := by
      apply Fin.ext
      change k + 1 = (1 : Fin 2).1 + 2 * q.1.1
      have hz := congrArg Fin.val hzero
      omega
    change
      (boundaryIncidenceGraph edge).DartAdj
        (alternatingDart d k0) (alternatingDart d k1)
    rw [hk0, hk1, alternatingDart_pair_zero, alternatingDart_pair_one]
    rfl
  · have honeVal : q.2.1 = 1 := congrArg Fin.val hone
    have hi1 : q.1.1 + 1 < d.length := by
      omega
    let i1 : Fin d.length := ⟨q.1.1 + 1, hi1⟩
    have hk0 :
        k0 =
          finProdFinEquiv (m := d.length) (n := 2)
            (q.1, (1 : Fin 2)) := by
      rw [← hq]
      congr
      exact Prod.ext rfl hone.symm
    have hk1 :
        k1 =
          finProdFinEquiv (m := d.length) (n := 2)
            (i1, (0 : Fin 2)) := by
      apply Fin.ext
      change k + 1 = (0 : Fin 2).1 + 2 * i1.1
      dsimp [i1]
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

/-- The flattened incidence darts have pairwise distinct underlying graph
edges.  Distinct connectors rule out repetitions at different cyclic
positions, while `label_ne_succ` rules out traversing the same edge out and
back at one connector. -/
theorem alternatingDart_edge_injective
    (d : CyclicIncidenceData edge) :
    Function.Injective
      (fun k : Fin (d.length * 2) => (alternatingDart d k).edge) := by
  intro k l hkl
  let qk : Fin d.length × Fin 2 :=
    (finProdFinEquiv (m := d.length) (n := 2)).symm k
  let ql : Fin d.length × Fin 2 :=
    (finProdFinEquiv (m := d.length) (n := 2)).symm l
  have hkSide : qk.2 = 0 ∨ qk.2 = 1 := by
    fin_cases qk.2 <;> simp
  have hlSide : ql.2 = 0 ∨ ql.2 = 1 := by
    fin_cases ql.2 <;> simp
  rcases hkSide with hk0 | hk1 <;>
    rcases hlSide with hl0 | hl1
  · have h := hkl
    simp [alternatingDart, qk, ql, hk0, hl0,
      leftDart, SimpleGraph.Dart.edge, Sym2.eq_iff] at h
    have hi : qk.1 = ql.1 :=
      d.connector_injective h.2
    have hq : qk = ql := by
      apply Prod.ext
      · exact hi
      · simpa [hk0, hl0]
    exact
      (finProdFinEquiv (m := d.length) (n := 2)).symm.injective hq
  · have h := hkl
    simp [alternatingDart, qk, ql, hk0, hl1,
      leftDart, rightDart, SimpleGraph.Dart.edge, Sym2.eq_iff] at h
    have hi : qk.1 = ql.1 :=
      d.connector_injective h.2
    apply False.elim
    apply d.label_ne_succ qk.1
    simpa [hi] using h.1
  · have h := hkl
    simp [alternatingDart, qk, ql, hk1, hl0,
      leftDart, rightDart, SimpleGraph.Dart.edge, Sym2.eq_iff] at h
    have hi : qk.1 = ql.1 :=
      d.connector_injective h.1
    apply False.elim
    apply d.label_ne_succ qk.1
    simpa [hi] using h.2
  · have h := hkl
    simp [alternatingDart, qk, ql, hk1, hl1,
      rightDart, SimpleGraph.Dart.edge, Sym2.eq_iff] at h
    have hi : qk.1 = ql.1 :=
      d.connector_injective h.1
    have hq : qk = ql := by
      apply Prod.ext
      · exact hi
      · simpa [hk1, hl1]
    exact
      (finProdFinEquiv (m := d.length) (n := 2)).symm.injective hq

/-- The ordered list of the two incidence darts contributed by every
connector. -/
def incidenceDarts
    (d : CyclicIncidenceData edge) :
    List (boundaryIncidenceGraph edge).Dart :=
  List.ofFn (alternatingDart d)

theorem incidenceDarts_ne_nil
    (d : CyclicIncidenceData edge) :
    d.incidenceDarts ≠ [] := by
  rw [incidenceDarts, List.ofFn_eq_nil_iff]
  omega

theorem incidenceDarts_chain
    (d : CyclicIncidenceData edge) :
    d.incidenceDarts.IsChain
      (boundaryIncidenceGraph edge).DartAdj := by
  simpa [incidenceDarts] using alternatingDarts_chain d

theorem incidenceDarts_head_fst
    (d : CyclicIncidenceData edge) :
    (d.incidenceDarts.head d.incidenceDarts_ne_nil).fst =
      Sum.inl (d.label 0) := by
  rw [List.head_eq_getElem_zero]
  simp [incidenceDarts, alternatingDart, leftDart, finProdFinEquiv]

theorem incidenceDarts_last_snd
    (d : CyclicIncidenceData edge) :
    (d.incidenceDarts.getLast d.incidenceDarts_ne_nil).snd =
      Sum.inl (d.label 0) := by
  have hlastIndex :
      finProdFinEquiv (m := d.length) (n := 2)
          (Fin.last d.length, (1 : Fin 2)) =
        Fin.last (d.length * 2) := by
    apply Fin.ext
    simp [finProdFinEquiv, Fin.last]
    omega
  have hsuccLast :
      cyclicSucc (Fin.last d.length) = (0 : Fin d.length) := by
    apply Fin.ext
    change ((d.length - 1) + 1) % d.length = 0
    rw [Nat.sub_add_cancel (by omega : 1 ≤ d.length)]
    exact Nat.mod_self d.length
  rw [List.getLast_eq_getElem d.incidenceDarts_ne_nil]
  have hlen : d.incidenceDarts.length = d.length * 2 := by
    simp [incidenceDarts]
  have hidx :
      d.incidenceDarts.length - 1 =
        (Fin.last (d.length * 2)).1 := by
    simp [hlen, Fin.last]
  simp only [hidx, incidenceDarts, List.getElem_ofFn]
  rw [← hlastIndex, alternatingDart_pair_one]
  change Sum.inl (d.label (cyclicSucc (Fin.last d.length))) =
    Sum.inl (d.label 0)
  rw [hsuccLast]

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
  simpa [incidenceDarts, List.map_ofFn] using
    (List.nodup_ofFn.mpr (alternatingDart_edge_injective d))

@[simp]
theorem incidenceRawWalk_length
    (d : CyclicIncidenceData edge) :
    d.incidenceRawWalk.length = d.length * 2 := by
  classical
  unfold incidenceRawWalk
  simp [incidenceDarts]

/-- The cyclic incidence data determines a nonempty closed walk in the
boundary incidence graph. -/
noncomputable def incidenceCircuit
    (d : CyclicIncidenceData edge) :
    (boundaryIncidenceGraph edge).Walk
      (Sum.inl (d.label 0)) (Sum.inl (d.label 0)) :=
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
  have hzero : d.incidenceCircuit.length = 0 :=
    hnil.length_eq_zero
  have hlen : d.incidenceCircuit.length = d.length * 2 := by
    simp [incidenceCircuit]
  omega

/-- Acyclic incidence graphs forbid cyclic incidence data. -/
theorem no_cyclicIncidenceData_of_acyclic
    (hAcyc : (boundaryIncidenceGraph edge).IsAcyclic)
    (d : CyclicIncidenceData edge) :
    False := by
  exact
    hAcyc (d.incidenceCircuit.cycleBypass)
      d.incidenceCircuit_isCircuit.isCycle_cycleBypass


/-- Direct endpoint for the circulation proof.  A forest restricted to a set
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
