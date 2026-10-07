import Girth.IncidenceCircuit
import Girth.CyclicRun

/-! # Compressing cyclic incidence runs

Before the final incidence contradiction, the circulation proof has one owner
label for every edge of the original Berge cycle. Consecutive labels may
agree. Only owner changes are forced through the local witness; connectors
inside one owner run may remain private. This file compresses equal-label runs
and retains precisely the change connectors.
-/

namespace StructuralRamsey.Girth

universe v
variable {W E : Type v}

/-- Cyclic owner data before maximal equal-label runs have been compressed.
Incidence in the target labelled family is required only at genuine owner
changes. -/
structure RawCyclicIncidenceData (edge : E → Set W) where
  length : ℕ
  hlength : 2 ≤ length
  label : Fin length → E
  connector : Fin length → W
  connector_injective : Function.Injective connector
  boundary_mem :
    ∀ i, label i ≠ label (cyclicSucc i) →
      connector i ∈ edge (label i) ∧
      connector i ∈ edge (label (cyclicSucc i))
  nonconstant : ∃ i j, label i ≠ label j

namespace RawCyclicIncidenceData

variable {edge : E → Set W}

theorem length_pos (d : RawCyclicIncidenceData edge) : 0 < d.length :=
  lt_of_lt_of_le (by decide) d.hlength

def zeroIndex (d : RawCyclicIncidenceData edge) : Fin d.length :=
  ⟨0, d.length_pos⟩

/-- Cyclic translation commutes with cyclic successor. -/
theorem finCycle_cyclicSucc
    {n : ℕ} (s i : Fin n) :
    (finCycle s) (cyclicSucc i) =
      cyclicSucc ((finCycle s) i) := by
  rw [cyclicSucc_eq_finRotate, cyclicSucc_eq_finRotate]
  simp only [finRotate_apply, finCycle_apply]
  ac_rfl

/-- Rotate the cyclic indexing without changing owner-change incidence data. -/
def rotate
    (d : RawCyclicIncidenceData edge)
    (s : Fin d.length) :
    RawCyclicIncidenceData edge where
  length := d.length
  hlength := d.hlength
  label i := d.label ((finCycle s) i)
  connector i := d.connector ((finCycle s) i)
  connector_injective := by
    intro i j hij
    exact (finCycle s).injective (d.connector_injective hij)
  boundary_mem := by
    intro i hne
    have hneOld :
        d.label ((finCycle s) i) ≠
          d.label (cyclicSucc ((finCycle s) i)) := by
      intro heq
      apply hne
      rw [finCycle_cyclicSucc]
      exact heq
    have h := d.boundary_mem ((finCycle s) i) hneOld
    constructor
    · exact h.1
    · rw [finCycle_cyclicSucc]
      exact h.2
  nonconstant := by
    rcases d.nonconstant with ⟨i, j, hij⟩
    let i' : Fin d.length := (finCycle s).symm i
    let j' : Fin d.length := (finCycle s).symm j
    refine ⟨i', j', ?_⟩
    change d.label ((finCycle s) i') ≠
      d.label ((finCycle s) j')
    have hi' : (finCycle s) i' = i := by
      exact Equiv.apply_symm_apply (finCycle s) i
    have hj' : (finCycle s) j' = j := by
      exact Equiv.apply_symm_apply (finCycle s) j
    rw [hi', hj']
    exact hij

/-- Canonical last index of nonempty raw cyclic data. -/
def last
    (d : RawCyclicIncidenceData edge) :
    Fin d.length :=
  ⟨d.length - 1, Nat.sub_lt d.length_pos (by decide)⟩

/-- Rotating by the successor of an old index sends the last new
position back to that old index. -/
theorem finCycle_last_cyclicSucc
    (d : RawCyclicIncidenceData edge)
    (i : Fin d.length) :
    (finCycle (cyclicSucc i)) d.last = i := by
  rw [finCycle_apply]
  apply Fin.ext
  rw [Fin.val_add]
  change
    (d.length - 1 + (i.1 + 1) % d.length) % d.length = i.1
  by_cases hnext : i.1 + 1 < d.length
  · rw [Nat.mod_eq_of_lt hnext]
    have hsum :
        d.length - 1 + (i.1 + 1) =
          d.length + i.1 := by
      omega
    rw [hsum, Nat.add_mod_right, Nat.mod_eq_of_lt i.2]
  · have hlast : i.1 + 1 = d.length := by
      omega
    rw [hlast, Nat.mod_self, Nat.add_zero,
      Nat.mod_eq_of_lt (Nat.sub_lt d.length_pos (by decide))]
    omega

/-- If the transition at i is redundant, rotate it to the wrap-around:
the last and first labels of the rotated word agree. -/
theorem rotate_succ_last_label_eq_zero
    (d : RawCyclicIncidenceData edge)
    (i : Fin d.length)
    (heq : d.label i = d.label (cyclicSucc i)) :
    (d.rotate (cyclicSucc i)).label
        (d.rotate (cyclicSucc i)).last =
      (d.rotate (cyclicSucc i)).label
        (d.rotate (cyclicSucc i)).zeroIndex := by
  change
    d.label ((finCycle (cyclicSucc i)) d.last) =
      d.label ((finCycle (cyclicSucc i)) d.zeroIndex)
  rw [d.finCycle_last_cyclicSucc i]
  have hz :
      (finCycle (cyclicSucc i)) d.zeroIndex =
        cyclicSucc i := by
    rw [finCycle_apply]
    apply Fin.ext
    rw [Fin.val_add]
    simp [zeroIndex, Nat.mod_eq_of_lt (cyclicSucc i).2]
  rw [hz]
  exact heq

/-- Inclusion of all indices except the last one. -/
def keepBeforeLast
    (d : RawCyclicIncidenceData edge)
    (i : Fin (d.length - 1)) :
    Fin d.length :=
  ⟨i.1, by
    have := d.hlength
    omega⟩

theorem keepBeforeLast_injective
    (d : RawCyclicIncidenceData edge) :
    Function.Injective d.keepBeforeLast := by
  intro i j hij
  apply Fin.ext
  have hv := congrArg Fin.val hij
  simpa [keepBeforeLast] using hv

/-- If the last and first labels agree, delete the redundant last label and
last connector. Incidence is only transported for transitions which remain
genuine owner changes. -/
def dropLast
    (d : RawCyclicIncidenceData edge)
    (h3 : 3 ≤ d.length)
    (hwrap : d.label d.last = d.label d.zeroIndex) :
    RawCyclicIncidenceData edge := by
  classical
  let keep := d.keepBeforeLast
  let z : Fin (d.length - 1) := ⟨0, by omega⟩
  refine
    { length := d.length - 1
      hlength := by omega
      label := fun i => d.label (keep i)
      connector := fun i => d.connector (keep i)
      connector_injective := ?_
      boundary_mem := ?_
      nonconstant := ?_ }
  · intro i j hij
    apply d.keepBeforeLast_injective
    exact d.connector_injective hij
  · intro i hneNew
    let oi : Fin d.length := keep i
    by_cases hnext : i.1 + 1 < d.length - 1
    · let j : Fin (d.length - 1) := ⟨i.1 + 1, hnext⟩
      have hsuccNew : cyclicSucc i = j := by
        apply Fin.ext
        change (i.1 + 1) % (d.length - 1) = i.1 + 1
        rw [Nat.mod_eq_of_lt hnext]
      have hsuccOld : cyclicSucc oi = keep j := by
        apply Fin.ext
        change (i.1 + 1) % d.length = j.1
        dsimp [j]
        rw [Nat.mod_eq_of_lt (by omega)]
      have hneOld :
          d.label oi ≠ d.label (cyclicSucc oi) := by
        intro heq
        apply hneNew
        simpa [hsuccNew, hsuccOld, oi] using heq
      have h := d.boundary_mem oi hneOld
      constructor
      · exact h.1
      · simpa [hsuccNew, hsuccOld, oi] using h.2
    · have hilast : i.1 + 1 = d.length - 1 := by
        omega
      have hsuccNew :
          cyclicSucc i = z := by
        apply Fin.ext
        change (i.1 + 1) % (d.length - 1) = 0
        rw [hilast, Nat.mod_self]
      have hsuccOld : cyclicSucc oi = d.last := by
        apply Fin.ext
        change (i.1 + 1) % d.length = d.length - 1
        rw [hilast, Nat.mod_eq_of_lt (by omega)]
      have hkeepZero : keep z = d.zeroIndex := by
        apply Fin.ext
        rfl
      have hneOld :
          d.label oi ≠ d.label (cyclicSucc oi) := by
        intro heq
        apply hneNew
        have heq' : d.label (keep i) = d.label d.zeroIndex := by
          simpa [oi, hsuccOld, hwrap] using heq
        simpa [hsuccNew, hkeepZero] using heq'
      have h := d.boundary_mem oi hneOld
      constructor
      · exact h.1
      · have hright :
            d.connector oi ∈ edge (d.label d.zeroIndex) := by
          simpa [hsuccOld, hwrap] using h.2
        simpa [hsuccNew, hkeepZero, oi] using hright
  · by_contra hconst
    push_neg at hconst
    have hAll : ∀ i : Fin d.length, d.label i = d.label d.zeroIndex := by
      intro i
      by_cases hi : i = d.last
      · subst i
        exact hwrap
      · have hvalne : i.1 ≠ d.length - 1 := by
          intro hval
          apply hi
          apply Fin.ext
          simpa [RawCyclicIncidenceData.last] using hval
        have hlt : i.1 < d.length - 1 := by
          omega
        let i' : Fin (d.length - 1) := ⟨i.1, hlt⟩
        have hEq := hconst i' z
        change d.label (keep i') = d.label (keep z) at hEq
        have hkeepI : keep i' = i := by
          apply Fin.ext
          rfl
        have hkeepZero : keep z = d.zeroIndex := by
          apply Fin.ext
          rfl
        rw [hkeepI, hkeepZero] at hEq
        exact hEq
    rcases d.nonconstant with ⟨i, j, hij⟩
    exact hij ((hAll i).trans (hAll j).symm)

/-- Dropping the redundant wrap-around strictly decreases the length. -/
theorem dropLast_length_lt
    (d : RawCyclicIncidenceData edge)
    (h3 : 3 ≤ d.length)
    (hwrap : d.label d.last = d.label d.zeroIndex) :
    (d.dropLast h3 hwrap).length < d.length := by
  dsimp [dropLast]
  omega

/-- Cyclic successor has no fixed point once there are at least two indices. -/
theorem cyclicSucc_ne_self_of_two_le
    {n : ℕ} (hn : 2 ≤ n) (i : Fin n) :
    cyclicSucc i ≠ i := by
  intro h
  have hv := congrArg Fin.val h
  change (i.1 + 1) % n = i.1 at hv
  by_cases hi : i.1 + 1 < n
  · rw [Nat.mod_eq_of_lt hi] at hv
    omega
  · have hieq : i.1 + 1 = n := by
      omega
    rw [hieq, Nat.mod_self] at hv
    omega

/-- A nonconstant cyclic word with one equal adjacent pair has length at least
three. -/
theorem three_le_length_of_label_eq_succ
    (d : RawCyclicIncidenceData edge)
    (i : Fin d.length)
    (heq : d.label i = d.label (cyclicSucc i)) :
    3 ≤ d.length := by
  by_contra h3
  have hlt3 : d.length < 3 := Nat.lt_of_not_ge h3
  have h2 := d.hlength
  have hlen : d.length = 2 := by
    omega
  have hne : i ≠ cyclicSucc i :=
    Ne.symm (cyclicSucc_ne_self_of_two_le d.hlength i)
  have hpair :
      ({i, cyclicSucc i} : Finset (Fin d.length)) = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [Finset.card_pair hne]
    simp [hlen]
  have hall : ∀ j : Fin d.length, d.label j = d.label i := by
    intro j
    have hjmem :
        j ∈ ({i, cyclicSucc i} : Finset (Fin d.length)) := by
      rw [hpair]
      simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hjmem
    rcases hjmem with hj | hj
    · simpa [hj]
    · simpa [hj] using heq.symm
  rcases d.nonconstant with ⟨j, k, hjk⟩
  exact hjk ((hall j).trans (hall k).symm)

/-- Repeatedly delete redundant equal-label transitions until every cyclic
transition changes label. The resulting compressed cycle never has more
positions than the original one. -/
theorem exists_compressed_le
    (d : RawCyclicIncidenceData edge) :
    ∃ c : CyclicIncidenceData edge, c.length ≤ d.length := by
  classical
  suffices hAux :
      ∀ n : ℕ, ∀ d : RawCyclicIncidenceData edge,
        d.length = n →
        ∃ c : CyclicIncidenceData edge, c.length ≤ d.length by
    exact hAux d.length d rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro d hlen
      by_cases hgood :
          ∀ i : Fin d.length,
            d.label i ≠ d.label (cyclicSucc i)
      · refine ⟨{
          length := d.length
          hlength := d.hlength
          label := d.label
          connector := d.connector
          connector_injective := d.connector_injective
          label_ne_succ := hgood
          left_mem := fun i => (d.boundary_mem i (hgood i)).1
          right_mem := fun i => (d.boundary_mem i (hgood i)).2
        }, le_rfl⟩
      · push_neg at hgood
        obtain ⟨i, heq⟩ := hgood
        have h3 : 3 ≤ d.length :=
          d.three_le_length_of_label_eq_succ i heq
        let r := d.rotate (cyclicSucc i)
        have hwrap : r.label r.last = r.label r.zeroIndex := by
          simpa [r] using d.rotate_succ_last_label_eq_zero i heq
        let d' := r.dropLast h3 hwrap
        have hltD : d'.length < d.length := by
          dsimp [d']
          exact r.dropLast_length_lt h3 hwrap
        have hltN : d'.length < n := by
          simpa [hlen] using hltD
        obtain ⟨c, hc⟩ := ih d'.length hltN d' rfl
        refine ⟨c, hc.trans (Nat.le_of_lt hltD)⟩

/-- Every nonconstant raw cyclic owner pattern therefore yields the compressed
cyclic incidence data consumed by the circuit theorem. -/
noncomputable def compress
    (d : RawCyclicIncidenceData edge) :
    CyclicIncidenceData edge :=
  Classical.choose d.exists_compressed_le

theorem compress_length_le
    (d : RawCyclicIncidenceData edge) :
    d.compress.length ≤ d.length :=
  Classical.choose_spec d.exists_compressed_le

/-- Raw owner data extracted from a Berge cycle. Only connectors across actual
owner changes need to lie in the two corresponding labelled pieces. -/
def ofBergeCycle
    {H : Set (Set W)}
    (c : BergeCycle H)
    (owner : Fin c.length → E)
    (edge : E → Set W)
    (hBoundary :
      ∀ i, owner i ≠ owner (cyclicSucc i) →
        c.vertex i ∈ edge (owner i) ∧
        c.vertex i ∈ edge (owner (cyclicSucc i)))
    (hOwnerNonconstant :
      ∃ i j : Fin c.length, owner i ≠ owner j) :
    RawCyclicIncidenceData edge where
  length := c.length
  hlength := c.hlength
  label := owner
  connector := c.vertex
  connector_injective := c.vertex_injective
  boundary_mem := hBoundary
  nonconstant := hOwnerNonconstant

/-- End-to-end maximal run compression for a Berge owner word. -/
theorem exists_compressed_ofBergeCycle
    {H : Set (Set W)}
    (c : BergeCycle H)
    (owner : Fin c.length → E)
    (edge : E → Set W)
    (hBoundary :
      ∀ i, owner i ≠ owner (cyclicSucc i) →
        c.vertex i ∈ edge (owner i) ∧
        c.vertex i ∈ edge (owner (cyclicSucc i)))
    (hOwnerNonconstant :
      ∃ i j : Fin c.length, owner i ≠ owner j) :
    ∃ d : CyclicIncidenceData edge,
      d.length ≤ c.length :=
  exists_compressed_le
    (ofBergeCycle c owner edge hBoundary hOwnerNonconstant)

/-- Direct contradiction used for untouched subsystems in the circulation
proof. A forest restricted to the fine part cannot support the change
connectors of a nonconstant owner word around a Berge cycle. -/
theorem no_nonconstant_owner_cycle_of_forest_restriction
    {H : Set (Set W)}
    {ι : Type v}
    {F : ι → HypergraphPiece W}
    [Fintype ι] [Nonempty ι]
    (hForest : ForestOfCopies F)
    (P : Set W)
    (hEdgePart :
      ∀ ⦃i j : ι⦄, i ≠ j → ∀ ⦃e : Set W⦄,
        e ∈ (F i).edges → e ∈ (F j).edges →
          (e ∩ P).Subsingleton)
    (c : BergeCycle H)
    (owner : Fin c.length → ι)
    (hBoundary :
      ∀ i, owner i ≠ owner (cyclicSucc i) →
        c.vertex i ∈ ((F (owner i)).restrictCarrier P).carrier ∧
        c.vertex i ∈
          ((F (owner (cyclicSucc i))).restrictCarrier P).carrier)
    (hOwnerNonconstant :
      ∃ i j : Fin c.length, owner i ≠ owner j) :
    False := by
  let raw : RawCyclicIncidenceData
      (fun i => ((F i).restrictCarrier P).carrier) :=
    ofBergeCycle c owner
      (fun i => ((F i).restrictCarrier P).carrier)
      hBoundary hOwnerNonconstant
  exact
    CyclicIncidenceData.no_cyclicIncidenceData_of_forest_restriction
      hForest P hEdgePart raw.compress

/-- One-part specialization of the preceding contradiction. -/
theorem no_nonconstant_owner_cycle_of_forest_part
    {H : Set (Set W)}
    {ι : Type v}
    {F : ι → HypergraphPiece W}
    [Fintype ι] [Nonempty ι]
    (hForest : ForestOfCopies F)
    (P : Set W)
    (hPart : EdgesMeetPartAtMostOne F P)
    (c : BergeCycle H)
    (owner : Fin c.length → ι)
    (hBoundary :
      ∀ i, owner i ≠ owner (cyclicSucc i) →
        c.vertex i ∈ ((F (owner i)).restrictCarrier P).carrier ∧
        c.vertex i ∈
          ((F (owner (cyclicSucc i))).restrictCarrier P).carrier)
    (hOwnerNonconstant :
      ∃ i j : Fin c.length, owner i ≠ owner j) :
    False := by
  let raw : RawCyclicIncidenceData
      (fun i => ((F i).restrictCarrier P).carrier) :=
    ofBergeCycle c owner
      (fun i => ((F i).restrictCarrier P).carrier)
      hBoundary hOwnerNonconstant
  exact
    CyclicIncidenceData.no_cyclicIncidenceData_of_forest_part
      hForest P hPart raw.compress

end RawCyclicIncidenceData

end StructuralRamsey.Girth
