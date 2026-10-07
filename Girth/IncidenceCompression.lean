import Girth.IncidenceCircuit
import Girth.CyclicRun

/-! # Compressing cyclic incidence runs

Before the final incidence contradiction, the circulation proof has one label
for every edge of the original Berge cycle.  Consecutive labels may agree.
This file formalizes the elementary cyclic compression which removes such
redundant transitions while preserving the connector incidences.
-/

namespace StructuralRamsey.Girth

universe v
variable {W E : Type v}

/-- Cyclic incidence data before maximal equal-label runs have been
compressed.  The label word is required to be nonconstant. -/
structure RawCyclicIncidenceData (edge : E → Set W) where
  length : ℕ
  hlength : 2 ≤ length
  label : Fin length → E
  connector : Fin length → W
  connector_injective : Function.Injective connector
  left_mem : ∀ i, connector i ∈ edge (label i)
  right_mem : ∀ i, connector i ∈ edge (label (cyclicSucc i))
  nonconstant : ∃ i j, label i ≠ label j

namespace RawCyclicIncidenceData

variable {edge : E → Set W}

/-- Cyclic translation commutes with cyclic successor. -/
theorem finCycle_cyclicSucc
    {n : ℕ} (i s : Fin n) :
    finCycle (cyclicSucc i) s =
      cyclicSucc (finCycle i s) := by
  rw [cyclicSucc_eq_finRotate, cyclicSucc_eq_finRotate]
  simp only [finRotate_apply, finCycle_apply]
  ac_rfl

/-- Rotate the cyclic indexing without changing any incidence data. -/
def rotate
    (d : RawCyclicIncidenceData edge)
    (s : Fin d.length) :
    RawCyclicIncidenceData edge where
  length := d.length
  hlength := d.hlength
  label i := d.label (finCycle i s)
  connector i := d.connector (finCycle i s)
  connector_injective := by
    intro i j hij
    apply (finCycle s).injective
    exact d.connector_injective hij
  left_mem i := d.left_mem (finCycle i s)
  right_mem i := by
    have h := d.right_mem (finCycle i s)
    rw [← finCycle_cyclicSucc i s] at h
    exact h
  nonconstant := by
    rcases d.nonconstant with ⟨i, j, hij⟩
    let i' : Fin d.length := (finCycle s).symm i
    let j' : Fin d.length := (finCycle s).symm j
    refine ⟨i', j', ?_⟩
    simpa [i', j'] using hij

/-- Canonical last index of nonempty raw cyclic data. -/
def last
    (d : RawCyclicIncidenceData edge) :
    Fin d.length :=
  ⟨d.length - 1, by omega⟩

/-- Rotating to the successor of an index sends the last new position back to
that index. -/
theorem finCycle_last_cyclicSucc
    (d : RawCyclicIncidenceData edge)
    (i : Fin d.length) :
    finCycle d.last (cyclicSucc i) = i := by
  haveI : NeZero d.length := ⟨by omega⟩
  have hlast : d.last = (-1 : Fin d.length) := by
    apply Fin.ext
    change d.length - 1 = ((-1 : Fin d.length) : ℕ)
    conv_rhs =>
      rw [show d.length = (d.length - 1) + 1 by omega]
    rw [Fin.coe_neg_one]
  rw [finCycle_apply, cyclicSucc_eq_finRotate, finRotate_apply, hlast]
  calc
    (-1 : Fin d.length) + (i + 1) =
        ((-1 : Fin d.length) + 1) + i := by ac_rfl
    _ = i := by simp

/-- If the transition at i is redundant, rotate it to the wrap-around:
the last and first labels of the rotated word agree. -/
theorem rotate_succ_last_label_eq_zero
    (d : RawCyclicIncidenceData edge)
    (i : Fin d.length)
    (heq : d.label i = d.label (cyclicSucc i)) :
    (d.rotate (cyclicSucc i)).label
        (d.rotate (cyclicSucc i)).last =
      (d.rotate (cyclicSucc i)).label 0 := by
  change
    d.label (finCycle d.last (cyclicSucc i)) =
      d.label (finCycle 0 (cyclicSucc i))
  rw [d.finCycle_last_cyclicSucc i]
  simpa [finCycle_apply] using heq


/-- Inclusion of all indices except the last one. -/
def keepBeforeLast
    (d : RawCyclicIncidenceData edge)
    (i : Fin (d.length - 1)) :
    Fin d.length :=
  ⟨i.1, by omega⟩

theorem keepBeforeLast_injective
    (d : RawCyclicIncidenceData edge) :
    Function.Injective d.keepBeforeLast := by
  intro i j hij
  apply Fin.ext
  exact congrArg Fin.val hij

/-- If the last and first labels agree, delete the redundant last label and
last connector.  Nonconstancy guarantees this operation is only used when at
least three positions remain. -/
def dropLast
    (d : RawCyclicIncidenceData edge)
    (h3 : 3 ≤ d.length)
    (hwrap : d.label d.last = d.label 0) :
    RawCyclicIncidenceData edge := by
  classical
  let keep := d.keepBeforeLast
  refine
    { length := d.length - 1
      hlength := by omega
      label := fun i => d.label (keep i)
      connector := fun i => d.connector (keep i)
      connector_injective := ?_
      left_mem := ?_
      right_mem := ?_
      nonconstant := ?_ }
  · intro i j hij
    apply d.keepBeforeLast_injective
    exact d.connector_injective hij
  · intro i
    exact d.left_mem (keep i)
  · intro i
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
      have h := d.right_mem oi
      rw [hsuccOld] at h
      simpa [hsuccNew, oi] using h
    · have hilast : i.1 + 1 = d.length - 1 := by
        omega
      have hsuccNew :
          cyclicSucc i = (0 : Fin (d.length - 1)) := by
        apply Fin.ext
        change (i.1 + 1) % (d.length - 1) = 0
        rw [hilast, Nat.mod_self]
      have hsuccOld : cyclicSucc oi = d.last := by
        apply Fin.ext
        change (i.1 + 1) % d.length = d.length - 1
        rw [hilast, Nat.mod_eq_of_lt (by omega)]
      have h := d.right_mem oi
      rw [hsuccOld, hwrap] at h
      simpa [hsuccNew, oi, keep, keepBeforeLast] using h
  · by_contra hconst
    push_neg at hconst
    have hAll : ∀ i : Fin d.length, d.label i = d.label 0 := by
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
        have hEq :=
          hconst i' (0 : Fin (d.length - 1))
        change
          d.label (keep i') =
            d.label (keep (0 : Fin (d.length - 1))) at hEq
        simpa [i', keep, keepBeforeLast] using hEq
    rcases d.nonconstant with ⟨i, j, hij⟩
    exact hij ((hAll i).trans (hAll j).symm)

/-- Dropping the redundant wrap-around strictly decreases the length. -/
theorem dropLast_length_lt
    (d : RawCyclicIncidenceData edge)
    (h3 : 3 ≤ d.length)
    (hwrap : d.label d.last = d.label 0) :
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
  have hlen : d.length = 2 := by
    omega
  have hne : i ≠ cyclicSucc i :=
    (cyclicSucc_ne_self_of_two_le d.hlength i)
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
    rcases Finset.mem_pair.mp hjmem with hj | hj
    · simpa [hj]
    · simpa [hj] using heq.symm
  rcases d.nonconstant with ⟨j, k, hjk⟩
  exact hjk ((hall j).trans (hall k).symm)

/-- Repeatedly delete redundant equal-label transitions until every cyclic
transition changes label.  The resulting compressed cycle never has more
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
          left_mem := d.left_mem
          right_mem := d.right_mem
        }, le_rfl⟩
      · push_neg at hgood
        obtain ⟨i, heq⟩ := hgood
        have h3 : 3 ≤ d.length :=
          d.three_le_length_of_label_eq_succ i heq
        let r := d.rotate (cyclicSucc i)
        have hwrap : r.label r.last = r.label 0 := by
          simpa [r] using d.rotate_succ_last_label_eq_zero i heq
        let d' := r.dropLast h3 hwrap
        have hltD : d'.length < d.length := by
          dsimp [d']
          exact r.dropLast_length_lt h3 hwrap
        have hltN : d'.length < n := by
          simpa [hlen] using hltD
        obtain ⟨c, hc⟩ := ih d'.length hltN d' rfl
        refine ⟨c, hc.trans ?_⟩
        exact Nat.le_of_lt hltD

/-- Every nonconstant raw cyclic incidence pattern therefore yields the
compressed cyclic incidence data consumed by the circuit theorem. -/
noncomputable def compress
    (d : RawCyclicIncidenceData edge) :
    CyclicIncidenceData edge :=
  Classical.choose d.exists_compressed_le

theorem compress_length_le
    (d : RawCyclicIncidenceData edge) :
    d.compress.length ≤ d.length :=
  Classical.choose_spec d.exists_compressed_le


/-- Raw cyclic incidence data extracted from a Berge cycle and an arbitrary
owner assignment.  The hyperedges of the Berge cycle are only used to supply
distinct connector vertices; the owner pieces may repeat. -/
def ofBergeCycle
    {H : Set (Set W)}
    (c : BergeCycle H)
    (owner : Fin c.length → E)
    (edge : E → Set W)
    (hLeft : ∀ i, c.vertex i ∈ edge (owner i))
    (hRight :
      ∀ i, c.vertex i ∈ edge (owner (cyclicSucc i)))
    (hOwnerNonconstant :
      ∃ i j : Fin c.length, owner i ≠ owner j) :
    RawCyclicIncidenceData edge where
  length := c.length
  hlength := c.hlength
  label := owner
  connector := c.vertex
  connector_injective := c.vertex_injective
  left_mem := hLeft
  right_mem := hRight
  nonconstant := hOwnerNonconstant

/-- End-to-end combinatorial form of maximal run compression: a Berge cycle
with a nonconstant owner word and adjacent connector incidence yields
compressed cyclic incidence data, of no greater length. -/
theorem exists_compressed_ofBergeCycle
    {H : Set (Set W)}
    (c : BergeCycle H)
    (owner : Fin c.length → E)
    (edge : E → Set W)
    (hLeft : ∀ i, c.vertex i ∈ edge (owner i))
    (hRight :
      ∀ i, c.vertex i ∈ edge (owner (cyclicSucc i)))
    (hOwnerNonconstant :
      ∃ i j : Fin c.length, owner i ≠ owner j) :
    ∃ d : CyclicIncidenceData edge,
      d.length ≤ c.length := by
  exact
    (ofBergeCycle c owner edge hLeft hRight hOwnerNonconstant).
      exists_compressed_le

/-- Direct contradiction used for untouched subsystems in the circulation
proof.  If the owner pieces form a forest after restriction, a Berge cycle
cannot have a nonconstant owner word whose connector at every transition lies
in both adjacent owner pieces. -/
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
    (hLeft :
      ∀ i,
        c.vertex i ∈
          ((F (owner i)).restrictCarrier P).carrier)
    (hRight :
      ∀ i,
        c.vertex i ∈
          ((F (owner (cyclicSucc i))).restrictCarrier P).carrier)
    (hOwnerNonconstant :
      ∃ i j : Fin c.length, owner i ≠ owner j) :
    False := by
  let raw : RawCyclicIncidenceData
      (fun i => ((F i).restrictCarrier P).carrier) :=
    ofBergeCycle c owner
      (fun i => ((F i).restrictCarrier P).carrier)
      hLeft hRight hOwnerNonconstant
  exact
    no_cyclicIncidenceData_of_forest_restriction
      hForest P hEdgePart raw.compress

/-- One-part specialization of
`no_nonconstant_owner_cycle_of_forest_restriction`. -/
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
    (hLeft :
      ∀ i,
        c.vertex i ∈
          ((F (owner i)).restrictCarrier P).carrier)
    (hRight :
      ∀ i,
        c.vertex i ∈
          ((F (owner (cyclicSucc i))).restrictCarrier P).carrier)
    (hOwnerNonconstant :
      ∃ i j : Fin c.length, owner i ≠ owner j) :
    False := by
  let raw : RawCyclicIncidenceData
      (fun i => ((F i).restrictCarrier P).carrier) :=
    ofBergeCycle c owner
      (fun i => ((F i).restrictCarrier P).carrier)
      hLeft hRight hOwnerNonconstant
  exact
    no_cyclicIncidenceData_of_forest_part
      hForest P hPart raw.compress

end RawCyclicIncidenceData

end StructuralRamsey.Girth
