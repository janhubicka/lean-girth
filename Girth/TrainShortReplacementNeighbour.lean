import Girth.TrainSingleShortReplacement
import Mathlib.Tactic

/-!
# Circulation: short witnesses are automatically distinct from neighbours

Acceptability already contains the geometric obstruction needed for the
remaining short-replacement legality check.  An actual edge cannot be incident
with three distinct connector positions of an acceptable big cycle:
if its wagon occurs as a connector, A2 confines all incident vertices to the
two neighbouring positions and forbids one edge through both; if it does not,
A3 confines all incident vertices to two positions.

Consequently, on a cycle of length at least three, an edge incident with the
two boundary connectors of one occurrence cannot equal either neighbouring
edge label.  This is exactly the adjacent-label check needed by the
one-occurrence replacement kernel.
-/

namespace StructuralRamsey.Girth

/-- In a cycle with at least three positions, predecessor and successor of one
position are different. -/
theorem trainCyclicPred_ne_cyclicSucc_of_three_le
    {n : ℕ} (hn : 3 ≤ n) (i : Fin n) :
    trainCyclicPred i ≠ cyclicSucc i := by
  intro h
  have hv := congrArg Fin.val h
  simp only [trainCyclicPred, cyclicSucc, Fin.val_mk] at hv
  by_cases hz : i.val = 0
  · have hm : n - 1 < n := by omega
    have h1 : 1 < n := by omega
    simp [hz, Nat.mod_eq_of_lt hm, Nat.mod_eq_of_lt h1] at hv
    omega
  · have hp : (i.val + n - 1) % n = i.val - 1 := by
      have heq : i.val + n - 1 = n + (i.val - 1) := by omega
      rw [heq]
      have hlt : i.val - 1 < n := by omega
      simpa [Nat.add_mod, Nat.mod_eq_of_lt hlt]
    rw [hp] at hv
    by_cases hs : i.val + 1 < n
    · rw [Nat.mod_eq_of_lt hs] at hv
      omega
    · have hsEq : i.val + 1 = n := by omega
      rw [hsEq, Nat.mod_self] at hv
      omega

namespace OrderOneData

universe v
variable {V E I P : Type v} (D : OrderOneData V E I P)

/-- Three distinct points cannot all lie in a two-point set. -/
private theorem three_not_two {α : Type v}
    {i j k a b : α} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hi : i = a ∨ i = b) (hj : j = a ∨ j = b)
    (hk : k = a ∨ k = b) : False := by
  rcases hi with hi | hi <;>
    rcases hj with hj | hj <;>
    rcases hk with hk | hk <;>
    subst_vars <;> contradiction

/-- An actual edge of an acceptable big cycle is incident with at most two
connector positions.  The statement is phrased as exclusion of three distinct
positions, which is the form needed for replacement legality. -/
theorem BigCycle.not_edge_incident_three_distinct
    {n : ℕ} (C : D.BigCycle n) (hAccept : C.Acceptable)
    (e : E) (i j k : Fin n)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hi : D.Incident (.inr e) (C.connector i))
    (hj : D.Incident (.inr e) (C.connector j))
    (hk : D.Incident (.inr e) (C.connector k)) : False := by
  let p := D.parent e
  have classify (t : Fin n)
      (ht : D.Incident (.inr e) (C.connector t)) :
      (∃ x : V, C.connector t = .inl x ∧ x ∈ D.edgeCarrier e) ∨
        C.connector t = .inr p := by
    cases hct : C.connector t with
    | inl x =>
        left
        refine ⟨x, rfl, ?_⟩
        simpa [Incident, carrier] using ht
    | inr q =>
        right
        have ht' : D.Meets (.inr e) q := by
          simpa [Incident] using ht
        rcases ht' with ⟨f, hf, hfp⟩
        have hfe : f = e := by simpa [OrderOneData.edges] using hf
        subst f
        simpa [p] using congrArg (fun z => Sum.inr z) hfp.symm
  have inWagon {t : Fin n} {x : V}
      (hcx : C.connector t = .inl x) (hxe : x ∈ D.edgeCarrier e) :
      C.InWagonAt p t :=
    ⟨x, hcx, ⟨e, rfl, hxe⟩⟩
  have oneWagon (w u v : Fin n)
      (hw : C.connector w = .inr p)
      (huv : u ≠ v)
      (hu : ∃ x : V, C.connector u = .inl x ∧ x ∈ D.edgeCarrier e)
      (hv : ∃ y : V, C.connector v = .inl y ∧ y ∈ D.edgeCarrier e) : False := by
    rcases hu with ⟨x, hux, hxe⟩
    rcases hv with ⟨y, hvy, hye⟩
    have hxu := hAccept.2.1.1 w p hw u (inWagon hux hxe)
    have hyv := hAccept.2.1.1 w p hw v (inWagon hvy hye)
    have hNeighbors : trainCyclicPred w ≠ cyclicSucc w := by
      intro hps
      apply huv
      rcases hxu with huPred | huSucc <;>
        rcases hyv with hvPred | hvSucc <;> aesop
    rcases hxu with huPred | huSucc <;>
      rcases hyv with hvPred | hvSucc
    · exact huv (huPred.trans hvPred.symm)
    · have hleft : C.connector (trainCyclicPred w) = .inl x := by
        rw [← huPred]
        exact hux
      have hright : C.connector (cyclicSucc w) = .inl y := by
        rw [← hvSucc]
        exact hvy
      exact (hAccept.2.1.2 w p x y hw hleft hright hNeighbors
        ⟨e, rfl, hxe⟩ ⟨e, rfl, hye⟩) ⟨e, hxe, hye⟩
    · have hleft : C.connector (trainCyclicPred w) = .inl y := by
        rw [← hvPred]
        exact hvy
      have hright : C.connector (cyclicSucc w) = .inl x := by
        rw [← huSucc]
        exact hux
      exact (hAccept.2.1.2 w p y x hw hleft hright hNeighbors
        ⟨e, rfl, hye⟩ ⟨e, rfl, hxe⟩) ⟨e, hye, hxe⟩
    · exact huv (huSucc.trans hvSucc.symm)
  rcases classify i hi with hiV | hiW
  · rcases classify j hj with hjV | hjW
    · rcases classify k hk with hkV | hkW
      · have wi := inWagon hiV.choose_spec.1 hiV.choose_spec.2
        have wj := inWagon hjV.choose_spec.1 hjV.choose_spec.2
        have wk := inWagon hkV.choose_spec.1 hkV.choose_spec.2
        by_cases hc : ∃ t : Fin n, C.connector t = .inr p
        · rcases hc with ⟨t, ht⟩
          exact three_not_two hij hik hjk
            (hAccept.2.1.1 t p ht i wi)
            (hAccept.2.1.1 t p ht j wj)
            (hAccept.2.1.1 t p ht k wk)
        · have hc' : ∀ t : Fin n, C.connector t ≠ .inr p := by
            intro t ht
            exact hc ⟨t, ht⟩
          rcases hAccept.2.2 p hc' with ⟨t, ht⟩
          exact three_not_two hij hik hjk
            (ht i wi) (ht j wj) (ht k wk)
      · exact oneWagon k i j hkW hij hiV hjV
    · rcases classify k hk with hkV | hkW
      · exact oneWagon j i k hjW hik hiV hkV
      · exact hij (C.connector_injective
          (Eq.trans hiW (Eq.symm hjW)))
  · rcases classify j hj with hjV | hjW
    · rcases classify k hk with hkV | hkW
      · exact oneWagon i j k hiW hjk hjV hkV
      · exact hik (C.connector_injective
          (Eq.trans hiW (Eq.symm hkW)))
    · rcases classify k hk with hkV | hkW
      · exact hjk (C.connector_injective
          (Eq.trans hjW (Eq.symm hkW)))
      · exact hij (C.connector_injective
          (Eq.trans hiW (Eq.symm hjW)))

/-- On a cycle of length at least three, an actual edge incident with the two
boundary connectors of occurrence j differs from both neighbouring labels. -/
theorem BigCycle.shortEdge_ne_neighbors
    {n : ℕ} (C : D.BigCycle n) (hAccept : C.Acceptable) (hn : 3 ≤ n)
    (j : Fin n) (e : E)
    (hPred : D.Incident (.inr e) (C.connector (trainCyclicPred j)))
    (hHere : D.Incident (.inr e) (C.connector j)) :
    C.label (trainCyclicPred j) ≠ .inr e ∧
      (.inr e : I ⊕ E) ≠ C.label (cyclicSucc j) := by
  have hSuccSelf : j ≠ cyclicSucc j := by
    intro h
    exact C.adjacent_ne j (congrArg C.label h)
  have hPredSelf : trainCyclicPred j ≠ j := by
    intro h
    have hs := cyclicSucc_trainCyclicPred_of_two_le C.length_ge_two j
    rw [h] at hs
    exact hSuccSelf hs.symm
  have hPredSucc : trainCyclicPred j ≠ cyclicSucc j :=
    trainCyclicPred_ne_cyclicSucc_of_three_le hn j
  constructor
  · intro hEq
    let t := trainCyclicPred j
    have hSuccT : cyclicSucc t = j :=
      cyclicSucc_trainCyclicPred_of_two_le C.length_ge_two j
    have hPrevPrev : D.Incident (.inr e)
        (C.connector (trainCyclicPred t)) := by
      have h := C.right_incident (trainCyclicPred t)
      have hs := cyclicSucc_trainCyclicPred_of_two_le C.length_ge_two t
      rw [hs, hEq] at h
      exact h
    exact C.not_edge_incident_three_distinct D hAccept e
      (trainCyclicPred t) t j
      (by
        intro h
        have hs := cyclicSucc_trainCyclicPred_of_two_le C.length_ge_two t
        rw [h] at hs
        exact C.adjacent_ne t (congrArg C.label hs.symm))
      (by
        intro h
        exact (trainCyclicPred_ne_cyclicSucc_of_three_le hn t)
          (h.trans hSuccT.symm))
      (by simpa [t] using hPredSelf)
      hPrevPrev hPred hHere
  · intro hEq
    have hNext : D.Incident (.inr e) (C.connector (cyclicSucc j)) := by
      have h := C.left_incident (cyclicSucc j)
      rw [← hEq] at h
      exact h
    exact C.not_edge_incident_three_distinct D hAccept e
      (trainCyclicPred j) j (cyclicSucc j)
      hPredSelf hPredSucc hSuccSelf hPred hHere hNext

end OrderOneData
end StructuralRamsey.Girth
