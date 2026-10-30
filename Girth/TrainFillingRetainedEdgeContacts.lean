import Girth.TrainFillingContractionPositions
import Girth.TrainShortReplacementNeighbour

/-!
# Old edges meet at most two retained filling connectors

An old edge may meet three original connectors: two vertices and its
wagon. Exactly that configuration makes the wagon contractible. After
deleting all such wagons, no old edge meets three retained positions.
No projected cycle, normalization, or pretrain linearity is assumed.
-/
namespace StructuralRamsey.Girth.TrainFilling
universe v
variable {V I P : Type v}
variable (F : TrainFilling V) (copyCarrier : I → Set V)
variable (copyEdges : I → Set F.OldEdge) (parent : F.OldEdge → P)
local notation "O" => F.oldData copyCarrier copyEdges parent
local notation "H" => F.filledData copyCarrier copyEdges parent

private theorem three_positions_not_two {α : Type v}
    {i j k a b : α} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hi : i = a ∨ i = b) (hj : j = a ∨ j = b)
    (hk : k = a ∨ k = b) : False := by
  rcases hi with hi | hi <;> rcases hj with hj | hj <;>
    rcases hk with hk | hk <;> subst_vars <;> contradiction

theorem old_edge_incidence_cases (f : F.OldEdge) (q : V ⊕ P)
    (h : (O).Incident (.inr f) q) :
    (∃ x : V, q = Sum.inl x ∧ x ∈ f.1) ∨ q = Sum.inr (parent f) := by
  cases q with
  | inl x => exact Or.inl ⟨x, rfl, h⟩
  | inr p =>
      obtain ⟨g, hgf, hgp⟩ := h
      have hg : g = f := hgf
      subst g
      exact Or.inr (congrArg Sum.inr hgp.symm)

/-- Source-side exclusion; it is not inferred from projected legality. -/
theorem old_edge_not_incident_three_retained
    {n : ℕ} (C : (H).BigCycle n) (hA2 : C.A2) (hA3 : C.A3)
    (f : F.OldEdge) (i j k : Fin n)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hRi : ¬ F.ContractibleBlock copyCarrier copyEdges parent C i)
    (hRj : ¬ F.ContractibleBlock copyCarrier copyEdges parent C j)
    (hRk : ¬ F.ContractibleBlock copyCarrier copyEdges parent C k)
    (hi : (O).Incident (.inr f) (C.connector i))
    (hj : (O).Incident (.inr f) (C.connector j))
    (hk : (O).Incident (.inr f) (C.connector k)) : False := by
  let p := parent f
  have inParent (x : V) (hx : x ∈ f.1) : (H).WagonVertex p x :=
    (F.wagonVertex_filled_iff_old copyCarrier copyEdges parent p x).mpr ⟨f, rfl, hx⟩
  have inWagon {t : Fin n} {x : V}
      (ht : C.connector t = Sum.inl x) (hx : x ∈ f.1) :
      C.InWagonAt p t := ⟨x, ht, inParent x hx⟩
  have oneWagon (w u z : Fin n)
      (hw : C.connector w = Sum.inr p)
      (hR : ¬ F.ContractibleBlock copyCarrier copyEdges parent C w)
      (huz : u ≠ z)
      (hu : ∃ x : V, C.connector u = Sum.inl x ∧ x ∈ f.1)
      (hz : ∃ y : V, C.connector z = Sum.inl y ∧ y ∈ f.1) : False := by
    obtain ⟨x, hux, hxf⟩ := hu
    obtain ⟨y, hzy, hyf⟩ := hz
    have hpu := hA2.1 w p hw u (inWagon hux hxf)
    have hpz := hA2.1 w p hw z (inWagon hzy hyf)
    have hNeighbours : trainCyclicPred w ≠ cyclicSucc w := by
      intro h
      apply huz
      rcases hpu with hpu | hpu <;> rcases hpz with hpz | hpz <;> aesop
    apply hR
    rcases hpu with hpu | hpu <;> rcases hpz with hpz | hpz
    · exact False.elim (huz (hpu.trans hpz.symm))
    · refine ⟨p, x, y, hw, ?_, ?_, hNeighbours,
        inParent x hxf, inParent y hyf, f, hxf, hyf⟩
      · rw [← hpu]; exact hux
      · rw [← hpz]; exact hzy
    · refine ⟨p, y, x, hw, ?_, ?_, hNeighbours,
        inParent y hyf, inParent x hxf, f, hyf, hxf⟩
      · rw [← hpz]; exact hzy
      · rw [← hpu]; exact hux
    · exact False.elim (huz (hpu.trans hpz.symm))
  rcases F.old_edge_incidence_cases copyCarrier copyEdges parent f _ hi with hiV | hiW
  · rcases F.old_edge_incidence_cases copyCarrier copyEdges parent f _ hj with hjV | hjW
    · rcases F.old_edge_incidence_cases copyCarrier copyEdges parent f _ hk with hkV | hkW
      · have wi := inWagon hiV.choose_spec.1 hiV.choose_spec.2
        have wj := inWagon hjV.choose_spec.1 hjV.choose_spec.2
        have wk := inWagon hkV.choose_spec.1 hkV.choose_spec.2
        by_cases hOccurs : ∃ t : Fin n, C.connector t = Sum.inr p
        · obtain ⟨t, ht⟩ := hOccurs
          exact three_positions_not_two hij hik hjk
            (hA2.1 t p ht i wi) (hA2.1 t p ht j wj) (hA2.1 t p ht k wk)
        · have hAbsent : ∀ t : Fin n, C.connector t ≠ Sum.inr p := by
            intro t ht
            exact hOccurs ⟨t, ht⟩
          obtain ⟨t, ht⟩ := hA3 p hAbsent
          exact three_positions_not_two hij hik hjk (ht i wi) (ht j wj) (ht k wk)
      · exact oneWagon k i j hkW hRk hij hiV hjV
    · rcases F.old_edge_incidence_cases copyCarrier copyEdges parent f _ hk with hkV | hkW
      · exact oneWagon j i k hjW hRj hik hiV hkV
      · exact hjk (C.connector_injective (hjW.trans hkW.symm))
  · rcases F.old_edge_incidence_cases copyCarrier copyEdges parent f _ hj with hjV | hjW
    · rcases F.old_edge_incidence_cases copyCarrier copyEdges parent f _ hk with hkV | hkW
      · exact oneWagon i j k hiW hRi hjk hjV hkV
      · exact hik (C.connector_injective (hiW.trans hkW.symm))
    · exact hij (C.connector_injective (hiW.trans hjW.symm))

private theorem three_cyclic_positions {m : ℕ} (hm : 3 ≤ m) (j : Fin m) :
    trainCyclicPred j ≠ j ∧ j ≠ cyclicSucc j ∧
      trainCyclicPred j ≠ cyclicSucc j := by
  have hTwo : 2 ≤ m := by omega
  have hps := trainCyclicPred_ne_cyclicSucc_of_three_le hm j
  have hs : j ≠ cyclicSucc j := by
    intro h
    have hp := congrArg trainCyclicPred h
    rw [trainCyclicPred_cyclicSucc_of_two_le hTwo] at hp
    exact hps (hp.trans h)
  refine ⟨?_, hs, hps⟩
  intro h
  have hnext := cyclicSucc_trainCyclicPred_of_two_le hTwo j
  rw [h] at hnext
  exact hs hnext.symm

/-- Incidence proves the missing adjacent-edge inequality of a projected
word of length at least three. The word is NOT assumed to be a BigCycle. -/
theorem projected_adjacent_edge_ne
    {n m : ℕ} (C : (H).BigCycle n) (hA2 : C.A2) (hA3 : C.A3)
    (hm : 3 ≤ m) (position : Fin m ↪o Fin n)
    (hRetained : ∀ j, ¬ F.ContractibleBlock copyCarrier copyEdges parent C (position j))
    (label : Fin m → I ⊕ F.OldEdge)
    (hLeft : ∀ j, (O).Incident (label j) (C.connector (position j)))
    (hRight : ∀ j, (O).Incident (label (cyclicSucc j))
      (C.connector (position j)))
    (j : Fin m) (f : F.OldEdge)
    (hj : label j = Sum.inr f)
    (hNext : label (cyclicSucc j) = Sum.inr f) : False := by
  have hTwo : 2 ≤ m := by omega
  have hIndices := three_cyclic_positions hm j
  have hPredInc : (O).Incident (.inr f)
      (C.connector (position (trainCyclicPred j))) := by
    have h := hRight (trainCyclicPred j)
    rw [cyclicSucc_trainCyclicPred_of_two_le hTwo, hj] at h
    exact h
  apply F.old_edge_not_incident_three_retained copyCarrier copyEdges parent
    C hA2 hA3 f (position (trainCyclicPred j)) (position j)
    (position (cyclicSucc j))
    (fun h => hIndices.1 (position.injective h))
    (fun h => hIndices.2.2 (position.injective h))
    (fun h => hIndices.2.1 (position.injective h))
    (hRetained _) (hRetained _) (hRetained _) hPredInc
  · simpa only [hj] using hLeft j
  · simpa only [hNext] using hLeft (cyclicSucc j)
end StructuralRamsey.Girth.TrainFilling
