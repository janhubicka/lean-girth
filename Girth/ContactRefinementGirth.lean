import Girth.ContactCycleCompression
import Girth.ContactTrainData

/-! Single-part refinements yield the sharp hypergraph girth bound
used by the lexicographic induction. The descent uses actual
nested parent maps, with global labelled bounds at the proper
cuts. No auxiliary incidence acyclicity theorem is required. -/

namespace StructuralRamsey.Girth
universe v
variable {V E I Part : Type v}

namespace ContactHypergraphData
variable (D : ContactHypergraphData V E I)
variable {m : ℕ} (T : ContactTrainData E m)

def WagonBounds (q : Fin (m+1) → ℕ) : Prop :=
  ∀ μ, μ.val < m →
    LabelledGirthGT (D.atCut (T.parent μ)).contactWagonCarrier (q μ)

theorem systemBounds_wagonBounds {q : Fin (m+1) → ℕ}
    (h : D.SystemBounds T q) : D.WagonBounds T q :=
  fun μ hp => (h μ hp).g3

/-- Short edge cycles are contained in one wagon of the chosen
cut, by direct compression of their owner word. -/
theorem cycle_constant_at_cut (μ : Fin (m+1)) {g : ℕ}
    (hg : LabelledGirthGT (D.atCut (T.parent μ)).contactWagonCarrier g)
    (C : LabelledBergeCycle D.edgeCarrier) (hshort : C.length ≤ g) :
    ∀ i j, T.parent μ (C.label i) = T.parent μ (C.label j) := by
  classical
  let owner : Fin C.length → T.Wagon μ := fun i => T.parent μ (C.label i)
  let K := (D.atCut (T.parent μ)).contactWagonCarrier
  have hContain : ∀ i, D.edgeCarrier (C.label i) ⊆ K (owner i) :=
    fun i x hx => ⟨C.label i,rfl,hx⟩
  by_contra h
  have hnon : ¬ ∃ p, ∀ i, owner i = p := by
    rintro ⟨p,hp⟩
    apply h
    intro i j
    exact (hp i).trans (hp j).symm
  have hchanges := C.contact_changes_gt owner K hContain hg hnon
  have hc : contactOwnerChanges owner ≤ C.length := by
    rw [← contactOwnerCutPositions_card owner]
    simpa using Finset.card_le_card (Finset.subset_univ (contactOwnerCutPositions owner))
  omega

/-- If a cycle lies inside a parent wagon and its children meet
only in a single part, nonconstancy at the child cut forces
at least 2(g+1) physical edges. This is the manuscript's stronger
bound, not merely the historical gain by one. -/
theorem cycle_singlePart_step (μ ν : Fin (m+1)) (hle : μ ≤ ν)
    (part : V → Part) (allowed : Set Part) (hAllowed : allowed.Subsingleton)
    (hPart : ∀ e, Set.InjOn part (D.edgeCarrier e))
    (hparam : D.Parameter T μ ν (part ⁻¹' allowed))
    {g : ℕ} (hg : LabelledGirthGT (D.atCut (T.parent μ)).contactWagonCarrier g)
    (C : LabelledBergeCycle D.edgeCarrier)
    (hparent : ∀ i j, T.parent ν (C.label i) = T.parent ν (C.label j))
    (hshort : C.length ≤ 2*g+1) :
    ∀ i j, T.parent μ (C.label i) = T.parent μ (C.label j) := by
  classical
  let owner : Fin C.length → T.Wagon μ := fun i => T.parent μ (C.label i)
  let K := (D.atCut (T.parent μ)).contactWagonCarrier
  have hContain : ∀ i, D.edgeCarrier (C.label i) ⊆ K (owner i) :=
    fun i x hx => ⟨C.label i,rfl,hx⟩
  /- We only need the child intersection assertion for occurring
  child labels. This avoids assuming the parameter for unrelated
  coarser wagons. -/
  have hchange (i : Fin C.length) (hi : i ∈ contactOwnerCutPositions owner) :
      part (C.vertex i) ∈ allowed := by
    by_contra h
    exact ((mem_contactOwnerCutPositions_iff owner i).mp hi)
      (hparam (C.label i) (C.label (cyclicSucc i)) (C.vertex i)
        (hparent i (cyclicSucc i)) (C.left_mem i) (C.right_mem i) h)
  have hsep : ∀ i, i ∈ contactOwnerCutPositions owner →
      cyclicSucc i ∉ contactOwnerCutPositions owner := by
    intro i hi hj
    have he := hPart (C.label (cyclicSucc i)) (C.right_mem i)
      (C.left_mem (cyclicSucc i)) (hAllowed (hchange i hi) (hchange _ hj))
    exact contactSucc_ne C.hlength i (C.vertex_injective he).symm
  by_contra h
  have hnon : ¬ ∃ p, ∀ i, owner i = p := by
    rintro ⟨p,hp⟩
    apply h
    intro i j
    exact (hp i).trans (hp j).symm
  have hchanges := C.contact_changes_gt owner K hContain hg hnon
  have htwice := contact_twice_changes_le owner hsep
  omega

/-- The bottom cut can be treated without a separate girth
hypothesis: if the first parameter has at most one part,
a genuine cycle inside one first wagon is impossible. -/
theorem no_cycle_at_first_singlePart (hm : 0 < m)
    (part : V → Part) (allowed : Set Part) (hAllowed : allowed.Subsingleton)
    (hPart : ∀ e, Set.InjOn part (D.edgeCarrier e))
    (hparam : D.Parameter T ⟨0,by omega⟩ ⟨1,by omega⟩ (part ⁻¹' allowed))
    (C : LabelledBergeCycle D.edgeCarrier)
    (hparent : ∀ i j, T.parent ⟨1,by omega⟩ (C.label i) =
        T.parent ⟨1,by omega⟩ (C.label j)) : False := by
  let i : Fin C.length := ⟨0,by have := C.hlength; omega⟩
  have hall : ∀ j, part (C.vertex j) ∈ allowed := by
    intro j
    by_contra h
    have he := T.bottom (hparam (C.label j) (C.label (cyclicSucc j)) (C.vertex j)
      (hparent j _) (C.left_mem j) (C.right_mem j) h)
    exact contactSucc_ne C.hlength j (C.label_injective he).symm
  have he := hPart (C.label (cyclicSucc i)) (C.right_mem i)
    (C.left_mem (cyclicSucc i)) (hAllowed (hall i) (hall (cyclicSucc i)))
  exact contactSucc_ne C.hlength i (C.vertex_injective he).symm

/-- Descent through d single-part levels. Every d-wagon has girth
greater than 2g+1, including the case d=1, in which no positive
child-cut bound is needed. -/
theorem no_short_cycle_in_refined_wagon
    (d g : ℕ) (hd : 0 < d) (hdm : d ≤ m)
    (part : V → Part) (allowed : Fin m → Set Part)
    (hAllowed : ∀ j : Fin m, j.val < d → (allowed j).Subsingleton)
    (hPart : ∀ e, Set.InjOn part (D.edgeCarrier e))
    (hparam : D.Parameters T (fun j => part ⁻¹' allowed j))
    (hGirth : ∀ μ : Fin (m+1), 0 < μ.val → μ.val < d →
      LabelledGirthGT (D.atCut (T.parent μ)).contactWagonCarrier g)
    (C : LabelledBergeCycle D.edgeCarrier) (hshort : C.length ≤ 2*g+1)
    (hparent : ∀ i j, T.parent ⟨d,by omega⟩ (C.label i) =
      T.parent ⟨d,by omega⟩ (C.label j)) : False := by
  have aux : ∀ k : ℕ, ∀ hk : k ≤ d,
      (∀ i j, T.parent ⟨k,by omega⟩ (C.label i) =
        T.parent ⟨k,by omega⟩ (C.label j)) → False := by
    intro k
    induction k with
    | zero =>
      intro hk h
      let i : Fin C.length := ⟨0,by have := C.hlength; omega⟩
      have he := T.bottom (h i (cyclicSucc i))
      exact contactSucc_ne C.hlength i (C.label_injective he).symm
    | succ k ih =>
      intro hk h
      by_cases hk0 : k = 0
      · subst k
        exact D.no_cycle_at_first_singlePart T (by omega) part
          (allowed ⟨0,by omega⟩) (hAllowed _ (by omega)) hPart
          (hparam ⟨0,by omega⟩) C h
      · let j : Fin m := ⟨k,by omega⟩
        have hj : j.val < d := by change k < d; omega
        have hpos : 0 < j.castSucc.val := by change 0 < k; omega
        have hbelow : j.castSucc.val < d := hj
        have hle : j.castSucc ≤ j.succ := by change k ≤ k+1; omega
        have hchild := D.cycle_singlePart_step T j.castSucc j.succ hle part
          (allowed j) (hAllowed j hj) hPart (hparam j) (hGirth _ hpos hbelow) C h hshort
        exact ih (by omega) hchild
  exact aux d le_rfl hparent

/-- The global refinement gain follows by first localizing a
short edge cycle to a d-wagon. At universal top this containment
is automatic; otherwise the positive bound at the retained cut
supplies it. -/
theorem refined_edge_girth
    (d g q : ℕ) (hd : 0 < d) (hdm : d ≤ m) (hq : q ≤ 2*g+1)
    (part : V → Part) (allowed : Fin m → Set Part)
    (hAllowed : ∀ j : Fin m, j.val < d → (allowed j).Subsingleton)
    (hPart : ∀ e, Set.InjOn part (D.edgeCarrier e))
    (hparam : D.Parameters T (fun j => part ⁻¹' allowed j))
    (hGirth : ∀ μ : Fin (m+1), 0 < μ.val → μ.val < d →
      LabelledGirthGT (D.atCut (T.parent μ)).contactWagonCarrier g)
    (htail : d < m → LabelledGirthGT
      (D.atCut (T.parent ⟨d,by omega⟩)).contactWagonCarrier q) :
    LabelledGirthGT D.edgeCarrier q := by
  rintro ⟨C,hC⟩
  have hparent : ∀ i j, T.parent ⟨d,by omega⟩ (C.label i) =
      T.parent ⟨d,by omega⟩ (C.label j) := by
    by_cases h : d < m
    · exact D.cycle_constant_at_cut T ⟨d,by omega⟩ (htail h) C hC
    · have he : d = m := by omega
      subst m
      exact fun i j => T.top (C.label i) (C.label j)
  exact D.no_short_cycle_in_refined_wagon T d g hd hdm part allowed hAllowed
    hPart hparam hGirth C (hC.trans hq) hparent

end ContactHypergraphData
end StructuralRamsey.Girth
