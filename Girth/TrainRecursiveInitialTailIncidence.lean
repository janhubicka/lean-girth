import Girth.TrainRecursiveInitialTailGirth
import Girth.BoundaryIncidenceAcyclic
import Girth.IncidenceCompression

/-!
# Edge-only cycles and the labelled horizontal cut

Only connectors at genuine parent-wagon changes are used in the incidence
contradiction.  Such connectors must be vertices, and cyclic run compression
retains their actual incidence and distinctness.  The cut is restricted to
the finite set of parent labels which occur, without identifying carriers.

The quantitative hypothesis here is the number of those used parent labels.
The separate weighted-count argument must derive this number from the source
cycle's twice-order before applying the theorem to a system-girth cutoff.
-/

namespace StructuralRamsey.Girth

universe v

section Labelled

variable {V W Q : Type v}

/-- Forgetting the labels cannot create a physical Berge cycle.  Distinct
physical edges admit distinct choices of their original labels. -/
theorem LabelledGirthGT.range_girth {H : Q → Set V} {q : ℕ}
    (h : LabelledGirthGT H q) : GirthGT (Set.range H) q := by
  rintro ⟨c, hc⟩
  classical
  choose label hLabel using c.edge_mem
  let lifted : LabelledBergeCycle H := {
    length := c.length
    hlength := c.hlength
    label := label
    vertex := c.vertex
    label_injective := by
      intro i j hij
      apply c.edge_injective
      exact (hLabel i).symm.trans ((congrArg H hij).trans (hLabel j))
    vertex_injective := c.vertex_injective
    left_mem := by
      intro i
      rw [hLabel i]
      exact c.left_mem i
    right_mem := by
      intro i
      rw [hLabel (cyclicSucc i)]
      exact c.right_mem i
  }
  exact h ⟨lifted, hc⟩

/-- Injectively transporting vertices preserves a labelled girth bound. -/
theorem labelledGirthGT_image
    (H : Q → Set V) (f : V → W) (hf : Function.Injective f) (q : ℕ)
    (h : LabelledGirthGT H q) :
    LabelledGirthGT (fun p => f '' H p) q := by
  rintro ⟨c, hc⟩
  classical
  have hChoose (i : Fin c.length) : ∃ x, x ∈ H (c.label i) ∧ f x = c.vertex i :=
    c.left_mem i
  choose vertex hMem hVertex using hChoose
  let pulled : LabelledBergeCycle H := {
    length := c.length
    hlength := c.hlength
    label := c.label
    vertex := vertex
    label_injective := c.label_injective
    vertex_injective := by
      intro i j hij
      apply c.vertex_injective
      exact (hVertex i).symm.trans ((congrArg f hij).trans (hVertex j))
    left_mem := hMem
    right_mem := by
      intro i
      obtain ⟨x, hx, hfx⟩ := c.right_mem i
      have hEq : vertex i = x := hf ((hVertex i).trans hfx.symm)
      exact hEq.symm ▸ hx
  }
  exact h ⟨pulled, hc⟩

/-- The complete incidence graph of at most `q` labelled carriers is
acyclic under labelled girth greater than `q`. -/
theorem labelledGirthGT_incidence_acyclic_of_card
    [Fintype Q] (H : Q → Set V) (q : ℕ) (hq : 2 ≤ q)
    (hCard : Fintype.card Q ≤ q) (h : LabelledGirthGT H q) :
    (boundaryIncidenceGraph H).IsAcyclic := by
  exact boundaryIncidenceGraph_isAcyclic_of_pairwiseSubsingleton_of_girthGT
    H (fun {_ _} hne =>
      labelledGirthGT_two_pairwise_subsingleton (labelledGirthGT_mono h hq) _ _ hne)
    q hCard h.range_girth

end Labelled

namespace OrderOneData.BigCycle

variable {V E I P : Type v} {D : OrderOneData V E I P}
variable {n : ℕ} (C : D.BigCycle n)

/-- Under cut girth, an edge-only cycle with at most `q` distinct parent
labels has a constant parent label.  This theorem uses the actual labelled
cut and the actual source connectors, with no acceptability hypothesis.
-/
theorem parent_constant_of_labelledCutGirth_of_used_card
    (edge : Fin n → E) (hLabel : ∀ i, C.label i = Sum.inr (edge i))
    (q : ℕ) (hq : 2 ≤ q)
    (hCut : LabelledGirthGT (fun p => {x | D.WagonVertex p x}) q)
    (hCard : Nat.card (Set.range (fun i => D.parent (edge i))) ≤ q) :
    ∀ i j : Fin n, D.parent (edge i) = D.parent (edge j) := by
  classical
  by_contra hConstant
  push Not at hConstant
  obtain ⟨i, j, hij⟩ := hConstant
  let owner : Fin n → P := fun k => D.parent (edge k)
  let Used : Type v := Set.range owner
  let picked : Fin n → Used := fun k => ⟨owner k, ⟨k, rfl⟩⟩
  have hOnto : Function.Surjective picked := by
    rintro ⟨p, ⟨k, hk⟩⟩
    exact ⟨k, Subtype.ext hk⟩
  haveI : Finite Used := Finite.of_surjective picked hOnto
  letI : Fintype Used := Fintype.ofFinite Used
  let carrier : Used → Set (V ⊕ P) :=
    fun p => Sum.inl '' {x | D.WagonVertex p.val x}
  have hUsedGirth : LabelledGirthGT (fun p : Used => {x | D.WagonVertex p.val x}) q :=
    labelledGirthGT_of_injective_reindex _ Subtype.val Subtype.val_injective q hCut
  have hCarrierGirth : LabelledGirthGT carrier q :=
    labelledGirthGT_image _ Sum.inl Sum.inl_injective q hUsedGirth
  have hUsedCard : Fintype.card Used ≤ q := by
    simpa only [Nat.card_eq_fintype_card] using hCard
  have hAcyclic : (boundaryIncidenceGraph carrier).IsAcyclic :=
    labelledGirthGT_incidence_acyclic_of_card carrier q hq hUsedCard hCarrierGirth
  have hBoundary : ∀ k : Fin n, picked k ≠ picked (cyclicSucc k) →
      C.connector k ∈ carrier (picked k) ∧
        C.connector k ∈ carrier (picked (cyclicSucc k)) := by
    intro k hk
    have hLeft := C.left_incident k
    have hRight := C.right_incident k
    rw [hLabel k] at hLeft
    rw [hLabel (cyclicSucc k)] at hRight
    cases hConnector : C.connector k with
    | inl x =>
        rw [hConnector] at hLeft hRight
        exact ⟨⟨x, ⟨edge k, rfl, hLeft⟩, rfl⟩,
          ⟨x, ⟨edge (cyclicSucc k), rfl, hRight⟩, rfl⟩⟩
    | inr p =>
        rw [hConnector] at hLeft hRight
        obtain ⟨e, he, hep⟩ := hLeft
        obtain ⟨f, hf, hfp⟩ := hRight
        have heq : e = edge k := he
        have hfq : f = edge (cyclicSucc k) := hf
        subst e
        subst f
        exact (hk (Subtype.ext (hep.trans hfp.symm))).elim
  let raw : RawCyclicIncidenceData carrier := {
    length := n
    hlength := C.length_ge_two
    label := picked
    connector := C.connector
    connector_injective := C.connector_injective
    boundary_mem := hBoundary
    nonconstant := ⟨i, j, fun h => hij (congrArg Subtype.val h)⟩
  }
  exact CyclicIncidenceData.no_cyclicIncidenceData_of_acyclic hAcyclic raw.compress

end OrderOneData.BigCycle
end StructuralRamsey.Girth
