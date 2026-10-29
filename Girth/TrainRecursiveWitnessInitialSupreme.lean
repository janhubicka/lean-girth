import Girth.TrainRecursiveWitnessInitial
import Girth.TrainShortOnlyPlanGlobal

/-!
# An occurring initial target is supreme in its own component

If a genuine cycle contains a designated label and all its other labels
are edges belonging to that copy, keep the designated occurrences and
replace each edge by itself.  The literal resulting word is unchanged,
so the original BigCycle certifies global legality, including length two.

The actual initial-picture corollary requires both an occurrence of the
selected component label and physical containment of every cycle label in
that component.  It does not choose an absent designated label.  This is
only the designated-occurrence case of the manuscript's picture-zero lemma:
cycle localization and exclusion of short edge-only cycles by the target's
horizontal-cut girth remain separate hypotheses and construction work.
-/

namespace StructuralRamsey.Girth.TrainRecursiveWitness

universe u v

/-- A present designated label is supreme if every different label is one
of its own actual edges.  The plan has the original cycle as its output. -/
theorem hasSupremeAt_of_other_labels_own_edges
    {V E Q W : Type v} (O : OrderOneData V E Q W)
    {n : ℕ} (C : O.BigCycle n) (k : Fin n)
    (hk : O.designated (C.label k))
    (hOther : ∀ j : Fin n, C.label j ≠ C.label k →
      ∃ e : E, C.label j = Sum.inr e ∧ e ∈ O.edges (C.label k)) :
    C.HasSupremeAt O k := by
  have hlabel : ∃ q : Q, C.label k = Sum.inl q := by
    cases h : C.label k with
    | inl q => exact ⟨q, rfl⟩
    | inr e => simp only [h, OrderOneData.designated] at hk
  obtain ⟨q, hq⟩ := hlabel
  let pieces : Fin n → TrainSupremePiece E W := fun j =>
    match C.label j with
    | .inl _ => .keep
    | .inr e => .short e
  refine ⟨hk, pieces, ?_, ?_⟩
  · intro j
    constructor
    · intro hj
      simp only [pieces, hj, hq]
    · intro hne
      obtain ⟨e, he, hown⟩ := hOther j hne
      simp only [pieces, he]
      refine ⟨hown, ?_, ?_⟩
      · have hp := C.right_incident (trainCyclicPred j)
        simpa only [cyclicSucc_trainCyclicPred_of_two_le C.length_ge_two j, he] using hp
      · simpa only [he] using C.left_incident j
  · refine ⟨n, C, ?_⟩
    symm
    unfold OrderOneData.BigCycle.resultWord
    have hword : (fun j : Fin n => C.pieceWord O j (pieces j)) =
        (fun j : Fin n => [(C.label j, C.connector j)]) := by
      funext j
      cases h : C.label j <;>
        simp only [pieces, h, OrderOneData.BigCycle.pieceWord]
    rw [hword]
    exact flatten_ofFn_singleton (fun j : Fin n => (C.label j, C.connector j))

open StructuralRamsey.RelStructure

variable {L : RelLanguage.{u}} {UA VB P : Type v}

/-- The literal selected B-copy is supreme in a cycle physically contained
in that initial component and containing that actual selected label.  No
system-girth premise, replacement plan, or edge-only-cycle exclusion is
assumed or concluded here.
-/
theorem initialCycle_hasSupremeAt_of_contained
    (A : RelStructure L UA) (B : RelStructure L VB) [Nonempty VB]
    (D : RelStructure L P) (family : Set (RelStructure.Embedding B D))
    {m : ℕ}
    (T : EdgeTrainLevels (OldACarrierEdge A
      (StructuralRamsey.Partite.Initial.picture B
        (fun b : family => b.1.toFunctionEmbedding)).toRelStructure) m)
    (μ : Fin (m + 1)) {n : ℕ}
    (C : (selectedPictureOrderOneData A B D
      (StructuralRamsey.Partite.Initial.picture B
        (fun b : family => b.1.toFunctionEmbedding))
      family (initialSelected B D family) T μ).BigCycle n)
    (b : family) (k : Fin n)
    (hOccurs : C.label k = Sum.inl
      ⟨initialDesignatedCopy B D family b, ⟨b, rfl⟩⟩)
    (hContained : ∀ j : Fin n,
      (selectedPictureOrderOneData A B D
        (StructuralRamsey.Partite.Initial.picture B
          (fun b : family => b.1.toFunctionEmbedding))
        family (initialSelected B D family) T μ).carrier (C.label j) ⊆
        copyCarrier (initialDesignatedCopy B D family b).embedding) :
    C.HasSupremeAt _ k := by
  let O := selectedPictureOrderOneData A B D
    (StructuralRamsey.Partite.Initial.picture B
      (fun b : family => b.1.toFunctionEmbedding))
    family (initialSelected B D family) T μ
  apply hasSupremeAt_of_other_labels_own_edges O C k
  · rw [hOccurs]
    trivial
  · intro j hne
    cases hj : C.label j with
    | inr e =>
        refine ⟨e, rfl, ?_⟩
        rw [hOccurs]
        have hsub := hContained j
        rw [hj] at hsub
        exact hsub
    | inl q =>
        rcases q with ⟨q, hq⟩
        obtain ⟨c, rfl⟩ := hq
        have hsub := hContained j
        rw [hj] at hsub
        change copyCarrier (initialDesignatedCopy B D family c).embedding ⊆
          copyCarrier (initialDesignatedCopy B D family b).embedding at hsub
        obtain ⟨v⟩ := (inferInstance : Nonempty VB)
        obtain ⟨w, hw⟩ := hsub (show (c, v) ∈
          copyCarrier (initialDesignatedCopy B D family c).embedding from ⟨v, rfl⟩)
        have hcb : c = b := (congrArg Prod.fst hw).symm
        subst c
        exact (hne (hj.trans hOccurs.symm)).elim

end StructuralRamsey.Girth.TrainRecursiveWitness
