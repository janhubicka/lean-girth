import Girth.TrainSupremePlanTransport

set_option Elab.async false

/-!
# Exact designated-label reindexing preserves full system girth

The indexed old-copy model and the actual selected-copy model use different
types for their designated labels.  A genuine equivalence of those labels
changes neither the physical edges, vertices, wagons, nor edge ownership.
Every acceptable cycle pulls back with the same connectors and order, and
the literal physical map transports its entire legal simultaneous plan.

This is a bijective reindexing, not an identification of labels with equal
carriers.  In particular, it does not justify deleting duplicate-looking
copies or replacing the global replacement condition by local pieces.
-/

namespace StructuralRamsey.Girth.OrderOneData

universe v
variable {V E I J P : Type v} (D : OrderOneData V E I P) (e : J ≃ I)

/-- Rename designated copies by an equivalence. All physical data are fixed. -/
def reindexDesignated : OrderOneData V E J P where
  edgeCarrier := D.edgeCarrier
  copyCarrier := fun j => D.copyCarrier (e j)
  copyEdges := fun j => D.copyEdges (e j)
  parent := D.parent

private def reindexToOriginal : LiteralPhysicalMap (D.reindexDesignated e) D where
  vertex := Function.Embedding.refl V
  edge := Function.Embedding.refl E
  designated := e.toEmbedding
  wagon := Function.Embedding.refl P
  incident := by
    intro a z h
    cases a <;> cases z <;> exact h
  source_edge := by
    intro a x h
    cases a <;> exact h
  parent := fun _ => rfl
  no_new_pair := fun _ _ _ h => h

private def reindexFromOriginal : LiteralPhysicalMap D (D.reindexDesignated e) where
  vertex := Function.Embedding.refl V
  edge := Function.Embedding.refl E
  designated := e.symm.toEmbedding
  wagon := Function.Embedding.refl P
  incident := by
    intro a z h
    cases a with
    | inl i =>
        cases z <;>
          simpa [Incident, carrier, Meets, edges, reindexDesignated] using h
    | inr x => cases z <;> exact h
  source_edge := by
    intro a x h
    cases a with
    | inl i => simpa [edges, reindexDesignated] using h
    | inr y => exact h
  parent := fun _ => rfl
  no_new_pair := fun _ _ _ h => h

private theorem reindex_incident (a : J ⊕ E) (z : V ⊕ P) :
    (D.reindexDesignated e).Incident a z ↔
      D.Incident (Sum.map e id a) z := by
  cases a <;> cases z <;> rfl

private def reindexPullCycle {n : ℕ}
    (C : (D.reindexDesignated e).BigCycle n) : D.BigCycle n where
  length_ge_two := C.length_ge_two
  label := fun j => Sum.map e id (C.label j)
  connector := C.connector
  adjacent_ne := by
    intro j hj
    exact C.adjacent_ne j ((D.reindexToOriginal e).mapLabel_injective hj)
  connector_injective := C.connector_injective
  left_incident := fun j => (reindex_incident D e _ _).mp (C.left_incident j)
  right_incident := fun j => (reindex_incident D e _ _).mp (C.right_incident j)

private theorem reindexPull_order {n : ℕ}
    (C : (D.reindexDesignated e).BigCycle n) :
    (D.reindexPullCycle e C).twiceOrder = C.twiceOrder := rfl

private theorem reindexPull_acceptable {n : ℕ}
    (C : (D.reindexDesignated e).BigCycle n) (h : C.Acceptable) :
    (D.reindexPullCycle e C).Acceptable := by
  refine ⟨?_, h.2.1, h.2.2⟩
  intro ho
  obtain ⟨j, hj⟩ := h.1 ho
  refine ⟨j, ?_⟩
  change D.designated (Sum.map e id (C.label j))
  cases hLabel : C.label j with
  | inl i => trivial
  | inr x => simp [hLabel, designated] at hj

private theorem reindexPull_map_eq {n : ℕ}
    (C : (D.reindexDesignated e).BigCycle n) :
    (D.reindexFromOriginal e).mapBigCycle (D.reindexPullCycle e C) = C := by
  have hl : ((D.reindexFromOriginal e).mapBigCycle
      (D.reindexPullCycle e C)).label = C.label := by
    funext j
    change Sum.map e.symm id (Sum.map e id (C.label j)) = C.label j
    cases C.label j <;> simp
  have hc : ((D.reindexFromOriginal e).mapBigCycle
      (D.reindexPullCycle e C)).connector = C.connector := by
    funext j
    change Sum.map id id (C.connector j) = C.connector j
    cases C.connector j <;> rfl
  generalize (D.reindexFromOriginal e).mapBigCycle
    (D.reindexPullCycle e C) = Z at *
  cases Z
  cases C
  cases hl
  cases hc
  rfl

private theorem reindex_supreme_forward {q : ℕ} (h : D.SupremeCycleBound q) :
    (D.reindexDesignated e).SupremeCycleBound q := by
  intro n C ha ho
  have hs := h n (D.reindexPullCycle e C)
    (D.reindexPull_acceptable e C ha) ho
  have hm := (D.reindexFromOriginal e).hasSimultaneousSupreme_map
    (D.reindexPullCycle e C) hs
  rw [reindexPull_map_eq] at hm
  exact hm

private theorem reindex_twice :
    (D.reindexDesignated e).reindexDesignated e.symm = D := by
  cases D
  simp [reindexDesignated]

/-- Physical edge and wagon linearity are unchanged by designated reindexing. -/
theorem reindexDesignated_linearPretrain_iff :
    (D.reindexDesignated e).LinearPretrain ↔ D.LinearPretrain := Iff.rfl

/-- The exact full simultaneous replacement bound is invariant under
bijective designated-label reindexing, including the resulting BigCycle. -/
theorem reindexDesignated_supremeCycleBound_iff (q : ℕ) :
    (D.reindexDesignated e).SupremeCycleBound q ↔ D.SupremeCycleBound q := by
  constructor
  · intro h
    have ht := reindex_supreme_forward (D.reindexDesignated e) e.symm h
    rw [reindex_twice] at ht
    exact ht
  · exact reindex_supreme_forward D e

/-- Full system girth has exactly the same numerical cutoff after a genuine
equivalence of designated labels. No geometric conclusion is an input. -/
theorem reindexDesignated_fullSystemGirth_iff (q : ℕ) :
    (D.reindexDesignated e).FullSystemGirthGT q ↔ D.FullSystemGirthGT q := by
  exact and_congr (D.reindexDesignated_linearPretrain_iff e)
    (D.reindexDesignated_supremeCycleBound_iff e q)

end StructuralRamsey.Girth.OrderOneData
