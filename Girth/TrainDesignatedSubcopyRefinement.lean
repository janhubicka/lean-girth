import Girth.TrainDesignatedSubcopyProjection
import Girth.TrainOldPosPieceTransfer
import Girth.TrainOptionalFreshnessConverse

/-!
# Circulation: refine a literal old-parent replacement to target labels

Enlarging a target cycle forgets which component target each retained
designated occurrence names. A genuine literal replacement cycle of that
enlargement can be refined back: keep exactly the same edges and connectors,
and restore the original target label at every retained occurrence.

The old output supplies global adjacent-label distinctness and connector
injectivity. For a restored target, both boundary incidences come from the
original target cycle. The checked no-insertion predecessor identity locates
its preceding boundary even across the cyclic wrap. Thus this is valid at
every source length, including two, without an extra legality hypothesis on
the refined word or a local-validity-to-global inference.

The theorem applies to arbitrary literal replacement pieces, not only to
supreme plans. Plan validity is needed elsewhere to derive old-parent edge
membership and retained-target provenance, but not for this refinement.
-/

namespace StructuralRamsey.Girth.OrderOneData.DesignatedSubcopyFamily

universe v
variable {V E I J P : Type v}
variable {D : OrderOneData V E I P} (S : DesignatedSubcopyFamily D J)

/-- Enlarge only the designated label in a cyclic-word entry. -/
def enlargeEntry (a : (J ⊕ E) × (V ⊕ P)) : (I ⊕ E) × (V ⊕ P) :=
  (S.enlargeLabel a.1, a.2)

theorem pieceWord_enlargeCycle
    {n : ℕ} (C : S.target.BigCycle n) (i : Fin n)
    (piece : TrainSupremePiece E P) :
    (S.enlargeCycle C).pieceWord D i piece =
      (C.pieceWord S.target i piece).map S.enlargeEntry := by
  cases piece <;> rfl

/-- The complete ordered replacement word commutes with enlargement,
including every inserted wagon and both edges of every long piece. -/
theorem resultWord_enlargeCycle
    {n : ℕ} (C : S.target.BigCycle n)
    (pieces : Fin n → TrainSupremePiece E P) :
    (S.enlargeCycle C).resultWord D pieces =
      (C.resultWord S.target pieces).map S.enlargeEntry := by
  simp only [BigCycle.resultWord, List.map_flatten, List.map_ofFn,
    S.pieceWord_enlargeCycle, Function.comp_def]

/-- Actual edge incidence is identical in the two designated systems. -/
theorem target_incident_edge_iff (e : E) (c : V ⊕ P) :
    S.target.Incident (.inr e) c ↔ D.Incident (.inr e) c := by
  cases c <;> rfl

/-- A designated entry of the literal target word is an unchanged source
occurrence. This is proved before the target output cycle is constructed. -/
private theorem kept_target_of_word_member
    {n : ℕ} (C : S.target.BigCycle n)
    (pieces : Fin n → TrainSupremePiece E P) (target : J) (c : V ⊕ P)
    (hMem : (Sum.inl target, c) ∈ C.resultWord S.target pieces) :
    ∃ s : Fin n, pieces s = .keep ∧
      C.label s = Sum.inl target ∧ C.connector s = c := by
  unfold BigCycle.resultWord at hMem
  obtain ⟨block, hBlock, hEntry⟩ := List.mem_flatten.mp hMem
  obtain ⟨s, rfl⟩ := List.mem_ofFn.mp hBlock
  cases hp : pieces s with
  | keep =>
      have hEq : (Sum.inl target, c) = (C.label s, C.connector s) := by
        simpa [BigCycle.pieceWord, hp] using hEntry
      exact ⟨s, hp, (congrArg Prod.fst hEq).symm,
        (congrArg Prod.snd hEq).symm⟩
  | short e => simp [BigCycle.pieceWord, hp] at hEntry
  | long e p f => simp [BigCycle.pieceWord, hp] at hEntry

/-- Every globally legal literal replacement of the enlarged parent cycle
refines to a globally legal literal replacement of the original target
cycle. No new physical incidence or output-cycle assumption is supplied.

All source lengths are covered. In particular the length-two case uses the
same checked old output and predecessor identity as the general case. -/
theorem planProducesBigCycle_of_enlargeCycle
    {n : ℕ} (C : S.target.BigCycle n)
    (pieces : Fin n → TrainSupremePiece E P)
    (hGlobal : (S.enlargeCycle C).PlanProducesBigCycle D pieces) :
    C.PlanProducesBigCycle S.target pieces := by
  classical
  obtain ⟨m, B, hWord⟩ := hGlobal
  let W := C.resultWord S.target pieces
  have hMapped : List.ofFn (fun t : Fin m => (B.label t, B.connector t)) =
      W.map S.enlargeEntry :=
    hWord.trans (S.resultWord_enlargeCycle C pieces)
  have hLength : m = W.length := by
    have h := congrArg List.length hMapped
    simpa only [List.length_ofFn, List.length_map] using h
  subst m

  have hEntryMap (t : Fin W.length) :
      (B.label t, B.connector t) = S.enlargeEntry (W.get t) := by
    apply Option.some.inj
    calc
      some (B.label t, B.connector t) =
          (List.ofFn (fun u : Fin W.length => (B.label u, B.connector u)))[t.val]? := by
            simp only [List.getElem?_ofFn, dif_pos t.isLt]
      _ = (W.map S.enlargeEntry)[t.val]? :=
        congrArg (fun xs : List ((I ⊕ E) × (V ⊕ P)) => xs[t.val]?) hMapped
      _ = some (S.enlargeEntry (W.get t)) := by
        rw [List.getElem?_map, List.getElem?_eq_getElem t.isLt]
        rfl
  have hLabel (t : Fin W.length) :
      B.label t = S.enlargeLabel (W.get t).1 :=
    congrArg Prod.fst (hEntryMap t)
  have hConnectorAt (t : Fin W.length) :
      B.connector t = (W.get t).2 :=
    congrArg Prod.snd (hEntryMap t)

  obtain ⟨oldPos, hConnector, _hVertexPositions⟩ :=
    (S.enlargeCycle C).oldPos_exists_of_literal_resultWord D B pieces hWord
  have hConnectorC (s : Fin n) : B.connector (oldPos s) = C.connector s := by
    change B.connector (oldPos s) = (S.enlargeCycle C).connector s
    exact hConnector s
  have hFresh := (S.enlargeCycle C).longWagons_fresh_of_literalBigCycle
    D B pieces hWord
  have hKept (t : Fin W.length) (target : J)
      (ht : (W.get t).1 = Sum.inl target) :
      ∃ s : Fin n, pieces s = .keep ∧ C.label s = Sum.inl target ∧ t = oldPos s := by
    have hMem : (Sum.inl target, (W.get t).2) ∈ W := by
      have hPair : (Sum.inl target, (W.get t).2) = W.get t :=
        Prod.ext ht.symm rfl
      rw [hPair]
      exact List.get_mem W t
    obtain ⟨s, hKeep, hSource, hSourceConnector⟩ :=
      S.kept_target_of_word_member C pieces target (W.get t).2 hMem
    refine ⟨s, hKeep, hSource, ?_⟩
    apply B.connector_injective
    calc
      B.connector t = (W.get t).2 := hConnectorAt t
      _ = C.connector s := hSourceConnector.symm
      _ = B.connector (oldPos s) := (hConnectorC s).symm

  have hLeft (t : Fin W.length) :
      S.target.Incident (W.get t).1 (B.connector t) := by
    cases hTarget : (W.get t).1 with
    | inl target =>
        obtain ⟨s, _hKeep, hSource, hPosition⟩ := hKept t target hTarget
        rw [hPosition, hConnectorC s]
        change S.target.Incident (Sum.inl target) (C.connector s)
        have h := C.left_incident s
        rw [hSource] at h
        exact h
    | inr e =>
        have hOldLabel : B.label t = Sum.inr e := by
          rw [hLabel t, hTarget]
          rfl
        have h := B.left_incident t
        rw [hOldLabel] at h
        exact (S.target_incident_edge_iff e (B.connector t)).2 h

  have hBefore (t : Fin W.length) :
      S.target.Incident (W.get t).1 (B.connector (trainCyclicPred t)) := by
    cases hTarget : (W.get t).1 with
    | inl target =>
        obtain ⟨s, hKeep, hSource, hPosition⟩ := hKept t target hTarget
        have hNone : (S.enlargeCycle C).insertedConnector D pieces s = none := by
          simp only [BigCycle.insertedConnector, hKeep]
        have hPred := (S.enlargeCycle C).literal_oldPos_pred_of_noInsertion
          D B pieces hFresh hWord oldPos hConnector s hNone
        rw [hPosition, hPred, hConnectorC (trainCyclicPred s)]
        change S.target.Incident (Sum.inl target) (C.connector (trainCyclicPred s))
        have h := C.right_incident (trainCyclicPred s)
        rw [cyclicSucc_trainCyclicPred_of_two_le C.length_ge_two s, hSource] at h
        exact h
    | inr e =>
        have hOldLabel : B.label t = Sum.inr e := by
          rw [hLabel t, hTarget]
          rfl
        have h := B.right_incident (trainCyclicPred t)
        rw [cyclicSucc_trainCyclicPred_of_two_le B.length_ge_two t, hOldLabel] at h
        exact (S.target_incident_edge_iff e (B.connector (trainCyclicPred t))).2 h

  let refined : S.target.BigCycle W.length := {
    length_ge_two := B.length_ge_two
    label := fun t => (W.get t).1
    connector := B.connector
    adjacent_ne := by
      intro t hSame
      apply B.adjacent_ne t
      calc
        B.label t = S.enlargeLabel (W.get t).1 := hLabel t
        _ = S.enlargeLabel (W.get (cyclicSucc t)).1 := congrArg S.enlargeLabel hSame
        _ = B.label (cyclicSucc t) := (hLabel (cyclicSucc t)).symm
    connector_injective := B.connector_injective
    left_incident := hLeft
    right_incident := by
      intro t
      have h := hBefore (cyclicSucc t)
      rw [trainCyclicPred_cyclicSucc_of_two_le B.length_ge_two t] at h
      exact h }
  refine ⟨W.length, refined, ?_⟩
  change List.ofFn (fun t : Fin W.length => ((W.get t).1, B.connector t)) = W
  calc
    List.ofFn (fun t : Fin W.length => ((W.get t).1, B.connector t)) =
        List.ofFn (fun t : Fin W.length => W.get t) :=
      congrArg List.ofFn (funext (fun t => Prod.ext rfl (hConnectorAt t)))
    _ = W := List.ofFn_get W

end StructuralRamsey.Girth.OrderOneData.DesignatedSubcopyFamily
