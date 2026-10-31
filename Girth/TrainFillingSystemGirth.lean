import Girth.TrainFillingProjectionAllLengths
import Girth.TrainFillingNormalizedFreshness
import Girth.TrainFillingContractedBlockLift

/-!
# Full system-girth preservation under filling

Build the canonical old projected cycle, obtain its supreme designated
label, and lift its local pieces at EVERY original occurrence. Each
contracted block gives two short source pieces around its existing wagon.
Each singleton block uses the ordinary local filling lift.

Mixed normalization makes all new long wagons fresh automatically; the
checked fresh-local assembler supplies the literal globally legal output.
Finally pull back through normalization. No target cycle, local piece,
freshness, global replacement word, or output girth is an input.
-/
namespace StructuralRamsey.Girth.TrainFilling
universe v
variable {V I P : Type v}
variable (F : TrainFilling V) (copyCarrier : I → Set V)
variable (copyEdges : I → Set F.OldEdge) (parent : F.OldEdge → P)
local notation "O" => F.oldData copyCarrier copyEdges parent
local notation "H" => F.filledData copyCarrier copyEdges parent

/-- The full filling lift for a normalized source of length at least
three, with no exception when the projection has only two survivors. -/
theorem filled_normalized_supreme_of_fullSystemGirth
    {q n : ℕ} (hOld : (O).FullSystemGirthGT q)
    (hEdges : ∀ e f : F.NewEdge, e ≠ f → (e.1 ∩ f.1).Subsingleton)
    (C : (H).BigCycle n) (hAccept : C.Acceptable) (hn : 3 ≤ n)
    (hNormal : C.MixedNormalized H) (hOrder : C.twiceOrder ≤ 2 * q) :
    C.HasSimultaneousSupreme := by
  classical
  let B := F.projectedCycle copyCarrier copyEdges parent C hOld.1 hAccept hNormal hEdges
  let pos := F.retainedIndex copyCarrier copyEdges parent C
  obtain ⟨hBAccept, hBOrder⟩ := F.projectedCycle_acceptable_and_order
    copyCarrier copyEdges parent C hOld.1 hAccept hNormal hEdges
  have hSupreme := hOld.2 _ B hBAccept (hBOrder.trans hOrder)
  obtain ⟨k, hk, hLocal⟩ := B.localSupreme_of_simultaneous O hSupreme
  obtain ⟨target, hTarget⟩ : ∃ target : I, B.label k = Sum.inl target := by
    cases hl : B.label k with
    | inl target => exact ⟨target, rfl⟩
    | inr f => exact False.elim (by simpa [OrderOneData.designated, hl] using hk)
  have hSourceTarget : C.label (pos k) = Sum.inl target :=
    (F.projectedLabel_eq_designated_iff copyCarrier copyEdges parent C hOld.1 hNormal k target).mp hTarget
  have hkSource : (H).designated (C.label (pos k)) := by
    simp [OrderOneData.designated, hSourceTarget]
  have hLocalTarget (t : Fin (F.retainedPositions copyCarrier copyEdges parent C).card)
      (hNe : B.label t ≠ Sum.inl target) :
      (O).ShortPiece (.inl target) (B.connector (trainCyclicPred t)) (B.connector t) ∨
      (O).LongPiece (.inl target) (B.connector (trainCyclicPred t)) (B.connector t) := by
    simpa only [hTarget] using hLocal t (by rw [hTarget]; exact hNe)
  have hContracted (i : Fin n)
      (hi : F.ContractibleBlock copyCarrier copyEdges parent C i) :
      (∃ e : F.NewEdge, C.ShortValid H (pos k) i e) ∧
      (∃ e : F.NewEdge, C.ShortValid H (pos k) (cyclicSucc i) e) := by
    obtain ⟨t, ht⟩ := F.retainedIndex_surjective copyCarrier copyEdges parent C
      (cyclicSucc i) (F.contractible_neighbours_retained copyCarrier copyEdges parent C i hi).2
    have hPred : trainCyclicPred (pos t) = i := by
      rw [ht, trainCyclicPred_cyclicSucc_of_two_le C.length_ge_two]
    have hBefore : pos (trainCyclicPred t) = trainCyclicPred i := by
      rcases F.retainedIndex_predecessor copyCarrier copyEdges parent C t with
        ⟨hKeep, _h⟩ | ⟨_hDelete, h⟩
      · exact False.elim (hKeep (by rw [hPred]; exact hi))
      · simpa only [hPred] using h
    have hPhysical : B.label t = Sum.inr
        (F.contractingEdge copyCarrier copyEdges parent C hOld.1 i hi) := by
      change F.projectedLabel copyCarrier copyEdges parent C hOld.1 t = _
      unfold projectedLabel
      change (if h : F.ContractibleBlock copyCarrier copyEdges parent C (trainCyclicPred (pos t))
        then Sum.inr (F.contractingEdge copyCarrier copyEdges parent C hOld.1 _ h)
        else F.projectLabel (C.label (pos t))) = _
      simp only [hPred, dite_eq_left hi]
    obtain ⟨p, x, y, f, hp, hx, hy, _hxy, hxf, hyf, _hfp, _hUnique⟩ :=
      F.contractible_unique_old_edge copyCarrier copyEdges parent C hOld.1 i hi
    have hPiece := hLocalTarget t (by rw [hPhysical]; simp)
    change (O).ShortPiece (.inl target) (C.connector (pos (trainCyclicPred t)))
        (C.connector (pos t)) ∨
      (O).LongPiece (.inl target) (C.connector (pos (trainCyclicPred t)))
        (C.connector (pos t)) at hPiece
    rw [hBefore, ht, hx, hy] at hPiece
    obtain ⟨a, b, ha, hb, _hab⟩ :=
      F.contractible_has_edge_occurrences copyCarrier copyEdges parent C hNormal i hi
    obtain ⟨_hOwned, _hParent, a', b', _hCoverA, _hCoverB, _hDistinct,
      _hParentA, _hParentB, hShortA, hShortB⟩ :=
      F.contractedBlock_short_lifts copyCarrier copyEdges parent hOld.1 C hAccept hn
        target (pos k) i hSourceTarget a b ha hb x y p hx hp hy f hxf hyf hPiece
    exact ⟨⟨a', hShortA⟩, ⟨b', hShortB⟩⟩
  have hAt : C.HasSupremeAt H (pos k) := by
    apply C.hasSupremeAt_of_mixedNormalized_local H hAccept
      (F.filled_linearPretrain copyCarrier copyEdges parent hOld.1 hEdges) hNormal
      (pos k) hkSource
    intro j hNe
    by_cases hj : F.ContractibleBlock copyCarrier copyEdges parent C j
    · obtain ⟨e, he⟩ := (hContracted j hj).1
      exact Or.inl (C.shortPiece_of_valid H (pos k) j e he)
    · by_cases hp : F.ContractibleBlock copyCarrier copyEdges parent C (trainCyclicPred j)
      · obtain ⟨e, he⟩ := (hContracted (trainCyclicPred j) hp).2
        rw [cyclicSucc_trainCyclicPred_of_two_le C.length_ge_two] at he
        exact Or.inl (C.shortPiece_of_valid H (pos k) j e he)
      · obtain ⟨t, ht⟩ := F.retainedIndex_surjective copyCarrier copyEdges parent C j hj
        have hBefore : pos (trainCyclicPred t) = trainCyclicPred j := by
          rcases F.retainedIndex_predecessor copyCarrier copyEdges parent C t with
            ⟨_hKeep, h⟩ | ⟨hDelete, _h⟩
          · simpa only [ht] using h
          · exact False.elim (hp (by simpa only [ht] using hDelete))
        have hProjectedNe : B.label t ≠ Sum.inl target := by
          intro h
          have hSource := (F.projectedLabel_eq_designated_iff copyCarrier copyEdges parent
            C hOld.1 hNormal t target).mp h
          rw [ht] at hSource
          exact hNe (hSource.trans hSourceTarget.symm)
        have hPiece := hLocalTarget t hProjectedNe
        change (O).ShortPiece (.inl target) (C.connector (pos (trainCyclicPred t)))
            (C.connector (pos t)) ∨
          (O).LongPiece (.inl target) (C.connector (pos (trainCyclicPred t)))
            (C.connector (pos t)) at hPiece
        rw [hBefore, ht] at hPiece
        have hBoundaryNe : C.connector (trainCyclicPred j) ≠ C.connector j := by
          intro h
          have hpj := C.connector_injective h
          have hs := cyclicSucc_trainCyclicPred_of_two_le C.length_ge_two j
          rw [hpj] at hs
          exact (C.ne_cyclicSucc H j) hs.symm
        have hLift :
            (H).ShortPiece (.inl target) (C.connector (trainCyclicPred j)) (C.connector j) ∨
            (H).LongPiece (.inl target) (C.connector (trainCyclicPred j)) (C.connector j) := by
          rcases hPiece with hs | hl
          · exact F.shortPiece_lift copyCarrier copyEdges parent hOld.1.1 target _ _ hBoundaryNe hs
          · exact Or.inr (F.longPiece_lift copyCarrier copyEdges parent target _ _ hl)
        simpa only [hSourceTarget] using hLift
  exact C.hasSimultaneousSupreme_of_hasSupremeAt H (pos k) hAt

/-- Filling preserves the full simultaneous system-girth bound for the
inherited wagon partition. The input is only the actual filling, old
system girth and new physical-edge linearity. -/
theorem filled_fullSystemGirthGT
    {q : ℕ} (hOld : (O).FullSystemGirthGT q)
    (hEdges : ∀ e f : F.NewEdge, e ≠ f → (e.1 ∩ f.1).Subsingleton) :
    (H).FullSystemGirthGT q := by
  have hLinear := F.filled_linearPretrain copyCarrier copyEdges parent hOld.1 hEdges
  refine ⟨hLinear, ?_⟩
  intro n C hAccept hOrder
  by_cases hn : n = 2
  · subst n
    exact F.filled_two_supreme_of_fullSystemGirth copyCarrier copyEdges parent
      hOld hEdges C hAccept hOrder
  · have hnThree : 3 ≤ n := by have := C.length_ge_two; omega
    by_contra hNoSupreme
    obtain ⟨N, hNAccept, hNOrder, hNormal, hNoN⟩ :=
      C.exists_mixed_normalized_counterexample H hAccept hLinear hnThree hNoSupreme
    exact hNoN (F.filled_normalized_supreme_of_fullSystemGirth copyCarrier copyEdges parent
      hOld hEdges N hNAccept hnThree hNormal (by rw [hNOrder]; exact hOrder))
end StructuralRamsey.Girth.TrainFilling
