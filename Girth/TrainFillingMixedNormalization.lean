import Girth.TrainArbitraryReplacementComplete
import Girth.TrainShortOnlyLiteralAcceptability

/-!
# Circulation Section 13: simultaneous normalization before filling projection

A designated occurrence with one vertex boundary x and one wagon boundary
W can be replaced by an ambient W-edge whenever x belongs to W. Do this
at every such occurrence simultaneously, using only short pieces and
keeping every other label. The existing arbitrary-replacement theorem
constructs the globally legal output and proves acceptability, exact order
and pullback of every later supreme label.

The short-only connector identity shows that all positions and connectors
are unchanged. Hence every surviving designated occurrence is normalized.
No minimization over the number of designated occurrences, new cyclic
infrastructure or ambient-edge deletion is required. Length two is kept
separate; this theorem assumes source length at least three.

This is the normalization preceding contraction in the filling proof. It
does not yet construct the old-edge contraction or transfer system girth.
-/

namespace StructuralRamsey.Girth.OrderOneData

universe v
variable {V E I P : Type v} (D : OrderOneData V E I P)

/-- Mixed boundaries whose vertex lies in the wagon. Both cyclic
orientations are included, independently of the occurrence label. -/
def BigCycle.MixedWagonContact {n : ℕ} (C : D.BigCycle n) (j : Fin n) : Prop :=
  ∃ (x : V) (p : P), D.WagonVertex p x ∧
    ((C.connector (trainCyclicPred j) = Sum.inl x ∧ C.connector j = Sum.inr p) ∨
     (C.connector (trainCyclicPred j) = Sum.inr p ∧ C.connector j = Sum.inl x))

/-- Every mixed contact of this kind already has an actual edge label. -/
def BigCycle.MixedNormalized {n : ℕ} (C : D.BigCycle n) : Prop :=
  ∀ j : Fin n, D.designated (C.label j) → ¬ C.MixedWagonContact D j

/-- A mixed contact supplies a genuine ambient short edge through its
two boundary connectors. No designated-copy source ownership is needed
for this arbitrary normalization replacement. -/
theorem BigCycle.mixedWagonContact_edge
    {n : ℕ} (C : D.BigCycle n) (j : Fin n)
    (h : C.MixedWagonContact D j) :
    ∃ e : E, D.Incident (.inr e) (C.connector (trainCyclicPred j)) ∧
      D.Incident (.inr e) (C.connector j) := by
  obtain ⟨x, p, ⟨e, hep, hxe⟩, hBoundaries⟩ := h
  refine ⟨e, ?_⟩
  rcases hBoundaries with ⟨hBefore, hHere⟩ | ⟨hBefore, hHere⟩
  · constructor
    · rw [hBefore]
      exact hxe
    · rw [hHere]
      exact ⟨e, rfl, hep⟩
  · constructor
    · rw [hBefore]
      exact ⟨e, rfl, hep⟩
    · rw [hHere]
      exact hxe

/-- Mixed normalization depends only on the physical connector word
once the designated occurrence to be tested is specified. -/
theorem BigCycle.mixedWagonContact_iff_of_sameConnectors
    {n : ℕ} (C B : D.BigCycle n)
    (hConnector : ∀ i : Fin n, B.connector i = C.connector i)
    (j : Fin n) : B.MixedWagonContact D j ↔ C.MixedWagonContact D j := by
  simp only [BigCycle.MixedWagonContact, hConnector]

/-- Normalize all offending designated mixed occurrences in one actual
simultaneous short replacement. The output is a legal BigCycle with the
same positions, physical connectors and order. Every later indexed supreme
label pulls back to an original occurrence of that same designated label. -/
theorem BigCycle.exists_mixed_normalized
    {n : ℕ} (C : D.BigCycle n) (hAccept : C.Acceptable)
    (hLinear : D.LinearPretrain) (hn : 3 ≤ n) :
    ∃ B : D.BigCycle n,
      (∀ i : Fin n, B.connector i = C.connector i) ∧
      B.Acceptable ∧ B.twiceOrder = C.twiceOrder ∧ B.MixedNormalized D ∧
      (∀ kB : Fin n, B.HasSupremeAt D kB →
        ∃ kC : Fin n, C.label kC = B.label kB ∧ C.HasSupremeAt D kC) := by
  classical
  let bad : Fin n → Prop := fun i =>
    D.designated (C.label i) ∧ C.MixedWagonContact D i
  have hEdge : ∀ i : Fin n, bad i →
      ∃ e : E, D.Incident (.inr e) (C.connector (trainCyclicPred i)) ∧
        D.Incident (.inr e) (C.connector i) := by
    intro i hi
    exact C.mixedWagonContact_edge D i hi.2
  let pick : (i : Fin n) → bad i → E :=
    fun i hi => Classical.choose (hEdge i hi)
  have hPick (i : Fin n) (hi : bad i) :
      D.Incident (.inr (pick i hi)) (C.connector (trainCyclicPred i)) ∧
      D.Incident (.inr (pick i hi)) (C.connector i) :=
    Classical.choose_spec (hEdge i hi)
  let pieces : Fin n → TrainSupremePiece E P := fun i =>
    if hi : bad i then .short (pick i hi) else .keep
  let outLabel : Fin n → I ⊕ E := fun i =>
    if hi : bad i then .inr (pick i hi) else C.label i
  have hShort : ∀ i : Fin n, (pieces i).IsShortOrKeep := by
    intro i
    by_cases hi : bad i <;> simp [pieces, hi, TrainSupremePiece.IsShortOrKeep]
  have hInc : C.LocalPieceIncidence D pieces := by
    intro i
    by_cases hi : bad i
    · simpa only [pieces, dif_pos hi] using hPick i hi
    · simp only [pieces, dif_neg hi]
  have hNoLong (i : Fin n) (e : E) (p : P) (f : E) :
      pieces i ≠ .long e p f := by
    intro hi
    have h := hShort i
    rw [hi] at h
    exact h
  have hGeom : C.LocalLongA2Geometry D pieces := by
    intro i e f p hi
    exact False.elim (hNoLong i e p f hi)
  have hFresh : ∀ (i : Fin n) (e : E) (p : P) (f : E),
      pieces i = .long e p f → ∀ t : Fin n, C.connector t ≠ Sum.inr p := by
    intro i e p f hi
    exact False.elim (hNoLong i e p f hi)
  obtain ⟨m, B, hWord, hBAccept, hOrder, hPullback⟩ :=
    C.arbitrary_replacement_complete_of_three_le D hAccept hLinear hn
      pieces hInc hGeom hFresh
  have hProjection : List.ofFn B.connector = List.ofFn C.connector := by
    calc
      List.ofFn B.connector =
          (List.ofFn (fun j : Fin m => (B.label j, B.connector j))).map Prod.snd := by
            simp [List.map_ofFn, Function.comp_def]
      _ = (C.resultWord D pieces).map Prod.snd := congrArg (List.map Prod.snd) hWord
      _ = List.ofFn C.connector := C.shortOnly_resultWord_connectorList D pieces hShort
  have hLen : m = n := by
    have h := congrArg List.length hProjection
    simpa only [List.length_ofFn] using h
  cases hLen
  have hConnector : ∀ i : Fin n, B.connector i = C.connector i := by
    intro i
    have hAt := congrArg (fun xs : List (V ⊕ P) => xs[i.val]?) hProjection
    have hB : (List.ofFn B.connector)[i.val]? = some (B.connector i) := by
      simp [List.get_ofFn]
    have hC : (List.ofFn C.connector)[i.val]? = some (C.connector i) := by
      simp [List.get_ofFn]
    exact Option.some.inj (hB.symm.trans (hAt.trans hC))
  have hPieceWord : ∀ j : Fin n,
      C.pieceWord D j (pieces j) = [(outLabel j, C.connector j)] := by
    intro j
    by_cases hj : bad j <;> simp [pieces, outLabel, hj, BigCycle.pieceWord]
  have hResult : C.resultWord D pieces =
      List.ofFn (fun i : Fin n => (outLabel i, C.connector i)) := by
    rw [BigCycle.resultWord]
    simp_rw [hPieceWord]
    exact flatten_ofFn_singleton (fun i : Fin n => (outLabel i, C.connector i))
  have hLabel : ∀ i : Fin n, B.label i = outLabel i := by
    intro i
    have hAt := congrArg
      (fun xs : List ((I ⊕ E) × (V ⊕ P)) => xs[i.val]?) (hWord.trans hResult)
    have hB : (List.ofFn (fun j : Fin n =>
        (B.label j, B.connector j)))[i.val]? = some (B.label i, B.connector i) := by
      simp [List.get_ofFn]
    have hC : (List.ofFn (fun j : Fin n =>
        (outLabel j, C.connector j)))[i.val]? = some (outLabel i, C.connector i) := by
      simp [List.get_ofFn]
    exact congrArg Prod.fst (Option.some.inj (hB.symm.trans (hAt.trans hC)))
  refine ⟨B, hConnector, hBAccept, hOrder, ?_, hPullback⟩
  intro i hDesignated hMixed
  have hSourceMixed : C.MixedWagonContact D i :=
    (C.mixedWagonContact_iff_of_sameConnectors D B hConnector i).mp hMixed
  by_cases hi : bad i
  · have hLabelEdge : B.label i = Sum.inr (pick i hi) := by
      rw [hLabel i]
      simp only [outLabel, dif_pos hi]
    rw [hLabelEdge] at hDesignated
    exact hDesignated
  · have hLabelKept : B.label i = C.label i := by
      rw [hLabel i]
      simp only [outLabel, dif_neg hi]
    apply hi
    refine ⟨?_, hSourceMixed⟩
    rw [← hLabelKept]
    exact hDesignated

/-- A counterexample of length at least three has a normalized
counterexample of the same length and order. The implication is derived
from the actual indexed supreme pullback, with no assumed cycle transfer. -/
theorem BigCycle.exists_mixed_normalized_counterexample
    {n : ℕ} (C : D.BigCycle n) (hAccept : C.Acceptable)
    (hLinear : D.LinearPretrain) (hn : 3 ≤ n)
    (hNoSupreme : ¬ C.HasSimultaneousSupreme) :
    ∃ B : D.BigCycle n, B.Acceptable ∧ B.twiceOrder = C.twiceOrder ∧
      B.MixedNormalized D ∧ ¬ B.HasSimultaneousSupreme := by
  obtain ⟨B, _hConnectors, hBAccept, hOrder, hNormal, hPullback⟩ :=
    C.exists_mixed_normalized D hAccept hLinear hn
  refine ⟨B, hBAccept, hOrder, hNormal, ?_⟩
  rintro ⟨kB, hkB, pieces, hValid, hGlobal⟩
  obtain ⟨kC, _hLabel, hSupreme⟩ := hPullback kB ⟨hkB, pieces, hValid, hGlobal⟩
  exact hNoSupreme (C.hasSimultaneousSupreme_of_hasSupremeAt D kC hSupreme)

end StructuralRamsey.Girth.OrderOneData
