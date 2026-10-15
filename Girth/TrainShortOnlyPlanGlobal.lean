import Girth.TrainShortReplacementNeighbour
import Girth.TrainSimultaneousSupreme
import Mathlib.Data.List.OfFn
import Mathlib.Tactic

/-!
# Circulation: short-only supreme plans are globally legal

For an acceptable big cycle of length at least three, suppose a chosen
simultaneous supreme plan uses only `keep` and genuine short pieces.
The local `PlanValid` conditions already imply all global legality:

* kept occurrences are precisely occurrences of the supreme designated label;
* short occurrences carry actual edge labels and their two boundary incidences;
* a kept label cannot equal an actual edge label;
* two adjacent short edges cannot coincide, by the A2/A3 three-incidence
  obstruction from `TrainShortReplacementNeighbour`.

Thus the flattened replacement word is a literal BigCycle with the unchanged
connector sequence.  This discharges `PlanProducesBigCycle` for every
short-only plan; no output-wagon linearity or extra cycle assumption is used.
-/

namespace StructuralRamsey.Girth

universe v

namespace TrainSupremePiece

variable {E P : Type v}

/-- The replacement piece contributes exactly one occurrence and adds no
wagon connector. -/
def IsShortOrKeep : TrainSupremePiece E P → Prop
  | .keep => True
  | .short _ => True
  | .long _ _ _ => False

end TrainSupremePiece

private theorem flatten_ofFn_singleton
    {α : Type v} {n : ℕ} (f : Fin n → α) :
    (List.ofFn (fun i => [f i])).flatten = List.ofFn f := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [List.ofFn_succ', List.ofFn_succ']
      simp [ih]

namespace OrderOneData

variable {V E I P : Type v} (D : OrderOneData V E I P)

/-- The one-label output of a short-only replacement plan.  The long case is
given an arbitrary fallback; every theorem using this function assumes that
case impossible. -/
def BigCycle.shortPlanLabel
    {n : ℕ} (C : D.BigCycle n)
    (pieces : Fin n → TrainSupremePiece E P) (j : Fin n) : I ⊕ E :=
  match pieces j with
  | .keep => C.label j
  | .short e => .inr e
  | .long _ _ _ => C.label j

/-- Under PlanValid, a kept occurrence has the supreme label. -/
theorem BigCycle.label_eq_supreme_of_keep
    {n : ℕ} (C : D.BigCycle n) (k j : Fin n)
    (pieces : Fin n → TrainSupremePiece E P)
    (hPlan : BigCycle.PlanValid D C k pieces)
    (hKeep : pieces j = .keep) :
    C.label j = C.label k := by
  by_contra hne
  have h := (hPlan j).2 hne
  rw [hKeep] at h
  exact h

/-- Under PlanValid, a chosen short piece has the literal ShortValid data. -/
theorem BigCycle.shortValid_of_piece_eq_short
    {n : ℕ} (C : D.BigCycle n) (k j : Fin n)
    (pieces : Fin n → TrainSupremePiece E P)
    (hPlan : BigCycle.PlanValid D C k pieces)
    (e : E) (hShort : pieces j = .short e) :
    BigCycle.ShortValid D C k j e := by
  have hne : C.label j ≠ C.label k := by
    intro heq
    have h := (hPlan j).1 heq
    rw [hShort] at h
    cases h
  have h := (hPlan j).2 hne
  simpa [hShort] using h

/-- A designated source label is disjoint from every actual edge label. -/
theorem designated_ne_actualEdge
    (a : I ⊕ E) (e : E) (ha : D.designated a) :
    a ≠ Sum.inr e := by
  cases a with
  | inl i =>
      simp
  | inr f =>
      simp [designated] at ha

/-- Every short-only valid plan on an acceptable cycle of length at least three
actually produces a globally legal BigCycle. -/
theorem BigCycle.planProducesBigCycle_of_shortOnly
    {n : ℕ} (C : D.BigCycle n)
    (hAccept : C.Acceptable) (hn : 3 ≤ n)
    (k : Fin n) (hk : D.designated (C.label k))
    (pieces : Fin n → TrainSupremePiece E P)
    (hPlan : BigCycle.PlanValid D C k pieces)
    (hShortOnly : ∀ j, (pieces j).IsShortOrKeep) :
    BigCycle.PlanProducesBigCycle D C pieces := by
  classical
  let outLabel : Fin n → I ⊕ E :=
    fun j => C.shortPlanLabel D pieces j

  have hAdj : ∀ i : Fin n, outLabel i ≠ outLabel (cyclicSucc i) := by
    intro i
    have hSuccSelf : i ≠ cyclicSucc i := by
      intro h
      exact C.adjacent_ne i (congrArg C.label h)
    have hPredSelf : trainCyclicPred i ≠ i := by
      intro h
      have hs := cyclicSucc_trainCyclicPred_of_two_le C.length_ge_two i
      rw [h] at hs
      exact hSuccSelf hs.symm
    have hPredSucc : trainCyclicPred i ≠ cyclicSucc i :=
      trainCyclicPred_ne_cyclicSucc_of_three_le hn i
    cases hp : pieces i with
    | keep =>
        have hi : C.label i = C.label k :=
          C.label_eq_supreme_of_keep D k i pieces hPlan hp
        cases hq : pieces (cyclicSucc i) with
        | keep =>
            simpa [outLabel, BigCycle.shortPlanLabel, hp, hq] using
              C.adjacent_ne i
        | short e =>
            have hs : C.label k ≠ (Sum.inr e : I ⊕ E) :=
              D.designated_ne_actualEdge (C.label k) e hk
            simpa [outLabel, BigCycle.shortPlanLabel, hp, hq, hi] using hs
        | long e w f =>
            have hf : False := by
              simpa [TrainSupremePiece.IsShortOrKeep, hq] using
                hShortOnly (cyclicSucc i)
            exact False.elim hf
    | short e =>
        have hValidI :=
          C.shortValid_of_piece_eq_short D k i pieces hPlan e hp
        cases hq : pieces (cyclicSucc i) with
        | keep =>
            have hqeq : C.label (cyclicSucc i) = C.label k :=
              C.label_eq_supreme_of_keep D k (cyclicSucc i) pieces hPlan hq
            have hs : (Sum.inr e : I ⊕ E) ≠ C.label k :=
              (D.designated_ne_actualEdge (C.label k) e hk).symm
            simpa [outLabel, BigCycle.shortPlanLabel, hp, hq, hqeq] using hs
        | short f =>
            have hValidQ :=
              C.shortValid_of_piece_eq_short D k (cyclicSucc i)
                pieces hPlan f hq
            have hneEF : (Sum.inr e : I ⊕ E) ≠ Sum.inr f := by
              intro hef
              have heq : e = f := Sum.inr.inj hef
              subst f
              exact C.not_edge_incident_three_distinct D hAccept e
                (trainCyclicPred i) i (cyclicSucc i)
                hPredSelf hPredSucc hSuccSelf
                hValidI.2.1 hValidI.2.2 hValidQ.2.2
            simpa [outLabel, BigCycle.shortPlanLabel, hp, hq] using hneEF
        | long e w f =>
            have hf : False := by
              simpa [TrainSupremePiece.IsShortOrKeep, hq] using
                hShortOnly (cyclicSucc i)
            exact False.elim hf
    | long e w f =>
        have hf : False := by
          simpa [TrainSupremePiece.IsShortOrKeep, hp] using hShortOnly i
        exact False.elim hf

  have hLeft : ∀ i : Fin n, D.Incident (outLabel i) (C.connector i) := by
    intro i
    cases hp : pieces i with
    | keep =>
        simpa [outLabel, BigCycle.shortPlanLabel, hp] using C.left_incident i
    | short e =>
        have hValid :=
          C.shortValid_of_piece_eq_short D k i pieces hPlan e hp
        simpa [outLabel, BigCycle.shortPlanLabel, hp] using hValid.2.2
    | long e w f =>
        have hf : False := by
          simpa [TrainSupremePiece.IsShortOrKeep, hp] using hShortOnly i
        exact False.elim hf

  have hRight : ∀ i : Fin n,
      D.Incident (outLabel (cyclicSucc i)) (C.connector i) := by
    intro i
    cases hp : pieces (cyclicSucc i) with
    | keep =>
        simpa [outLabel, BigCycle.shortPlanLabel, hp] using C.right_incident i
    | short e =>
        have hValid :=
          C.shortValid_of_piece_eq_short D k (cyclicSucc i)
            pieces hPlan e hp
        have h := hValid.2.1
        rw [trainCyclicPred_cyclicSucc_of_two_le C.length_ge_two i] at h
        simpa [outLabel, BigCycle.shortPlanLabel, hp] using h
    | long e w f =>
        have hf : False := by
          simpa [TrainSupremePiece.IsShortOrKeep, hp] using
            hShortOnly (cyclicSucc i)
        exact False.elim hf

  let B : D.BigCycle n :=
    C.relabelSameConnectors D outLabel hAdj hLeft hRight

  have hPieceWord : ∀ j : Fin n,
      BigCycle.pieceWord D C j (pieces j) =
        [(outLabel j, C.connector j)] := by
    intro j
    cases hp : pieces j with
    | keep =>
        simp [BigCycle.pieceWord, outLabel, BigCycle.shortPlanLabel, hp]
    | short e =>
        simp [BigCycle.pieceWord, outLabel, BigCycle.shortPlanLabel, hp]
    | long e w f =>
        have hf : False := by
          simpa [TrainSupremePiece.IsShortOrKeep, hp] using hShortOnly j
        exact False.elim hf

  refine ⟨n, B, ?_⟩
  change List.ofFn (fun i : Fin n => (outLabel i, C.connector i)) =
    BigCycle.resultWord D C pieces
  rw [BigCycle.resultWord]
  simp_rw [hPieceWord]
  exact (flatten_ofFn_singleton
    (fun i : Fin n => (outLabel i, C.connector i))).symm

/-- Therefore a short-only PlanValid witness already gives the literal indexed
supreme property; no separate global-word premise remains. -/
theorem BigCycle.hasSupremeAt_of_shortOnlyPlan
    {n : ℕ} (C : D.BigCycle n)
    (hAccept : C.Acceptable) (hn : 3 ≤ n)
    (k : Fin n) (hk : D.designated (C.label k))
    (pieces : Fin n → TrainSupremePiece E P)
    (hPlan : BigCycle.PlanValid D C k pieces)
    (hShortOnly : ∀ j, (pieces j).IsShortOrKeep) :
    C.HasSupremeAt D k := by
  exact ⟨hk, pieces, hPlan,
    C.planProducesBigCycle_of_shortOnly D hAccept hn k hk
      pieces hPlan hShortOnly⟩


/-- It is enough to prove occurrence-wise existence of short witnesses.
The plan itself, all keep choices, and the global replacement word are then
constructed automatically.  This is the convenient interface for cycle
transfer after long local pieces have been resolved into short pieces along
existing wagon connectors. -/
theorem BigCycle.hasSupremeAt_of_all_shortValid
    {n : ℕ} (C : D.BigCycle n)
    (hAccept : C.Acceptable) (hn : 3 ≤ n)
    (k : Fin n) (hk : D.designated (C.label k))
    (hShort : ∀ j : Fin n, C.label j ≠ C.label k →
      ∃ e : E, BigCycle.ShortValid D C k j e) :
    C.HasSupremeAt D k := by
  classical
  let pieces : Fin n → TrainSupremePiece E P :=
    fun j =>
      if h : C.label j = C.label k then
        .keep
      else
        .short (Classical.choose (hShort j h))
  have hPlan : BigCycle.PlanValid D C k pieces := by
    intro j
    constructor
    · intro heq
      simp [pieces, heq]
    · intro hne
      have hs := Classical.choose_spec (hShort j hne)
      simpa [pieces, hne] using hs
  have hShortOnly : ∀ j, (pieces j).IsShortOrKeep := by
    intro j
    by_cases h : C.label j = C.label k
    · simp [pieces, h, TrainSupremePiece.IsShortOrKeep]
    · simp [pieces, h, TrainSupremePiece.IsShortOrKeep]
  exact C.hasSupremeAt_of_shortOnlyPlan D hAccept hn
    k hk pieces hPlan hShortOnly


/-- Unindexed form matching the literal conclusion used by SupremeCycleBound. -/
theorem BigCycle.hasSimultaneousSupreme_of_all_shortValid
    {n : ℕ} (C : D.BigCycle n)
    (hAccept : C.Acceptable) (hn : 3 ≤ n)
    (k : Fin n) (hk : D.designated (C.label k))
    (hShort : ∀ j : Fin n, C.label j ≠ C.label k →
      ∃ e : E, BigCycle.ShortValid D C k j e) :
    C.HasSimultaneousSupreme :=
  BigCycle.hasSimultaneousSupreme_of_hasSupremeAt D C k
    (C.hasSupremeAt_of_all_shortValid D hAccept hn k hk hShort)

end OrderOneData
end StructuralRamsey.Girth
