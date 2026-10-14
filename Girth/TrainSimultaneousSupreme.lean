import Girth.TrainBigCycleOrderOneExtraction
import Mathlib.Tactic

/-!
# Circulation: literal simultaneous supreme replacement

The manuscript's system-Girth condition has TWO demands:
(1) each replaced occurrence uses a legal short or long piece from
    one designated source copy, with all original occurrences of that
    source label retained;
(2) the chosen simultaneous replacements really form a big cycle.

This file records both demands. The result word is constructed, not
postulated: each old occurrence contributes one (label,connector) pair
if retained or short-replaced, and two pairs (e,W),(f,q) if long-replaced.
Flattening the pieces in cyclic order gives the output word. A witness
BigCycle must have precisely that word; hence its distinctness and
incidence conditions verify GLOBAL legality, not merely local pieces.

The full system-girth predicate also records linearity of the physical
edges and of the wagon carriers. We prove that this stronger, literal
condition yields the old local-piece bound, and therefore the exact
order-one bridge used in circulation parameter preservation.

Only the circulation proof is addressed; no appendix formalization.
-/

namespace StructuralRamsey.Girth

universe v

/-- A selected occurrence is retained, replaced by one genuine
source edge, or replaced by two genuine source edges with a wagon
connector between them. -/
inductive TrainSupremePiece (E P : Type v) where
  | keep
  | short (e : E)
  | long (e : E) (wagon : P) (f : E)
  deriving Repr

namespace OrderOneData

variable {V E I P : Type v} (D : OrderOneData V E I P)

/-- The actual output cyclic word contributed by a SINGLE source
occurrence with its original right connector. -/
def BigCycle.pieceWord {n : ℕ} (C : D.BigCycle n)
    (j : Fin n) : TrainSupremePiece E P →
      List ((I ⊕ E) × (V ⊕ P))
  | .keep => [(C.label j, C.connector j)]
  | .short e => [(Sum.inr e, C.connector j)]
  | .long e w f =>
      [(Sum.inr e, Sum.inr w), (Sum.inr f, C.connector j)]

/-- Concatenate all selected simultaneous replacements in cyclic
order. The last connector of each piece is the original connector
after that occurrence, so all old boundary connectors are retained. -/
def BigCycle.resultWord {n : ℕ} (C : D.BigCycle n)
    (pieces : Fin n → TrainSupremePiece E P) :
    List ((I ⊕ E) × (V ⊕ P)) :=
  (List.ofFn (fun j : Fin n => BigCycle.pieceWord D C j (pieces j))).flatten

/-- Local correctness of a CHOSEN short piece, including its two
boundary connectors and source-edge ownership. -/
def BigCycle.ShortValid {n : ℕ}
    (C : D.BigCycle n) (k j : Fin n) (e : E) : Prop :=
  e ∈ D.edges (C.label k) ∧
  D.Incident (.inr e) (C.connector (trainCyclicPred j)) ∧
  D.Incident (.inr e) (C.connector j)

/-- Local correctness of a CHOSEN long piece. Both boundaries
must be vertices joined by no ambient edge; the two source edges
are distinct and belong to one wagon. -/
def BigCycle.LongValid {n : ℕ}
    (C : D.BigCycle n) (k j : Fin n)
    (e : E) (w : P) (f : E) : Prop :=
  ∃ x y : V,
    C.connector (trainCyclicPred j) = Sum.inl x ∧
    C.connector j = Sum.inl y ∧
    e ∈ D.edges (C.label k) ∧
    f ∈ D.edges (C.label k) ∧
    e ≠ f ∧
    D.parent e = w ∧ D.parent f = w ∧
    x ∈ D.edgeCarrier e ∧ y ∈ D.edgeCarrier f ∧
    ¬ D.PairEdge x y

/-- Only occurrences of the named supreme label are kept.
Every other occurrence is replaced by a locally valid piece
using actual source edges of that supreme label. -/
def BigCycle.PlanValid {n : ℕ}
    (C : D.BigCycle n) (k : Fin n)
    (pieces : Fin n → TrainSupremePiece E P) : Prop :=
  ∀ j : Fin n,
    (C.label j = C.label k → pieces j = .keep) ∧
    (C.label j ≠ C.label k →
      match pieces j with
      | .keep => False
      | .short e => BigCycle.ShortValid D C k j e
      | .long e w f => BigCycle.LongValid D C k j e w f)

/-- Verify that the flattened simultaneous replacement WORD actually
comes from a big cycle: this checks every adjacent-label inequality,
distinct connector, and physical incidence globally. -/
def BigCycle.PlanProducesBigCycle {n : ℕ}
    (C : D.BigCycle n)
    (pieces : Fin n → TrainSupremePiece E P) : Prop :=
  ∃ m : ℕ, ∃ B : D.BigCycle m,
    List.ofFn (fun i : Fin m => (B.label i, B.connector i)) =
      BigCycle.resultWord D C pieces

/-- Literal supreme copy in the circulation definition. The
global validity requirement is not discarded: all simultaneous
pieces must assemble into a well-defined resulting big cycle. -/
def BigCycle.HasSimultaneousSupreme {n : ℕ}
    (C : D.BigCycle n) : Prop :=
  ∃ k : Fin n, D.designated (C.label k) ∧
    ∃ pieces : Fin n → TrainSupremePiece E P,
      BigCycle.PlanValid D C k pieces ∧
      BigCycle.PlanProducesBigCycle D C pieces

/-- An *indexed* simultaneous supreme plan keeps precisely the named
designated occurrence. This retains the information deliberately forgotten
by `HasSimultaneousSupreme`; in two-copy symmetry both indices matter. -/
def BigCycle.HasSupremeAt {n : ℕ}
    (C : D.BigCycle n) (k : Fin n) : Prop :=
  D.designated (C.label k) ∧
    ∃ pieces : Fin n → TrainSupremePiece E P,
      BigCycle.PlanValid D C k pieces ∧
      BigCycle.PlanProducesBigCycle D C pieces

/-- Forgetting the designated index recovers the usual supreme property. -/
theorem BigCycle.hasSimultaneousSupreme_of_hasSupremeAt
    {n : ℕ} (C : D.BigCycle n) (k : Fin n)
    (h : C.HasSupremeAt D k) : C.HasSimultaneousSupreme := by
  rcases h with ⟨hk, pieces, hv, hg⟩
  exact ⟨k, hk, pieces, hv, hg⟩

/-- The complete supreme-cycle condition at a given cutoff, using
the actual A1--A3 predicate and global simultaneous replacements. -/
def SupremeCycleBound (q : ℕ) : Prop :=
  ∀ (n : ℕ) (C : D.BigCycle n), C.Acceptable →
    C.twiceOrder ≤ 2 * q → C.HasSimultaneousSupreme

/-- Physical linearity of the pretrain: distinct edges intersect
in at most one vertex, and distinct wagon carriers do likewise. -/
def LinearPretrain : Prop :=
  (∀ e f : E, e ≠ f →
    (D.edgeCarrier e ∩ D.edgeCarrier f).Subsingleton) ∧
  (∀ p q : P, p ≠ q →
    ({x : V | D.WagonVertex p x} ∩
      {x : V | D.WagonVertex q x}).Subsingleton)

/-- Full circulation system-girth: linearity plus the genuine
simultaneous supreme-cycle condition. -/
def FullSystemGirthGT (q : ℕ) : Prop :=
  D.LinearPretrain ∧ D.SupremeCycleBound q

/-- A chosen legitimate short replacement is one of the
manuscript's possible local short pieces. -/
theorem BigCycle.shortPiece_of_valid {n : ℕ}
    (C : D.BigCycle n) (k j : Fin n) (e : E)
    (h : BigCycle.ShortValid D C k j e) :
    D.ShortPiece (C.label k)
      (C.connector (trainCyclicPred j)) (C.connector j) :=
  ⟨e, h.1, h.2.1, h.2.2⟩

/-- A chosen legitimate long replacement is one of the
manuscript's possible local long pieces. -/
theorem BigCycle.longPiece_of_valid {n : ℕ}
    (C : D.BigCycle n) (k j : Fin n)
    (e : E) (w : P) (f : E)
    (h : BigCycle.LongValid D C k j e w f) :
    D.LongPiece (C.label k)
      (C.connector (trainCyclicPred j)) (C.connector j) := by
  rcases h with ⟨x, y, hprev, hcurr, he, hf, hne,
    hpe, hpf, hxe, hyf, hPair⟩
  exact ⟨x, y, w, e, f, hprev, hcurr, he, hf,
    hne, hpe, hpf, hxe, hyf, hPair⟩

/-- Every genuine simultaneous supreme copy has the necessary local
short/long pieces. Importantly, the premise still requires the full
globally valid replacement word. -/
theorem BigCycle.localSupreme_of_simultaneous {n : ℕ}
    (C : D.BigCycle n)
    (h : C.HasSimultaneousSupreme) : C.HasLocalSupreme := by
  rcases h with ⟨k, hk, pieces, hValid, _hGlobal⟩
  refine ⟨k, hk, ?_⟩
  intro j hne
  have hj := (hValid j).2 hne
  cases hp : pieces j with
  | keep =>
      simp [hp] at hj
  | short e =>
      have hShort : BigCycle.ShortValid D C k j e := by
        simpa only [hp] using hj
      exact Or.inl (BigCycle.shortPiece_of_valid D C k j e hShort)
  | long e w f =>
      have hLong : BigCycle.LongValid D C k j e w f := by
        simpa only [hp] using hj
      exact Or.inr (BigCycle.longPiece_of_valid D C k j e w f hLong)

/-- The full global simultaneous-replacement condition implies the
previously verified local-piece system bound. -/
theorem localPieceSystemBound_of_supremeCycleBound
    (q : ℕ) (h : D.SupremeCycleBound q) :
    D.LocalPieceSystemBound q := by
  intro n C hAccept hOrder
  exact BigCycle.localSupreme_of_simultaneous D C
    (h n C hAccept hOrder)

/-- The full circulation system-girth hypothesis at cutoff one gives
the exact two-source order-one bridge condition. No bridge hypothesis
is smuggled into the definition. -/
theorem orderOneBound_of_fullSystemGirth
    (h : D.FullSystemGirthGT 1) : D.Bound := by
  exact D.bound_of_localPieceSystemBound
    (D.localPieceSystemBound_of_supremeCycleBound 1 h.2)

end OrderOneData
end StructuralRamsey.Girth
