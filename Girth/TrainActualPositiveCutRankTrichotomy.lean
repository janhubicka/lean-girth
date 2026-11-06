import Girth.TrainActualPositiveCutFullWitnessTrichotomy
import Girth.TrainActualSelectedOutputLexRank

set_option autoImplicit false
set_option Elab.async false

/-!
# Positive-cut witness trichotomy as a genuine cycle-rank descent

The already checked physical positive-cut witness theorem yields:
  * an actual finite sequence of legal one-edge short absorptions,
    with an acceptable same-order output of strictly fewer MINIMAL
    geometric owner changes; or
  * a globally supreme reduced gluing standard with designated
    reduced neighbors on both sides; or
  * an order-one cut word with two physical witness bridges.

The first case is not merely a descent in an arbitrary chosen
owner assignment: the original and new owners are both MINIMAL.
The canonical actual geometric lex rank includes the designated
occurrence count as its second coordinate. Strict decrease of the
first coordinate therefore gives an honest strict decrease of
the intrinsic lex rank, independent of the second coordinate.

The checked finite physical short-replacement composition theorem
pulls back any complete simultaneous supreme plan of the new
cycle to the old source cycle. The first case thus supplies the
EXACT descending successor needed by the well-founded global
SupremeCycleBound induction merged via #863.

The two remaining alternatives are retained unchanged. This file
does NOT assert that the all-designated neighbors yield a legal
replacement or that the order-one bridge case is closed. Those
are the genuine residual geometric obligations. Circulation only;
all physical A-edges and every distinct wagon label are retained.
No appendix.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v
section PositiveCutRankTrichotomy

variable {L : RelLanguage.{u}} {UA VB P X Y I : Type v}
variable (A : RelStructure L UA) (hA : A.Irreducible)
variable (B : RelStructure L VB) (D : RelStructure L P)
variable (C : StructuralRamsey.Partite.System L P X)
variable (family : Set (Embedding B D))
variable (selected : Set (DesignatedCopy B D C family))
variable (e : Embedding A D) (R : RelStructure L Y)
variable (f : I → Embedding
  (C.toRelStructure.induce (activeCarrier A C e.toFunctionEmbedding)) R)
variable {m : ℕ}
variable (T : EdgeTrainLevels (OldACarrierEdge A C.toRelStructure) m)
variable (U : EdgeTrainLevels (OldACarrierEdge A R) m)
variable (hShared : ∀ _i : I,
  Nonempty (SharedOldACarrierEdge A C.toRelStructure
    (activeCarrier A C e.toFunctionEmbedding)))
variable (hRel : ∀ (ν : Fin (m + 1)) (j : I)
  (p q : SharedOldACarrierEdge A C.toRelStructure
    (activeCarrier A C e.toFunctionEmbedding)),
  T.rel ν p.1 q.1 ↔
    U.rel ν (sharedOldACarrierCoreEmbedding A C.toRelStructure
      (activeCarrier A C e.toFunctionEmbedding) R f j p)
      (sharedOldACarrierCoreEmbedding A C.toRelStructure
        (activeCarrier A C e.toFunctionEmbedding) R f j q))
variable (μ : Fin (m + 1))

local notation "S" => activeCarrier A C e.toFunctionEmbedding
local notation "CoreEdge" => OldACarrierEdge A R
local notation "Out" => attachedSelectedPictureOrderOneData
  A hA B D C family selected e R f T U hShared μ
local notation "Wit" => sharedWitnessOrderOneData U μ
  (sharedOldACarrierCoreEmbedding A C.toRelStructure S R f)
  (Subtype.val : CoreEdge → Set Y)
local notation "GeomAllowed" => selectedOutputGeometricOwnerAllowed
  A hA B D C family selected e R f T U hShared μ
local notation "CycleRank" => attachedSelectedPicture_geometricLexRank
  A hA B D C family selected e R f T U hShared μ

include hRel

/-- The genuine positive-cut trichotomy with its short-absorption case
already normalized to a STRICT descent in the canonical intrinsic
cycle rank, together with full global supreme-plan pullback.

The other two branches are precise unresolved geometric situations,
not assumed-away extra hypotheses or local-piece substitutes. -/
theorem attachedSelectedPicture_positive_cut_rank_descent_or_designated_or_bridges
    {n q : ℕ} (K : (Out).BigCycle n)
    (hAccept : K.Acceptable) (hn : 3 ≤ n)
    (hLinear : (Out).LinearPretrain)
    (owner : Fin n → I ⊕ CoreEdge)
    (hAllowed : ∀ j, GeomAllowed (K.label j) (owner j))
    (hMinimal : ∀ other : Fin n → I ⊕ CoreEdge,
      (∀ j, GeomAllowed (K.label j) (other j)) →
      cyclicOwnerChanges owner ≤ cyclicOwnerChanges other)
    (hCuts : 2 ≤ cyclicOwnerChanges owner)
    (hq : 1 ≤ q) (hWitness : (Wit).FullSystemGirthGT q)
    (hOrder : K.twiceOrder ≤ 2 * q) :
    let Z := attachedSelectedPicture_geometric_cutBigCycle
      A hA B D C family selected e R f T U hShared hRel μ
      K owner hAllowed hCuts
    (∃ H : (Out).BigCycle n,
      H.Acceptable ∧ H.twiceOrder = K.twiceOrder ∧
      Prod.Lex (· < ·) (· < ·) (CycleRank H) (CycleRank K) ∧
      (H.HasSimultaneousSupreme → K.HasSimultaneousSupreme)) ∨
    (∃ target : Fin (cyclicOwnerChanges owner),
      ∃ i before after : I,
      Z.HasSupremeAt Wit target ∧
      Z.label target = Sum.inl i ∧
      Z.label (trainCyclicPred target) = Sum.inl before ∧
      Z.label (cyclicSucc target) = Sum.inl after) ∨
    (∃ (x : Y) (p : Quotient (U.wagonSetoid μ)),
      (∃ a b : Fin (cyclicOwnerChanges owner), a ≠ b ∧
        Z.connector a = Sum.inl x ∧ Z.connector b = Sum.inr p) ∧
      ∀ k, (Wit).Bridge (Z.label k) x p) := by
  rcases attachedSelectedPicture_positive_cut_descent_or_designated_or_bridges
      A hA B D C family selected e R f T U hShared hRel μ
      K hAccept hn owner hAllowed hCuts hq hWitness hOrder
      with hShort | hOther
  · obtain ⟨H, hReach, hHAccept, hHEqOrder,
        newOwner, hNewAllowed, hNewMinimal, hCutsDrop⟩ := hShort
    have hLex :
        Prod.Lex (· < ·) (· < ·)
          (cyclicOwnerChanges newOwner, H.designatedOccurrenceCount Out)
          (cyclicOwnerChanges owner, K.designatedOccurrenceCount Out) :=
      Prod.Lex.left _ _ hCutsDrop
    have hRank : Prod.Lex (· < ·) (· < ·)
        (CycleRank H) (CycleRank K) :=
      attachedSelectedPicture_geometricLexRank_drop
        A hA B D C family selected e R f T U hShared μ
        K H owner hAllowed hMinimal
        newOwner hNewAllowed hNewMinimal hLex
    refine Or.inl ⟨H, hHAccept, hHEqOrder, hRank, ?_⟩
    intro hHSupreme
    exact hReach.supreme_pullback_of_three_le
      Out hLinear hn hAccept hHSupreme
  · exact Or.inr hOther

end PositiveCutRankTrichotomy

end StructuralRamsey.Girth
