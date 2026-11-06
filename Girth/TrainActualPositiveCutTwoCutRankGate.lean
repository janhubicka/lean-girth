import Girth.TrainActualThreeCutFromFullSystem
import Girth.TrainActualPositiveCutRankTrichotomy
import Mathlib.Tactic

set_option autoImplicit false
set_option Elab.async false

/-!
# Path A: reduce the positive-cut lexicographic induction to exactly two cuts

This is a circulation-only composition of two separately checked interfaces.

* With at least three genuine geometric owner cuts, the one-pass
  source-expanded replacement gives simultaneous supremeness directly,
  using the OLD bound and the genuine witness FullSystemGirthGT.
* With exactly two cuts, the actual positive-cut rank trichotomy gives
  either a physically legal short absorption with STRICT canonical
  lexicographic rank descent and full supreme pullback, or one of the
  two explicit unresolved physical cases: two designated neighboring
  reduced labels or order-one vertex/wagon bridges.

The conclusion makes the EXACTLY-TWO-CUT requirement explicit in every
unresolved branch. No all-designated or order-one bridge transfer is
claimed, and no circular appeal to the output SupremeCycleBound occurs.
No support pruning, fake B-label identities, appendix, or manuscript edit.
-/

namespace StructuralRamsey.Girth
open StructuralRamsey.RelStructure

universe u v
section PositiveCutTwoCutRankGate

variable {L : RelLanguage.{u}} {UA VB P X Y I : Type v}
variable (A : RelStructure L UA) (hA : A.Irreducible)
variable (B : RelStructure L VB) (D : RelStructure L P)
variable (C : StructuralRamsey.Partite.System L P X)
variable (family : Set (RelStructure.Embedding B D))
variable (selected : Set (DesignatedCopy B D C family))
variable (e : RelStructure.Embedding A D) (R : RelStructure L Y)
variable (f : I → RelStructure.Embedding
  (C.toRelStructure.induce (activeCarrier A C e.toFunctionEmbedding)) R)
variable {m : ℕ}
variable (T : EdgeTrainLevels (OldACarrierEdge A C.toRelStructure) m)
variable (U : EdgeTrainLevels (OldACarrierEdge A R) m)
variable (hShared : ∀ _i : I, Nonempty (SharedOldACarrierEdge A C.toRelStructure
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
local notation "OldEdge" => OldACarrierEdge A C.toRelStructure
local notation "Selected" =>
  {b : DesignatedCopy B D C family // b ∈ selected}
local notation "Out" => attachedSelectedPictureOrderOneData
  A hA B D C family selected e R f T U hShared μ
local notation "Old" => selectedPictureOrderOneData
  A B D C family selected T μ
local notation "GeomAllowed" => selectedOutputGeometricOwnerAllowed
  A hA B D C family selected e R f T U hShared μ
local notation "Wit" => sharedWitnessOrderOneData U μ
  (sharedOldACarrierCoreEmbedding A C.toRelStructure S R f)
  (Subtype.val : CoreEdge → Set Y)
local notation "CycleRank" => attachedSelectedPicture_geometricLexRank
  A hA B D C family selected e R f T U hShared μ

include hRel

/-- Assuming precisely the strongness and genuine old/witness girth
inputs already present in the three-cut transfer, every acceptable
positive-cut cycle either has a complete supreme plan, admits a full
physical supreme-pullback strict lex-rank descent, or has EXACTLY TWO
geometric owner cuts and one of the two remaining physical obstructions.

This packages the entire >=3-cut case into a finished logical branch
of the global well-founded induction, without asserting the final
two-cut bridges or all-designated physical replacements. -/
theorem attachedSelectedPicture_positive_cut_rank_or_exact_two_cut_obstruction
    [Finite UA]
    (hStrong : ∀ b : RelStructure.Embedding B D, b ∈ family →
      AStrong A D (copyCarrier b))
    (hTwoCopies : ∀ b : Selected, ∃ r s : OldEdge,
      r ≠ s ∧ r.1 ⊆ copyCarrier b.1.embedding ∧
        s.1 ⊆ copyCarrier b.1.embedding)
    (hOldStrong : AStrong A C.toRelStructure S)
    (hCoreStrong : ∀ j : I, AStrong A R (copyCarrier (f j)))
    {n q : ℕ} (K : (Out).BigCycle n)
    (hAccept : K.Acceptable) (hn : 3 ≤ n)
    (hLinear : (Out).LinearPretrain)
    (hOrder : K.twiceOrder ≤ 2 * q)
    (owner : Fin n → I ⊕ CoreEdge)
    (hAllowed : ∀ j, GeomAllowed (K.label j) (owner j))
    (hMinimal : ∀ other : Fin n → I ⊕ CoreEdge,
      (∀ j, GeomAllowed (K.label j) (other j)) →
      cyclicOwnerChanges owner ≤ cyclicOwnerChanges other)
    (hCuts : 2 ≤ cyclicOwnerChanges owner)
    (hq : 1 ≤ q)
    (hWitness : (Wit).FullSystemGirthGT q)
    (hOldSupreme : (Old).SupremeCycleBound q) :
    let Z := attachedSelectedPicture_geometric_cutBigCycle
      A hA B D C family selected e R f T U hShared hRel μ
      K owner hAllowed hCuts
    K.HasSimultaneousSupreme ∨
    (∃ H : (Out).BigCycle n,
      H.Acceptable ∧ H.twiceOrder = K.twiceOrder ∧
      Prod.Lex (· < ·) (· < ·) (CycleRank H) (CycleRank K) ∧
      (H.HasSimultaneousSupreme → K.HasSimultaneousSupreme)) ∨
    (cyclicOwnerChanges owner = 2 ∧
      ((∃ target : Fin (cyclicOwnerChanges owner),
        ∃ i before after : I,
        Z.HasSupremeAt Wit target ∧
        Z.label target = Sum.inl i ∧
        Z.label (trainCyclicPred target) = Sum.inl before ∧
        Z.label (cyclicSucc target) = Sum.inl after) ∨
      (∃ (x : Y) (p : Quotient (U.wagonSetoid μ)),
        (∃ a b : Fin (cyclicOwnerChanges owner), a ≠ b ∧
          Z.connector a = Sum.inl x ∧ Z.connector b = Sum.inr p) ∧
        ∀ k, (Wit).Bridge (Z.label k) x p))) := by
  by_cases hThree : 3 ≤ cyclicOwnerChanges owner
  · exact Or.inl <|
      attachedSelectedPicture_three_cut_full_supreme_of_old_and_witness
        A hA B D C family selected e R f T U hShared hRel μ
        hStrong hTwoCopies hOldStrong hCoreStrong
        K hAccept hLinear hn hOrder owner hAllowed hThree
        hq hWitness hOldSupreme
  · have hExactlyTwo : cyclicOwnerChanges owner = 2 := by omega
    rcases attachedSelectedPicture_positive_cut_rank_descent_or_designated_or_bridges
      A hA B D C family selected e R f T U hShared hRel μ
      K hAccept hn hLinear owner hAllowed hMinimal
      hCuts hq hWitness hOrder with hDescent | hRest
    · exact Or.inr (Or.inl hDescent)
    · exact Or.inr (Or.inr ⟨hExactlyTwo, hRest⟩)

end PositiveCutTwoCutRankGate
end StructuralRamsey.Girth
