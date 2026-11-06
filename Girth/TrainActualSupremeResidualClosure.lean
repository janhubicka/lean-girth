import Girth.TrainNoSingleCyclicOwnerCut
import Girth.TrainActualPositiveCutRankTrichotomy
import Girth.TrainActualZeroCutGlobalSupreme
import Girth.TrainSupremeLexRankInduction

set_option autoImplicit false
set_option Elab.async false

/-!
# Complete global system girth reduces to the remaining physical exceptions

This is the final NON-GEOMETRIC closure step for the attached selected
picture's full simultaneous-supreme cycle condition.

For each acceptable output BigCycle, choose the actual minimum among
all admissible GEOMETRIC standard/core-edge owners. The genuine
finite-cyclic lemma shows that its number of cuts is either zero or
at least two. The zero-cut case lifts a legal global old-picture
supreme plan; for at least three source positions the checked physical
positive-cut trichotomy produces either a STRICT intrinsic lexicographic
rank descent (with complete global supreme pullback), or exactly one
of TWO explicitly retained geometric exceptions:
  (i) a designated supreme reduced standard with designated neighbours
      on both sides;
  (ii) a reduced order-one vertex/wagon word with physical bridges.

The separate length-two output case also remains an explicit physical
hypothesis. Once exactly these exceptional cases have been solved,
the existing well-founded rank theorem proves FULL SupremeCycleBound
and (with genuine pretrain linearity) FULL FullSystemGirthGT.

No global supreme plan is postulated for ordinary positive-cut cycles,
no phantom lower-stage witness is constructed, and no local-piece
bound is substituted for globally legal simultaneous replacement.
In particular this theorem is CONDITIONAL and should not be used as
an unconditional validation marker in the circulation manuscript.
No appendix.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v
section AttachedCycleExceptionalClosure

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
variable (hShared : ∀ _i : I, Nonempty
  (SharedOldACarrierEdge A C.toRelStructure
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
local notation "Selected" => {q : DesignatedCopy B D C family // q ∈ selected}
local notation "OldEdge" => OldACarrierEdge A C.toRelStructure
local notation "CoreEdge" => OldACarrierEdge A R
local notation "Out" => attachedSelectedPictureOrderOneData
  A hA B D C family selected e R f T U hShared μ
local notation "Old" => selectedPictureOrderOneData
  A B D C family selected T μ
local notation "Wit" => sharedWitnessOrderOneData U μ
  (sharedOldACarrierCoreEmbedding A C.toRelStructure S R f)
  (Subtype.val : CoreEdge → Set Y)
local notation "GeomAllowed" => selectedOutputGeometricOwnerAllowed
  A hA B D C family selected e R f T U hShared μ
local notation "CycleRank" => attachedSelectedPicture_geometricLexRank
  A hA B D C family selected e R f T U hShared μ

include hRel

/-- A complete attached-output system-girth certificate follows once
the genuine length-two source case and the EXACT two residual
positive-cut geometric alternatives are discharged.

All other cases are already established by zero-cut global transfer,
physical short-absorption with strict intrinsic rank decrease,
and well-founded induction. No assumptions about an abstract
rank-descent oracle, arbitrary chosen owner, or local-only pieces. -/
theorem attachedSelectedPicture_fullSystemGirth_of_residual_cases
    [Finite UA]
    (q : ℕ) (hq : 1 ≤ q)
    (hLinear : (Out).LinearPretrain)
    (hStrong : ∀ b : Embedding B D, b ∈ family →
      AStrong A D (copyCarrier b))
    (hTwo : ∀ r : Selected, ∃ x y : OldEdge,
      x ≠ y ∧ x.1 ⊆ copyCarrier r.1.embedding ∧
        y.1 ⊆ copyCarrier r.1.embedding)
    (hOldStrong : AStrong A C.toRelStructure S)
    (hCoreStrong : ∀ i : I, AStrong A R (copyCarrier (f i)))
    (hOldSupreme : (Old).SupremeCycleBound q)
    (hWitness : (Wit).FullSystemGirthGT q)
    (hTwoCycle : ∀ (K : (Out).BigCycle 2),
      K.Acceptable → K.twiceOrder ≤ 2 * q →
      K.HasSimultaneousSupreme)
    (hExceptions : ∀ {n : ℕ} (K : (Out).BigCycle n)
      (hAccept : K.Acceptable) (hn : 3 ≤ n)
      (owner : Fin n → I ⊕ CoreEdge)
      (hAllowed : ∀ j, GeomAllowed (K.label j) (owner j))
      (hMinimal : ∀ other : Fin n → I ⊕ CoreEdge,
        (∀ j, GeomAllowed (K.label j) (other j)) →
        cyclicOwnerChanges owner ≤ cyclicOwnerChanges other)
      (hCuts : 2 ≤ cyclicOwnerChanges owner)
      (hOrder : K.twiceOrder ≤ 2 * q),
      let Z := attachedSelectedPicture_geometric_cutBigCycle
        A hA B D C family selected e R f T U hShared hRel μ
        K owner hAllowed hCuts
      ((∃ target : Fin (cyclicOwnerChanges owner),
          ∃ i before after : I,
          Z.HasSupremeAt Wit target ∧
          Z.label target = Sum.inl i ∧
          Z.label (trainCyclicPred target) = Sum.inl before ∧
          Z.label (cyclicSucc target) = Sum.inl after) ∨
        (∃ x : Y, ∃ p : Quotient (U.wagonSetoid μ),
          (∃ a b : Fin (cyclicOwnerChanges owner),
            a ≠ b ∧ Z.connector a = Sum.inl x ∧
              Z.connector b = Sum.inr p) ∧
          ∀ k, (Wit).Bridge (Z.label k) x p)) →
      K.HasSimultaneousSupreme) :
    (Out).FullSystemGirthGT q := by
  have hStep : ∀ {n : ℕ} (K : (Out).BigCycle n),
      K.Acceptable → K.twiceOrder ≤ 2 * q →
      K.HasSimultaneousSupreme ∨
        ∃ (r : ℕ) (H : (Out).BigCycle r),
          H.Acceptable ∧ H.twiceOrder ≤ 2 * q ∧
          Prod.Lex (· < ·) (· < ·) (CycleRank H) (CycleRank K) ∧
          (H.HasSimultaneousSupreme → K.HasSimultaneousSupreme) := by
    intro n K hAccept hOrder
    obtain ⟨owner, hAllowed, hMinimal⟩ :=
      attachedSelectedPicture_cycle_exists_minimal_geometric_owners
        A hA B D C family selected e R f T U hShared μ K
    rcases cyclicOwnerChanges_zero_or_two_le K.length_ge_two owner
      with hZero | hCuts
    · exact Or.inl
        (attachedSelectedPicture_zero_cut_supreme_of_old_bound
          A hA B D C family selected e R f T U hShared hRel μ
          hStrong hTwo hOldStrong hCoreStrong
          K hAccept hOldSupreme hOrder owner hAllowed hZero)
    · by_cases hn : 3 ≤ n
      · rcases
          attachedSelectedPicture_positive_cut_rank_descent_or_designated_or_bridges
            A hA B D C family selected e R f T U hShared hRel μ
            K hAccept hn hLinear owner hAllowed hMinimal
            hCuts hq hWitness hOrder
          with hDrop | hException
        · obtain ⟨H, hHAccept, hSameOrder, hRank, hPull⟩ := hDrop
          refine Or.inr ⟨n, H, hHAccept, ?_, hRank, hPull⟩
          rw [hSameOrder]
          exact hOrder
        · exact Or.inl
            (hExceptions K hAccept hn owner hAllowed hMinimal
              hCuts hOrder hException)
      · have heq : n = 2 := by
          have hmin := K.length_ge_two
          omega
        subst n
        exact Or.inl (hTwoCycle K hAccept hOrder)
  exact ⟨hLinear,
    (Out).supremeCycleBound_of_lexDescent q
      (fun _ K => CycleRank K) hStep⟩

end AttachedCycleExceptionalClosure

end StructuralRamsey.Girth
