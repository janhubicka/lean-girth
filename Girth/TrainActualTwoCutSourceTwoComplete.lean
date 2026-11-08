import Girth.TrainOriginalSelectedMixedSourceClosure
import Girth.TrainTwoCycleOriginalVertexFullSupreme
import Girth.TrainTwoCycleOriginalDesignatedOfLinear
import Girth.TrainActualTwoCutDoubleWagonExclusion
import Girth.TrainActualMinimalTwoCutResidualClosure
import Mathlib.Tactic

set_option autoImplicit false
set_option Elab.async false

/-!
# Path A: complete ORIGINAL length-two, two-geometric-cut source cases

The original output BigCycle has two occurrences, two genuine owner
changes, and a minimum GEOMETRIC owner assignment (not a literal
source-label owner assignment). LinearPretrain forces an ORIGINAL
designated selected B-label (i,q). Minimality makes the OTHER chosen
geometric owner genuinely different from this ORIGINAL i.

Both real cuts provide exact connector lifts to the lower core witness.
The four physical connector cases are exhaustive:

* two vertices: old source/witness physical short-or-long and literal
  ORIGINAL standard map, with true strict all-length global plan;
* vertex/wagon in either order: old original selected-copy mixed probe,
  witness shadow bridge and strict global short plan;
* two wagons: impossible under true witness FullSystemGirthGT and q>=2.

This does not assume output FullSystemGirthGT, a reduced supreme oracle,
a fake original B-label/geometric owner equality, a high-girth partite
power, or any physical A-support pruning. A separate n>=3 two-cut
theorem remains the sole geometric callback in the full output closure.

The imported source modules are copied from unmerged draft PRs; this
integration is UNVERIFIED until all exact-head Lean/axiom CI passes.
No manuscript / appendix edits.
-/

namespace StructuralRamsey.Girth
open StructuralRamsey.RelStructure

universe u v
section SourceTwoComplete

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
variable (hShared : ∀ i : I, Nonempty
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
local notation "CoreEdge" => OldACarrierEdge A R
local notation "Selected" =>
  {q : DesignatedCopy B D C family // q ∈ selected}
local notation "Emb" => sharedOldACarrierCoreEmbedding
  A C.toRelStructure S R f
local notation "CoreEmb" => RelStructure.Attachment.coreEmbedding
  C.toRelStructure S R f
local notation "Train" => generatedActualASupportTrain
  A hA C.toRelStructure S R f T U hShared
local notation "CoreWagon" => generatedActualASupportTrain_coreWagonEmbedding
  A hA C.toRelStructure S R f T U
  (fun ν j p q h => (hRel ν j p q).mp h) hShared μ
local notation "Out" => attachedSelectedPictureOrderOneData
  A hA B D C family selected e R f T U hShared μ
local notation "Old" => selectedPictureOrderOneData
  A B D C family selected T μ
local notation "Wit" => sharedWitnessOrderOneData U μ
  Emb (Subtype.val : CoreEdge → Set Y)
local notation "GeomAllowed" => selectedOutputGeometricOwnerAllowed
  A hA B D C family selected e R f T U hShared μ

include hRel

/-- The EXACT original n=2 source is globally simultaneous-supreme for
ALL physical connector kinds, under old/witness positive full system
bounds, linearity, real A-strong standards and a MINIMAL two-cut owner
assignment. No separately assumed local original B-copy piece. -/
theorem attachedSelectedPicture_two_cycle_two_cut_full_supreme
    {qcut : ℕ} (hq : 1 ≤ qcut)
    (hLinear : (Out).LinearPretrain)
    (hOldStrong : AStrong A C.toRelStructure S)
    (hCoreStrong : ∀ j : I, AStrong A R (copyCarrier (f j)))
    (hOld : (Old).SupremeCycleBound qcut)
    (hWitness : (Wit).FullSystemGirthGT qcut)
    (K : (Out).BigCycle 2) (hAccept : K.Acceptable)
    (hOrder : K.twiceOrder ≤ 2 * qcut)
    (owner : Fin 2 → I ⊕ CoreEdge)
    (hAllowed : ∀ k, GeomAllowed (K.label k) (owner k))
    (hMinimal : ∀ other : Fin 2 → I ⊕ CoreEdge,
      (∀ k, GeomAllowed (K.label k) (other k)) →
        cyclicOwnerChanges owner ≤ cyclicOwnerChanges other)
    (hTwo : cyclicOwnerChanges owner = 2) :
    K.HasSimultaneousSupreme := by
  obtain ⟨target, hTarget⟩ :=
    OrderOneData.BigCycle.two_has_designated_of_linear
      (Out) K hAccept hLinear
  cases hOriginal : K.label target with
  | inr edge =>
      have hFalse : False := by
        simpa [hOriginal, OrderOneData.designated] using hTarget
      exact False.elim hFalse
  | inl iq =>
      rcases iq with ⟨i, q⟩
      have hLiteral : K.label target = Sum.inl (i,q) := hOriginal
      have hOther : Sum.inl i ≠ owner (cyclicSucc target) :=
        attachedSelectedPicture_two_cycle_original_standard_diff_shadow
          A hA B D C family selected e R f T U hShared μ
          K owner hAllowed hMinimal hTwo target i q hLiteral
      have hCut (k : Fin 2) : owner k ≠ owner (cyclicSucc k) :=
        cyclicOwner_two_cut_source_two_every_position owner hTwo k
      obtain ⟨c0, hLift0⟩ :=
        attachedSelectedPicture_geometric_cut_connector_lift
          A hA B D C family selected e R f T U hShared hRel μ
          K owner hAllowed 0 (hCut 0)
      obtain ⟨c1, hLift1⟩ :=
        attachedSelectedPicture_geometric_cut_connector_lift
          A hA B D C family selected e R f T U hShared hRel μ
          K owner hAllowed 1 (hCut 1)
      cases c0 with
      | inl x =>
          have h0 : K.connector (0 : Fin 2) = Sum.inl (CoreEmb x) := by
            simpa using hLift0.symm
          cases c1 with
          | inl y =>
              have h1 : K.connector (1 : Fin 2) = Sum.inl (CoreEmb y) := by
                simpa using hLift1.symm
              have hFour : K.twiceOrder = 4 := by
                simp [OrderOneData.BigCycle.twiceOrder, Fin.sum_univ_two,
                  cyclicSucc, OrderOneData.connectorKind,
                  twiceOccurrenceWeight, h0, h1]
              have hqTwo : 2 ≤ qcut := by omega
              exact attachedSelectedPicture_two_vertex_full_supreme_of_core_connectors
                A hA B D C family selected e R f T U hShared hRel μ
                hqTwo hOld hWitness hLinear hOldStrong hCoreStrong
                K hAccept owner hAllowed hTwo hMinimal
                target i q hLiteral x y h0 h1
          | inr p =>
              have h1 : K.connector (1 : Fin 2) =
                  Sum.inr (CoreWagon p) := by
                simpa using hLift1.symm
              exact attachedSelectedPicture_two_cycle_mixed_full_supreme_of_distinct_shadow
                A hA B D C family selected e R f T U hShared hRel μ
                hq hOld hWitness K hAccept owner hAllowed hTwo
                target i q hLiteral hOther x p (Or.inl ⟨h0,h1⟩)
      | inr p =>
          have h0 : K.connector (0 : Fin 2) =
              Sum.inr (CoreWagon p) := by
            simpa using hLift0.symm
          cases c1 with
          | inl x =>
              have h1 : K.connector (1 : Fin 2) =
                  Sum.inl (CoreEmb x) := by
                simpa using hLift1.symm
              exact attachedSelectedPicture_two_cycle_mixed_full_supreme_of_distinct_shadow
                A hA B D C family selected e R f T U hShared hRel μ
                hq hOld hWitness K hAccept owner hAllowed hTwo
                target i q hLiteral hOther x p (Or.inr ⟨h0,h1⟩)
          | inr r =>
              have h1 : K.connector (1 : Fin 2) =
                  Sum.inr (CoreWagon r) := by
                simpa using hLift1.symm
              have hFour : K.twiceOrder = 4 := by
                simp [OrderOneData.BigCycle.twiceOrder, Fin.sum_univ_two,
                  cyclicSucc, OrderOneData.connectorKind,
                  twiceOccurrenceWeight, h0, h1]
              have hqTwo : 2 ≤ qcut := by omega
              have hEveryWagon : ∀ k : Fin 2,
                  ∃ w : Quotient ((Train).wagonSetoid μ),
                    K.connector k = Sum.inr w := by
                intro k
                fin_cases k
                · exact ⟨CoreWagon p, h0⟩
                · exact ⟨CoreWagon r, h1⟩
              have hAtCut :
                  ∀ k : Fin (cyclicOwnerChanges owner),
                    ∃ w : Quotient ((Train).wagonSetoid μ),
                      K.connector (cyclicOwnerCutIndex owner k) = Sum.inr w :=
                fun k => hEveryWagon (cyclicOwnerCutIndex owner k)
              exact False.elim
                (attachedSelectedPicture_two_cut_double_wagon_absurd_of_witness
                  A hA B D C family selected e R f T U hShared hRel μ
                  K owner hAllowed hTwo hAtCut hWitness hqTwo)

/-- A picture-step output-girth theorem needs only the already separate
source length >=3 two-cut transfer once the n=2 cases above are present.
The closure retains exactly the ORIGINAL strongness, two old A-edge
and real witness/old supremeness premises of the circulation proof. -/
theorem attachedSelectedPicture_fullSystemGirth_of_three_le_two_cut
    [Finite UA]
    (qcut : ℕ) (hq : 1 ≤ qcut)
    (hLinear : (Out).LinearPretrain)
    (hStrong : ∀ b : RelStructure.Embedding B D, b ∈ family →
      AStrong A D (copyCarrier b))
    (hTwoSupport : ∀ r : Selected, ∃ x y : OldACarrierEdge A C.toRelStructure,
      x ≠ y ∧ x.1 ⊆ copyCarrier r.1.embedding ∧
        y.1 ⊆ copyCarrier r.1.embedding)
    (hOldStrong : AStrong A C.toRelStructure S)
    (hCoreStrong : ∀ i : I, AStrong A R (copyCarrier (f i)))
    (hOld : (Old).SupremeCycleBound qcut)
    (hWitness : (Wit).FullSystemGirthGT qcut)
    (hThree : ∀ {n : ℕ} (K : (Out).BigCycle n),
      3 ≤ n → K.Acceptable →
      (owner : Fin n → I ⊕ CoreEdge) →
      (∀ k, GeomAllowed (K.label k) (owner k)) →
      (∀ other : Fin n → I ⊕ CoreEdge,
        (∀ k, GeomAllowed (K.label k) (other k)) →
          cyclicOwnerChanges owner ≤ cyclicOwnerChanges other) →
      cyclicOwnerChanges owner = 2 →
      K.twiceOrder ≤ 2 * qcut →
      K.HasSimultaneousSupreme) :
    (Out).FullSystemGirthGT qcut := by
  apply attachedSelectedPicture_fullSystemGirth_of_minimal_two_cut_cases
    A hA B D C family selected e R f T U hShared hRel μ
    qcut hq hLinear hStrong hTwoSupport hOldStrong hCoreStrong
    hOld hWitness
  intro n K hAccept owner hAllowed hMinimal hExactlyTwo hOrder
  by_cases hn : n = 2
  · subst n
    exact attachedSelectedPicture_two_cycle_two_cut_full_supreme
      A hA B D C family selected e R f T U hShared hRel μ
      hq hLinear hOldStrong hCoreStrong hOld hWitness
      K hAccept hOrder owner hAllowed hMinimal hExactlyTwo
  · have hnThree : 3 ≤ n := by
      have hnTwo := K.length_ge_two
      omega
    exact hThree K hnThree hAccept owner hAllowed hMinimal
      hExactlyTwo hOrder

end SourceTwoComplete
end StructuralRamsey.Girth
