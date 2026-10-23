import Girth.TrainActualCutOrderOneBridges
import Girth.TrainActualCutNonOneAcceptable

/-!
# Exact physical witness-cut reduction dichotomy under full system girth

This theorem assembles, without another combinatorial argument, the
already separated interfaces for an actual selected-picture BigCycle:

- physical owner cuts construct a legal witness BigCycle;
- exact core restriction controls length, numerical order, A2 and A3;
- at order >= 2 the resulting BigCycle is acceptable (A1 vacuous);
- at order 1 both witness labels have genuine short physical bridges,
  even if the target contains no designated label.

The bridge premise is not a new axiom: full witness system-girth at ANY
cutoff at least one implies the previously verified order-one bound.

The one-standard / zero-cut alternative, later segment replacements,
global cycle transfer, filling and recursion are separate.
No appendix proof is used.
-/

namespace StructuralRamsey.Girth
namespace OrderOneData

universe v
variable {V E I P : Type v} (D : OrderOneData V E I P)

/-- Full system-girth above any positive cutoff supplies the exact
order-one physical bridge bound, by monotonicity of the numerical
cycle cutoff and the existing global-to-local consequence. -/
theorem orderOneBound_of_fullSystemGirth_positive
    {q : ℕ} (hq : 1 ≤ q)
    (hFull : D.FullSystemGirthGT q) : D.Bound := by
  apply D.orderOneBound_of_fullSystemGirth
  refine ⟨hFull.1, ?_⟩
  intro n Z hAccept hOrder
  exact hFull.2 n Z hAccept (by omega)

end OrderOneData

open StructuralRamsey.RelStructure

universe u v
section ActualCutReductionDichotomy

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
local notation "Out" => attachedSelectedPictureOrderOneData
  A hA B D C family selected e R f T U hShared μ
local notation "GeomAllowed" => selectedOutputGeometricOwnerAllowed
  A hA B D C family selected e R f T U hShared μ
local notation "Wit" => sharedWitnessOrderOneData U μ
  (sharedOldACarrierCoreEmbedding A C.toRelStructure S R f)
  (Subtype.val : CoreEdge → Set Y)

/-- Circulation's **positive-cut** witness reduction in one statement.
Numerical order/length never increase. If the output cut word has
order at least two, it is acceptable. At order one BOTH labels admit
actual physical witness bridges, without asserting A1 of an edge-only
reduct. Every owner is geometric; no foreign label is relabelled. -/
theorem attachedSelectedPicture_geometric_cut_reduction_dichotomy
    {n q : ℕ} (K : (Out).BigCycle n)
    (owner : Fin n → I ⊕ CoreEdge)
    (hAllowed : ∀ k : Fin n, GeomAllowed (K.label k) (owner k))
    (hCuts : 2 ≤ cyclicOwnerChanges owner)
    (hAccept : K.Acceptable)
    (hq : 1 ≤ q)
    (hWitness : (Wit).FullSystemGirthGT q) :
    let Z := attachedSelectedPicture_geometric_cutBigCycle
      A hA B D C family selected e R f T U hShared hRel μ
      K owner hAllowed hCuts
    (cyclicOwnerChanges owner ≤ n ∧
      Z.twiceOrder ≤ K.twiceOrder ∧ Z.A2 ∧ Z.A3) ∧
    (4 ≤ Z.twiceOrder → Z.Acceptable) ∧
    (Z.twiceOrder = 2 →
      ∃ (x : Y) (p : Quotient (U.wagonSetoid μ)),
        (∃ i j : Fin (cyclicOwnerChanges owner), i ≠ j ∧
          Z.connector i = Sum.inl x ∧ Z.connector j = Sum.inr p) ∧
        ∀ k, (Wit).Bridge (Z.label k) x p) := by
  let Z := attachedSelectedPicture_geometric_cutBigCycle
    A hA B D C family selected e R f T U hShared hRel μ
    K owner hAllowed hCuts
  have hBounds :=
    attachedSelectedPicture_geometric_cut_restriction_bounds
      A hA B D C family selected e R f T U hShared hRel μ
      K owner hAllowed hCuts hAccept.2.1 hAccept.2.2
  refine ⟨hBounds, ?_, ?_⟩
  · intro hOrder
    exact attachedSelectedPicture_geometric_cut_acceptable_of_two_le
      A hA B D C family selected e R f T U hShared hRel μ
      K owner hAllowed hCuts hAccept hOrder
  · intro hOrder
    exact attachedSelectedPicture_geometric_cut_orderOne_bridges
      A hA B D C family selected e R f T U hShared hRel μ
      K owner hAllowed hCuts
      (OrderOneData.orderOneBound_of_fullSystemGirth_positive
        Wit hq hWitness) hOrder

end ActualCutReductionDichotomy
end StructuralRamsey.Girth
