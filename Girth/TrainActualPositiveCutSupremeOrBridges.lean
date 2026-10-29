import Girth.TrainActualCutReductionDichotomy

/-!
# Genuine positive-cut witness: supreme plan or both physical bridges

The cut-defined witness BigCycle is now constructed, with length,
twice-order, A2/A3 and the exhaustive numerical order dichotomy.
Above order one it is acceptable. The ACTUAL witness
FullSystemGirthGT q therefore gives a globally legal simultaneous
supreme plan on the reduced cycle; at order one the existing bridge
theorem supplies the two physical bridges without falsely asserting
A1 of an edge-only reduced word.

No new picture geometry, artificial designated source label, or
assumption of a legal target word is introduced. This is the exact
positive-cut output alternative needed by the circulation transfer.
Its subsequent physical short-replacement transfer remains open.
-/

namespace StructuralRamsey.Girth
open StructuralRamsey.RelStructure

universe u v
section PositiveCutSupremeAlternative

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

/-- For a genuine positive-cut selected output cycle, the entire
reduced witness cycle has an ACTUAL global supreme replacement plan,
or it is of order one with two real physical witness bridges. In
particular the higher-order case consumes the witness SupremeCycleBound
at the correct twice-order WITHOUT an extra acceptability premise
on an edge-only two-occurrence cycle. -/
theorem attachedSelectedPicture_positive_cut_supreme_or_bridges
    {n q : ℕ} (K : (Out).BigCycle n)
    (owner : Fin n → I ⊕ CoreEdge)
    (hAllowed : ∀ k : Fin n, GeomAllowed (K.label k) (owner k))
    (hCuts : 2 ≤ cyclicOwnerChanges owner)
    (hAccept : K.Acceptable)
    (hq : 1 ≤ q)
    (hWitness : (Wit).FullSystemGirthGT q)
    (hOrder : K.twiceOrder ≤ 2 * q) :
    let Z := attachedSelectedPicture_geometric_cutBigCycle
      A hA B D C family selected e R f T U hShared hRel μ
      K owner hAllowed hCuts
    Z.HasSimultaneousSupreme ∨
      ∃ (x : Y) (p : Quotient (U.wagonSetoid μ)),
        (∃ i j : Fin (cyclicOwnerChanges owner), i ≠ j ∧
          Z.connector i = Sum.inl x ∧ Z.connector j = Sum.inr p) ∧
        ∀ k, (Wit).Bridge (Z.label k) x p := by
  let Z := attachedSelectedPicture_geometric_cutBigCycle
    A hA B D C family selected e R f T U hShared hRel μ
    K owner hAllowed hCuts
  obtain ⟨hBounds, hCases, hAcceptAbove, hBridges⟩ :=
    attachedSelectedPicture_geometric_cut_reduction_dichotomy
      A hA B D C family selected e R f T U hShared hRel μ
      K owner hAllowed hCuts hAccept hq hWitness
  rcases hCases with hOne | hAbove
  · exact Or.inr (hBridges hOne)
  · have hAcceptZ : Z.Acceptable := hAcceptAbove hAbove
    have hOrderZ : Z.twiceOrder ≤ 2 * q :=
      (hBounds.2.1).trans hOrder
    exact Or.inl (hWitness.2 _ Z hAcceptZ hOrderZ)

end PositiveCutSupremeAlternative
end StructuralRamsey.Girth
