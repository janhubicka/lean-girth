import Girth.TrainActualTwoCutSymmetricShortSupreme
import Girth.TrainTwoVertexPairEdgeShortValidBoth
import Mathlib.Tactic

set_option autoImplicit false
set_option Elab.async false

/-!
# Path A: full original-source supreme transfer in the two-cut pair-edge case

The attached selected picture has EXACTLY TWO geometric owner cuts.
Its genuine cut-indexed witness BigCycle has two distinct designated
standard labels and two VERTEX connectors x,y. Suppose that a real
physical core support edge contains both x and y.

At original source length n >= 3 and twice-order <= 2q, q is
automatically at least two. Genuine witness FullSystemGirthGT q
then makes this SAME core edge belong to both reduced designated
standard edge families, using the already checked pair-edge
ownership theorem. In particular it is a real ShortValid piece
at BOTH reduced cuts, each time with the OTHER standard as target.

The source A2/A3 two-contact theorem selects the unique forward
singleton owner run. The checked singleton-complement theorem
proves all remaining original source positions have the OTHER
standard as geometric owner. Finally the checked original-source
one-short/all-keep standard transfer plus OLD SupremeCycleBound
gives the entire ORIGINAL K.HasSimultaneousSupreme.

No reduced existential supreme plan is switched or reselected,
no original B-copy label is equated with an owner standard,
and all physical edge and wagon labels remain genuine.

This closes only the two-cut vertex/vertex PAIR-EDGE branch,
assuming the ordinary old/witness induction inputs. The
two-cut vertex/vertex no-pair LONG and mixed order-one
physical bridge cases remain separate. No appendix or paper edit.
-/

namespace StructuralRamsey.Girth
open StructuralRamsey.RelStructure

universe u v
section ActualTwoCutPairEdgeFullSource

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
local notation "Selected" => {r : DesignatedCopy B D C family // r ∈ selected}
local notation "Out" => attachedSelectedPictureOrderOneData
  A hA B D C family selected e R f T U hShared μ
local notation "Old" => selectedPictureOrderOneData
  A B D C family selected T μ
local notation "Wit" => sharedWitnessOrderOneData U μ
  (sharedOldACarrierCoreEmbedding A C.toRelStructure S R f)
  (Subtype.val : CoreEdge → Set Y)
local notation "GeomAllowed" => selectedOutputGeometricOwnerAllowed
  A hA B D C family selected e R f T U hShared μ

include hRel

/-- Pair-edge closure of the genuine exactly-two-cut, two-standard
vertex/vertex positive-cut reduction. The old bound is used ONLY in
the final zero-cut standard transfer, and the full witness bound
ONLY to derive real ShortValid membership in both standards. -/
theorem attachedSelectedPicture_two_cut_pairEdge_full_supreme
    [Finite UA]
    (hStrong : ∀ r : RelStructure.Embedding B D, r ∈ family →
      AStrong A D (copyCarrier r))
    (hTwoCopies : ∀ r : Selected, ∃ a c : OldEdge,
      a ≠ c ∧ a.1 ⊆ copyCarrier r.1.embedding ∧
        c.1 ⊆ copyCarrier r.1.embedding)
    (hOldStrong : AStrong A C.toRelStructure S)
    (hCoreStrong : ∀ j : I, AStrong A R (copyCarrier (f j)))
    {n q : ℕ} (K : (Out).BigCycle n)
    (hAccept : K.Acceptable) (hLinear : (Out).LinearPretrain)
    (hn : 3 ≤ n) (hOrder : K.twiceOrder ≤ 2 * q)
    (owner : Fin n → I ⊕ CoreEdge)
    (hAllowed : ∀ j, GeomAllowed (K.label j) (owner j))
    (hTwoCuts : cyclicOwnerChanges owner = 2)
    (i j : I)
    (hLabel0 : (attachedSelectedPicture_geometric_cutBigCycle
      A hA B D C family selected e R f T U hShared hRel μ
      K owner hAllowed (by omega)).label ⟨0, by omega⟩ = Sum.inl i)
    (hLabel1 : (attachedSelectedPicture_geometric_cutBigCycle
      A hA B D C family selected e R f T U hShared hRel μ
      K owner hAllowed (by omega)).label ⟨1, by omega⟩ = Sum.inl j)
    (x y : Y)
    (hConnector0 : (attachedSelectedPicture_geometric_cutBigCycle
      A hA B D C family selected e R f T U hShared hRel μ
      K owner hAllowed (by omega)).connector ⟨0, by omega⟩ = Sum.inl x)
    (hConnector1 : (attachedSelectedPicture_geometric_cutBigCycle
      A hA B D C family selected e R f T U hShared hRel μ
      K owner hAllowed (by omega)).connector ⟨1, by omega⟩ = Sum.inl y)
    (hPair : (Wit).PairEdge x y)
    (hWitness : (Wit).FullSystemGirthGT q)
    (hOldSupreme : (Old).SupremeCycleBound q) :
    K.HasSimultaneousSupreme := by
  let Z := attachedSelectedPicture_geometric_cutBigCycle
    A hA B D C family selected e R f T U hShared hRel μ
    K owner hAllowed (by omega : 2 ≤ cyclicOwnerChanges owner)
  have hLength : n ≤ K.twiceOrder :=
    OrderOneData.BigCycle.length_le_twiceOrder Out K
  have hq : 2 ≤ q := by omega
  obtain ⟨b, hbx, hby⟩ := hPair
  have hEveryShort : ∀ cut : Fin (cyclicOwnerChanges owner),
      Z.ShortValid Wit (trainCyclicPred cut) cut b :=
    OrderOneData.BigCycle.two_vertex_pairEdge_shortValid_for_each_cut
      Wit hTwoCuts Z q hq hWitness i j
      hLabel0 hLabel1 x y hConnector0 hConnector1 b hbx hby
  have hStandards : ∀ k : Fin (cyclicOwnerChanges owner),
      ∃ s : I, Z.label k = Sum.inl s := by
    intro k
    have hk : k.val = 0 ∨ k.val = 1 := by
      have hkBound := k.isLt
      omega
    rcases hk with hZero | hOne
    · have hk0 : k = (⟨0, by omega⟩ : Fin (cyclicOwnerChanges owner)) :=
        Fin.ext hZero
      rw [hk0]
      exact ⟨i, hLabel0⟩
    · have hk1 : k = (⟨1, by omega⟩ : Fin (cyclicOwnerChanges owner)) :=
        Fin.ext hOne
      rw [hk1]
      exact ⟨j, hLabel1⟩
  exact attachedSelectedPicture_two_cut_symmetric_short_supreme
    A hA B D C family selected e R f T U hShared hRel μ
    hStrong hTwoCopies hOldStrong hCoreStrong
    K hAccept hLinear hn hOrder
    owner hAllowed hTwoCuts hStandards b hEveryShort hOldSupreme

end ActualTwoCutPairEdgeFullSource
end StructuralRamsey.Girth
