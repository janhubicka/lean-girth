import Girth.TrainActualPositiveCutNeighborDichotomy
import Girth.TrainActualPositiveCutSupremeOrBridges

/-!
# Full-system-girth trichotomy for an actual positive-cut cycle

The real shared-witness FullSystemGirthGT condition, together with
the actual geometric cut restriction, provides either a globally
legal supreme reduced witness plan or its honest order-one
vertex/wagon physical bridges.

When an indexed supreme standard has a CORE EDGE on either side,
the verified singleton absorption moves the original selected
picture cycle to strictly fewer MINIMAL cuts, preserving its length,
twice-order, and acceptability. Otherwise both reduced neighbors
of that supreme standard are genuinely DESIGNATED gluing standards.

The result does not assert that these all-designated neighbors can
already be absorbed or that the order-one bridges give a legal
designated-retaining source replacement. Those are the residual
physical-transfer obligations. No appendix.
-/

namespace StructuralRamsey.Girth
open StructuralRamsey.RelStructure

universe u v
section PositiveCutFullWitnessTrichotomy

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
local notation "Wit" => sharedWitnessOrderOneData U μ
  (sharedOldACarrierCoreEmbedding A C.toRelStructure S R f)
  (Subtype.val : CoreEdge → Set Y)
local notation "GeomAllowed" => selectedOutputGeometricOwnerAllowed
  A hA B D C family selected e R f T U hShared μ

include hRel

/-- An actual acceptable selected-picture BigCycle (n >= 3) of
positive cut number, under the genuine witness full system girth
bound, has exactly the three useful alternatives:
* one physical short step yields an acceptable same-order cycle with
  STRICTLY fewer MINIMAL geometric cuts;
* a globally supreme reduced standard has designated neighbors on
  BOTH sides; or
* the reduced order-one word has two genuine physical bridges.

This is a reduction, not the final induction: all-designated and
order-one branches remain open. -/
theorem attachedSelectedPicture_positive_cut_descent_or_designated_or_bridges
    {n q : ℕ} (K : (Out).BigCycle n)
    (hAccept : K.Acceptable) (hn : 3 ≤ n)
    (owner : Fin n → I ⊕ CoreEdge)
    (hAllowed : ∀ j, GeomAllowed (K.label j) (owner j))
    (hCuts : 2 ≤ cyclicOwnerChanges owner)
    (hq : 1 ≤ q) (hWitness : (Wit).FullSystemGirthGT q)
    (hOrder : K.twiceOrder ≤ 2 * q) :
    let Z := attachedSelectedPicture_geometric_cutBigCycle
      A hA B D C family selected e R f T U hShared hRel μ
      K owner hAllowed hCuts
    (∃ H : (Out).BigCycle n,
      OrderOneData.BigCycle.PhysicalShortReachable Out K H ∧
      H.Acceptable ∧ H.twiceOrder = K.twiceOrder ∧
      ∃ newOwner : Fin n → I ⊕ CoreEdge,
        (∀ j, GeomAllowed (H.label j) (newOwner j)) ∧
        (∀ other : Fin n → I ⊕ CoreEdge,
          (∀ j, GeomAllowed (H.label j) (other j)) →
          cyclicOwnerChanges newOwner ≤ cyclicOwnerChanges other) ∧
        cyclicOwnerChanges newOwner < cyclicOwnerChanges owner) ∨
    (∃ target : Fin (cyclicOwnerChanges owner), ∃ i before after : I,
      Z.HasSupremeAt Wit target ∧ Z.label target = Sum.inl i ∧
      Z.label (trainCyclicPred target) = Sum.inl before ∧
      Z.label (cyclicSucc target) = Sum.inl after) ∨
    (∃ (x : Y) (p : Quotient (U.wagonSetoid μ)),
      (∃ a b : Fin (cyclicOwnerChanges owner), a ≠ b ∧
        Z.connector a = Sum.inl x ∧ Z.connector b = Sum.inr p) ∧
      ∀ k, (Wit).Bridge (Z.label k) x p) := by
  let Z := attachedSelectedPicture_geometric_cutBigCycle
    A hA B D C family selected e R f T U hShared hRel μ
    K owner hAllowed hCuts
  have hAlternative := attachedSelectedPicture_positive_cut_supreme_or_bridges
    A hA B D C family selected e R f T U hShared hRel μ
    K owner hAllowed hCuts hAccept hq hWitness hOrder
  rcases hAlternative with hSup | hBridges
  · obtain ⟨target, hDesignated, pieces, hValid, hGlobal⟩ := hSup
    cases ht : Z.label target with
    | inr edge =>
        have : False := by
          have h := hDesignated
          simp [OrderOneData.designated, ht] at h
        exact False.elim this
    | inl i =>
        have hAt : Z.HasSupremeAt Wit target :=
          ⟨hDesignated, pieces, hValid, hGlobal⟩
        rcases attachedSelectedPicture_positive_cut_edge_neighbor_or_two_designated
          A hA B D C family selected e R f T U hShared hRel μ
          K hAccept hn owner hAllowed hCuts target i ht hAt
          with hStep | hBoth
        · exact Or.inl hStep
        · obtain ⟨before, after, hb, ha⟩ := hBoth
          exact Or.inr (Or.inl ⟨target, i, before, after,
            hAt, ht, hb, ha⟩)
  · exact Or.inr (Or.inr hBridges)

end PositiveCutFullWitnessTrichotomy
end StructuralRamsey.Girth
