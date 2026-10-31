import Girth.TrainActualReducedCutFreshness

/-!
# Global reduced supreme-plan freshness at every source connector

When every source owner boundary is a genuine cut (for example,
three distinct owner segments around a length-three source cycle),
the canonical cyclic cut enumeration contains EVERY original connector.

Consequently a globally legal supreme long piece in the reduced
witness cannot insert ANY wagon already present in the original
source connector word. This closes the literal cut-freshness
transport part of the exceptional 3-occurrence designated singleton
case, conditional only on its all-boundaries-are-cuts hypothesis.

It does not prove that a particular A2 long-piece configuration
forces n=3; it does not supply a chosen new geometric owner,
and does not prove minimum-cut descent. No appendix.
-/

namespace StructuralRamsey.Girth
open StructuralRamsey.RelStructure

universe u v

/-- A cyclic owner word has the maximum possible number of cuts
exactly when every original position is a cut. Thus the length-three,
three-segment exceptional case retains all original connectors. -/
theorem cyclicOwnerChanges_eq_length_iff_every_cut
    {Owner : Type v} {n : ℕ} (owner : Fin n → Owner) :
    cyclicOwnerChanges owner = n ↔
      ∀ k : Fin n, owner k ≠ owner (cyclicSucc k) := by
  classical
  constructor
  · intro hCount
    have hCard :
        (Finset.univ : Finset (Fin n)).card ≤
          (cyclicOwnerCutPositions owner).card := by
      simpa [cyclicOwnerCutPositions_card] using hCount.symm.le
    have hEq : cyclicOwnerCutPositions owner =
        (Finset.univ : Finset (Fin n)) :=
      Finset.eq_of_subset_of_card_le (Finset.subset_univ _) hCard
    intro k
    apply (mem_cyclicOwnerCutPositions_iff owner k).mp
    rw [hEq]
    exact Finset.mem_univ k
  · intro hEvery
    have hEq : cyclicOwnerCutPositions owner =
        (Finset.univ : Finset (Fin n)) := by
      ext k
      simp only [mem_cyclicOwnerCutPositions_iff, Finset.mem_univ,
        iff_true]
      exact hEvery k
    calc
      cyclicOwnerChanges owner =
          (cyclicOwnerCutPositions owner).card :=
        (cyclicOwnerCutPositions_card owner).symm
      _ = n := by rw [hEq]; simp

section ActualFullCutLongFreshness

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

local notation "CoreEdge" => OldACarrierEdge A R
local notation "CoreWagon" => generatedActualASupportTrain_coreWagonEmbedding
  A hA C.toRelStructure (activeCarrier A C e.toFunctionEmbedding) R f T U
  (fun ν j p q h => Iff.mp (hRel ν j p q) h) hShared μ
local notation "Out" => attachedSelectedPictureOrderOneData
  A hA B D C family selected e R f T U hShared μ
local notation "Wit" => sharedWitnessOrderOneData U μ
  (sharedOldACarrierCoreEmbedding A C.toRelStructure
    (activeCarrier A C e.toFunctionEmbedding) R f)
  (Subtype.val : CoreEdge → Set Y)
local notation "GeomAllowed" => selectedOutputGeometricOwnerAllowed
  A hA B D C family selected e R f T U hShared μ

include hRel

/-- If every source position is an owner cut, then every genuine
long piece selected by a globally legal reduced supreme plan has a
wagon absent from ALL source connectors, not merely the cut subset. -/
theorem attachedSelectedPicture_supreme_long_wagon_fresh_of_all_source_cuts
    {n : ℕ} (K : (Out).BigCycle n)
    (owner : Fin n → I ⊕ CoreEdge)
    (hAllowed : ∀ j, GeomAllowed (K.label j) (owner j))
    (hCuts : 2 ≤ cyclicOwnerChanges owner)
    (hEveryCut : ∀ k : Fin n, owner k ≠ owner (cyclicSucc k))
    (target : Fin (cyclicOwnerChanges owner))
    (hSupreme : (attachedSelectedPicture_geometric_cutBigCycle
      A hA B D C family selected e R f T U hShared hRel μ
      K owner hAllowed hCuts).HasSupremeAt Wit target) :
    let Z := attachedSelectedPicture_geometric_cutBigCycle
      A hA B D C family selected e R f T U hShared hRel μ
      K owner hAllowed hCuts
    ∃ pieces : Fin (cyclicOwnerChanges owner) →
        TrainSupremePiece CoreEdge (Quotient (U.wagonSetoid μ)),
      Z.PlanValid Wit target pieces ∧
      Z.PlanProducesBigCycle Wit pieces ∧
      (∀ (cut : Fin (cyclicOwnerChanges owner))
        (first second : CoreEdge) (w : Quotient (U.wagonSetoid μ)),
        pieces cut = .long first w second →
        ∀ k : Fin n, K.connector k ≠ Sum.inr (CoreWagon w)) := by
  obtain ⟨pieces, hPlan, hProduces, hFresh⟩ :=
    attachedSelectedPicture_supreme_long_wagon_fresh_at_source_cuts
      A hA B D C family selected e R f T U hShared hRel μ
      K owner hAllowed hCuts target hSupreme
  refine ⟨pieces, hPlan, hProduces, ?_⟩
  intro cut first second w hp k
  have hk : k ∈ cyclicOwnerCutPositions owner :=
    (mem_cyclicOwnerCutPositions_iff owner k).mpr (hEveryCut k)
  obtain ⟨j, hj⟩ := (cyclicOwnerCutIndex_mem_iff owner k).mp hk
  simpa only [hj] using hFresh cut first second w hp j

end ActualFullCutLongFreshness
end StructuralRamsey.Girth
