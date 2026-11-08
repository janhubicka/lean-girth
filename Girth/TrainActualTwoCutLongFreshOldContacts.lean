import Girth.TrainCyclicTwoCutTwoStepComplement
import Girth.TrainWagonTwoContactFreshOldDichotomy
import Girth.TrainActualChosenTwoStepLong
import Mathlib.Tactic

set_option autoImplicit false
set_option Elab.async false

/-!
# Path A: ACTUAL two-cut reduced long gives fresh or old SOURCE wagon geometry

A genuine reduced LongValid piece at a physical cut of an acceptable
selected attached-output BigCycle has two actual core support edges,
one incident at each ORIGINAL owner-cut boundary connector. Both
edges have the same actual image wagon. Existing checked selected
physical incidence lifts identify those two original cut connectors
as distinct vertex contacts in that same physical wagon.

The source's actual A2/A3 therefore supplies an exhaustive split:
  * the physical wagon is fresh against ALL original connectors,
    and the two original cut positions are cyclically adjacent;
  * or the wagon already occurs at original position t, and the
    original cut positions are pred(t),succ(t) in one orientation.

The statement retains exact physical quotient wagon provenance and
both source indexed cut positions; it does not manufacture an
original source designated B-copy identity or claim either final
physical replacement. This is the precise source classification
needed for the two-cut nonedge LONG branch. No appendix or TeX.
-/

namespace StructuralRamsey.Girth
open StructuralRamsey.RelStructure

universe u v
section ActualTwoCutLongContacts

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
local notation "CoreWagon" => generatedActualASupportTrain_coreWagonEmbedding
  A hA C.toRelStructure S R f T U
  (fun ν j p q h => Iff.mp (hRel ν j p q) h) hShared μ

include hRel

/-- The physical image wagon of ANY genuine reduced two-cut LongValid
piece either is fresh and its ORIGINAL cut contacts are cyclically
adjacent, or is a real old source wagon with the two cut positions
straddling its occurrence. This is actual source A2/A3, not reduced
witness A2/A3. -/
theorem attachedSelectedPicture_two_cut_long_fresh_or_old_straddle
    {n : ℕ} (K : (Out).BigCycle n)
    (hAccept : K.Acceptable)
    (owner : Fin n → I ⊕ CoreEdge)
    (hAllowed : ∀ j, GeomAllowed (K.label j) (owner j))
    (hTwo : cyclicOwnerChanges owner = 2)
    (target cut : Fin (cyclicOwnerChanges owner))
    (first second : CoreEdge) (w : Quotient (U.wagonSetoid μ))
    (hLong : (attachedSelectedPicture_geometric_cutBigCycle
      A hA B D C family selected e R f T U hShared hRel μ
      K owner hAllowed (by omega)).LongValid Wit target cut
      first w second) :
    ((∀ t : Fin n, K.connector t ≠ Sum.inr (CoreWagon w)) ∧
      (cyclicOwnerCutIndex owner cut =
          cyclicSucc (cyclicOwnerCutIndex owner (trainCyclicPred cut)) ∨
       cyclicOwnerCutIndex owner (trainCyclicPred cut) =
          cyclicSucc (cyclicOwnerCutIndex owner cut))) ∨
    (∃ t : Fin n, K.connector t = Sum.inr (CoreWagon w) ∧
      ((cyclicOwnerCutIndex owner (trainCyclicPred cut) =
          trainCyclicPred t ∧
        cyclicOwnerCutIndex owner cut = cyclicSucc t) ∨
       (cyclicOwnerCutIndex owner (trainCyclicPred cut) =
          cyclicSucc t ∧
        cyclicOwnerCutIndex owner cut = trainCyclicPred t))) := by
  have hCuts : 2 ≤ cyclicOwnerChanges owner := by omega
  have hDifferentCut : trainCyclicPred cut ≠ cut := by
    intro hEq
    have hBack := cyclicSucc_trainCyclicPred_of_two_le hCuts cut
    rw [hEq] at hBack
    exact (cyclicSucc_ne_self_of_two_le hCuts cut) hBack
  have hDistinctOriginal :
      cyclicOwnerCutIndex owner (trainCyclicPred cut) ≠
        cyclicOwnerCutIndex owner cut := by
    intro hEq
    exact hDifferentCut ((cyclicOwnerCutIndex owner).injective hEq)
  obtain ⟨hContactA, hContactB⟩ :=
    attachedSelectedPicture_long_cut_piece_actual_source_contacts
      A hA B D C family selected e R f T U hShared hRel μ
      K owner hAllowed hCuts target cut first second w hLong
  exact K.two_wagon_contacts_fresh_adjacent_or_old_straddle
    Out hAccept (CoreWagon w)
      (cyclicOwnerCutIndex owner (trainCyclicPred cut))
      (cyclicOwnerCutIndex owner cut)
      hDistinctOriginal hContactA hContactB


/-- The old-wagon side of an actual reduced LongValid piece
has a CANONICAL two-step original owner run. With exactly two
cuts the physical wagon at t cannot be a cut (both cut
connectors are real vertices), and the verified cyclic-gap
enumerator chooses the forward-oriented two-step run.

Every other original source occurrence is geometrically owned
by the opposite reduced cut. The new wagon-fresh side remains
an exact adjacent-contact alternative, not an inferred
supreme-plan replacement. -/
theorem attachedSelectedPicture_two_cut_long_fresh_or_old_oriented
    {n : ℕ} (K : (Out).BigCycle n)
    (hAccept : K.Acceptable) (hn : 3 ≤ n)
    (owner : Fin n → I ⊕ CoreEdge)
    (hAllowed : ∀ j, GeomAllowed (K.label j) (owner j))
    (hTwo : cyclicOwnerChanges owner = 2)
    (target cut : Fin (cyclicOwnerChanges owner))
    (first second : CoreEdge) (w : Quotient (U.wagonSetoid μ))
    (hLong : (attachedSelectedPicture_geometric_cutBigCycle
      A hA B D C family selected e R f T U hShared hRel μ
      K owner hAllowed (by omega)).LongValid Wit target cut
      first w second) :
    ((∀ t : Fin n, K.connector t ≠ Sum.inr (CoreWagon w)) ∧
      (cyclicOwnerCutIndex owner cut =
          cyclicSucc (cyclicOwnerCutIndex owner (trainCyclicPred cut)) ∨
       cyclicOwnerCutIndex owner (trainCyclicPred cut) =
          cyclicSucc (cyclicOwnerCutIndex owner cut))) ∨
    (∃ t : Fin n, K.connector t = Sum.inr (CoreWagon w) ∧
      ∃ j : Fin (cyclicOwnerChanges owner),
        cyclicOwnerCutIndex owner j = cyclicSucc t ∧
        cyclicOwnerCutIndex owner (trainCyclicPred j) =
          trainCyclicPred t ∧
        ∀ x : Fin n, x ≠ t → x ≠ cyclicSucc t →
          owner x =
            owner (cyclicOwnerCutIndex owner (trainCyclicPred j))) := by
  rcases attachedSelectedPicture_two_cut_long_fresh_or_old_straddle
      A hA B D C family selected e R f T U hShared hRel μ
      K hAccept owner hAllowed hTwo target cut first second w hLong
      with hFresh | hOldCase
  · exact Or.inl hFresh
  · obtain ⟨t, hOld, hStraddle⟩ := hOldCase
    have hCuts : 2 ≤ cyclicOwnerChanges owner := by omega
    obtain ⟨hContactA, hContactB⟩ :=
      attachedSelectedPicture_long_cut_piece_actual_source_contacts
        A hA B D C family selected e R f T U hShared hRel μ
        K owner hAllowed hCuts target cut first second w hLong
    have hUncut : t ∉ cyclicOwnerCutPositions owner :=
      K.old_wagon_at_two_vertex_cuts_is_uncut
        Out owner hTwo cut (CoreWagon w)
        hContactA hContactB t hOld
    have hNeighborCuts :
        trainCyclicPred t ∈ cyclicOwnerCutPositions owner ∧
        cyclicSucc t ∈ cyclicOwnerCutPositions owner := by
      rcases hStraddle with ⟨hPrev, hNext⟩ |
        ⟨hNext, hPrev⟩
      · exact ⟨
          (cyclicOwnerCutIndex_mem_iff owner (trainCyclicPred t)).mpr
            ⟨trainCyclicPred cut, hPrev⟩,
          (cyclicOwnerCutIndex_mem_iff owner (cyclicSucc t)).mpr
            ⟨cut, hNext⟩⟩
      · exact ⟨
          (cyclicOwnerCutIndex_mem_iff owner (trainCyclicPred t)).mpr
            ⟨cut, hPrev⟩,
          (cyclicOwnerCutIndex_mem_iff owner (cyclicSucc t)).mpr
            ⟨trainCyclicPred cut, hNext⟩⟩
    obtain ⟨j, hHere, hPrev, hComplement⟩ :=
      cyclicOwner_two_cut_old_wagon_oriented_run
        owner hn hTwo t hNeighborCuts.1 hNeighborCuts.2 hUncut
    exact Or.inr ⟨t, hOld, j, hHere, hPrev, hComplement⟩

end ActualTwoCutLongContacts
end StructuralRamsey.Girth
