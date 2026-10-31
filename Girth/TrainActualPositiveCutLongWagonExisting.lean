import Girth.TrainActualSupremeCutBoundarySupport
import Girth.TrainArbitraryLongA2Geometry
import Girth.TrainCyclicOwnerAbsorption

/-!
# An actual non-singleton reduced LONG piece uses an old connector wagon

At a genuinely long reduced witness piece, the two cut connectors
are distinct vertices in the parent wagon of its two witness edges.
The core physical embedding gives actual output edges through both
ORIGINAL boundary vertices, with the same generated output wagon
label.

If the two physical cut positions are neither equal nor cyclically
adjacent, A3 of the ORIGINAL acceptable output cycle forces that
wagon to ALREADY be one of its connectors. This formalizes the
non-singleton long-segment step of the circulation argument.

The statement is deliberately conditional on nonconsecutiveness
of the original cut positions. The separate singleton/2-occurrence
cases are not assumed away, and this theorem does not construct a
legal simultaneous replacement. No appendix.
-/

namespace StructuralRamsey.Girth

universe v

namespace OrderOneData

variable {V E I P : Type v} (D : OrderOneData V E I P)

/-- Two nonadjacent vertex connectors of an acceptable big cycle
cannot both lie in one wagon unless that wagon occurs as a
literal connector of the cycle. This is the exact contrapositive
of A3, including the cyclic wrap. -/
theorem BigCycle.wagon_connector_of_nonadjacent_contacts
    {n : ℕ} (C : D.BigCycle n) (hA3 : C.A3)
    (w : P) (a b : Fin n)
    (hab : a ≠ b)
    (hba : b ≠ cyclicSucc a)
    (habSucc : a ≠ cyclicSucc b)
    (ha : C.InWagonAt w a) (hb : C.InWagonAt w b) :
    ∃ j : Fin n, C.connector j = Sum.inr w := by
  by_contra hNone
  have hFresh : ∀ t : Fin n, C.connector t ≠ Sum.inr w := by
    intro t ht
    exact hNone ⟨t, ht⟩
  obtain ⟨root, hWindow⟩ := hA3 w hFresh
  have hA := hWindow a ha
  have hB := hWindow b hb
  rcases hA with haRoot | haSucc
  · rcases hB with hbRoot | hbSucc
    · exact hab (haRoot.trans hbRoot.symm)
    · apply hba
      rw [haRoot, hbSucc]
  · rcases hB with hbRoot | hbSucc
    · apply habSucc
      rw [hbRoot, haSucc]
    · exact hab (haSucc.trans hbSucc.symm)

end OrderOneData

open StructuralRamsey.RelStructure

universe u
section ActualLongWitnessWagon

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
local notation "CoreEmb" =>
  RelStructure.Attachment.coreEmbedding C.toRelStructure S R f
local notation "CoreWagon" => generatedActualASupportTrain_coreWagonEmbedding
  A hA C.toRelStructure S R f T U
  (fun ν j p q h => Iff.mp (hRel ν j p q) h) hShared μ
local notation "CoreActual" => (fun (b : CoreEdge) =>
  actualAPictureEdgeEquiv A hA C.toRelStructure S R f
    (physicalCoreEdge (sharedOldACarrierInclusion A C.toRelStructure S) I b))
local notation "Out" => attachedSelectedPictureOrderOneData
  A hA B D C family selected e R f T U hShared μ
local notation "Wit" => sharedWitnessOrderOneData U μ
  (sharedOldACarrierCoreEmbedding A C.toRelStructure S R f)
  (Subtype.val : CoreEdge → Set Y)
local notation "GeomAllowed" => selectedOutputGeometricOwnerAllowed
  A hA B D C family selected e R f T U hShared μ

include hRel

/-- A LONG piece of the genuine positive-cut witness spanning two
nonconsecutive ORIGINAL cut positions forces its witness wagon to be
a literal GENERATED OUTPUT wagon connector of the original cycle.

Both physical endpoint contacts and the exact quotient wagon
embedding are proved from the given long witness piece. The only
geometric hypothesis not already available from LongValid is
nonconsecutiveness of the two original cut positions. -/
theorem attachedSelectedPicture_long_cut_piece_wagon_is_old_connector
    {n : ℕ} (K : (Out).BigCycle n) (hAccept : K.Acceptable)
    (owner : Fin n → I ⊕ CoreEdge)
    (hAllowed : ∀ k : Fin n, GeomAllowed (K.label k) (owner k))
    (hCuts : 2 ≤ cyclicOwnerChanges owner)
    (target cut : Fin (cyclicOwnerChanges owner))
    (first second : CoreEdge) (w : Quotient (U.wagonSetoid μ))
    (hLong : (attachedSelectedPicture_geometric_cutBigCycle
      A hA B D C family selected e R f T U hShared hRel μ
      K owner hAllowed hCuts).LongValid Wit target cut first w second)
    (a : Fin n) (b : Fin n)
    (ha : cyclicOwnerCutIndex owner (trainCyclicPred cut) = a)
    (hb : cyclicOwnerCutIndex owner cut = b)
    (hNonNext : b ≠ cyclicSucc a)
    (hNonPrev : a ≠ cyclicSucc b) :
    ∃ j : Fin n, K.connector j = Sum.inr (CoreWagon w) := by
  let Z := attachedSelectedPicture_geometric_cutBigCycle
    A hA B D C family selected e R f T U hShared hRel μ
    K owner hAllowed hCuts
  obtain ⟨x, y, hPrev, hHere, _hFirst, _hSecond,
    _hDistinct, hParentFirst, hParentSecond,
    hFirstX, hSecondY, _hNoPair⟩ := hLong
  have hMap (j : Fin (cyclicOwnerChanges owner)) :
      Sum.map CoreEmb CoreWagon (Z.connector j) =
        K.connector (cyclicOwnerCutIndex owner j) := by
    change Sum.map CoreEmb CoreWagon
      (attachedSelectedPicture_cutConnector
        A hA B D C family selected e R f T U hShared hRel μ
        K owner hAllowed j) =
        K.connector (cyclicOwnerCutIndex owner j)
    exact attachedSelectedPicture_cutConnector_eq
      A hA B D C family selected e R f T U hShared hRel μ
      K owner hAllowed j
  have hAtA : K.connector a = Sum.inl (CoreEmb x) := by
    have h := hMap (trainCyclicPred cut)
    rw [hPrev, ha] at h
    exact h.symm
  have hAtB : K.connector b = Sum.inl (CoreEmb y) := by
    have h := hMap cut
    rw [hHere, hb] at h
    exact h.symm
  have hWagonX : (Out).WagonVertex (CoreWagon w) (CoreEmb x) := by
    refine ⟨CoreActual first, ?_, ?_⟩
    · change CoreWagon ((Wit).parent first) = CoreWagon w
      exact congrArg CoreWagon hParentFirst
    · change (CoreEmb x) ∈ (CoreActual first).1
      rw [actualAPictureEdgeEquiv_core_carrier A hA C.toRelStructure S R f first]
      exact ⟨x, hFirstX, rfl⟩
  have hWagonY : (Out).WagonVertex (CoreWagon w) (CoreEmb y) := by
    refine ⟨CoreActual second, ?_, ?_⟩
    · change CoreWagon ((Wit).parent second) = CoreWagon w
      exact congrArg CoreWagon hParentSecond
    · change (CoreEmb y) ∈ (CoreActual second).1
      rw [actualAPictureEdgeEquiv_core_carrier A hA C.toRelStructure S R f second]
      exact ⟨y, hSecondY, rfl⟩
  have hSourceA : K.InWagonAt (CoreWagon w) a :=
    ⟨CoreEmb x, hAtA, hWagonX⟩
  have hSourceB : K.InWagonAt (CoreWagon w) b :=
    ⟨CoreEmb y, hAtB, hWagonY⟩
  have hDifferentCut : trainCyclicPred cut ≠ cut := by
    intro hEq
    have hBack := cyclicSucc_trainCyclicPred_of_two_le hCuts cut
    rw [hEq] at hBack
    exact (cyclicSucc_ne_self_of_two_le hCuts cut) hBack
  have hDifferent : a ≠ b := by
    intro hEq
    apply hDifferentCut
    apply (cyclicOwnerCutIndex owner).injective
    exact ha.trans (hEq.trans hb.symm)
  exact K.wagon_connector_of_nonadjacent_contacts
    Out hAccept.2.2 (CoreWagon w) a b
    hDifferent hNonNext hNonPrev hSourceA hSourceB

end ActualLongWitnessWagon
end StructuralRamsey.Girth
