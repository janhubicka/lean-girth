import Girth.TrainCyclicTwoCutSingletonComplement
import Girth.TrainActualCoreSingletonConsecutiveCuts
import Girth.TrainShortReplacementNeighbour
import Mathlib.Tactic

set_option autoImplicit false
set_option Elab.async false

/-!
# Path A: a two-cut selected cycle of length at least three has a standard owner

Any occurrence geometrically owned by a physical core A-edge is
ISOLATED: its immediate predecessor and successor owners must differ.
At EXACTLY TWO cyclic owner changes there can be at most one such
isolated occurrence when n>=3. This is a pure cyclic consequence
of the existing singleton-run complement theorem.

Consequently an actual selected cycle of length at least three
whose geometric owner word has exactly two cuts MUST have at
least one genuine designated gluing STANDARD owner. In particular
the residual two-cut reduced witness cannot have both labels
physical core A-edges. This removes the completely edge-only
case from the positive-cut source-length>=3 analysis, without
assuming any witness supreme plan, a synthetic original B-label,
or a restricted physical support system. No appendix or TeX.
-/

namespace StructuralRamsey.Girth

universe v

/-- With only TWO cyclic owner changes, two distinct source
positions cannot both be isolated from their predecessor and
successor owners, provided the source has at least three positions. -/
theorem cyclicOwner_two_cut_isolated_unique
    {Owner : Type v} {n : ℕ}
    (owner : Fin n → Owner)
    (hn : 3 ≤ n)
    (hTwo : cyclicOwnerChanges owner = 2)
    (p q : Fin n)
    (hpBefore : owner (trainCyclicPred p) ≠ owner p)
    (hpAfter : owner p ≠ owner (cyclicSucc p))
    (hqBefore : owner (trainCyclicPred q) ≠ owner q)
    (hqAfter : owner q ≠ owner (cyclicSucc q)) :
    p = q := by
  have hCutBefore :
      trainCyclicPred p ∈ cyclicOwnerCutPositions owner := by
    apply (mem_cyclicOwnerCutPositions_iff owner _).mpr
    simpa only [cyclicSucc_trainCyclicPred_of_two_le
      (by omega : 2 ≤ n) p] using hpBefore
  have hCutAfter : p ∈ cyclicOwnerCutPositions owner :=
    (mem_cyclicOwnerCutPositions_iff owner p).mpr hpAfter
  obtain ⟨j, hThis, hPrev⟩ :=
    cyclicOwnerCutIndex_pred_of_adjacent_cuts
      owner (by omega : 2 ≤ n) p hCutBefore hCutAfter
  have hForward : cyclicOwnerCutIndex owner j =
      cyclicSucc (cyclicOwnerCutIndex owner (trainCyclicPred j)) := by
    rw [hThis, hPrev]
    exact (cyclicSucc_trainCyclicPred_of_two_le
      (by omega : 2 ≤ n) p).symm
  have hOther (x : Fin n) (hx : x ≠ p) :
      owner x = owner
        (cyclicOwnerCutIndex owner (trainCyclicPred j)) := by
    apply cyclicOwner_two_cut_singleton_complement_owner
      owner (by omega : 2 ≤ n) hTwo j hForward x
    simpa only [hThis] using hx
  by_contra hpq
  have hQ := hOther q hpq.symm
  by_cases hPred : trainCyclicPred q = p
  · have hSucc : cyclicSucc q ≠ p := by
      intro hh
      exact (trainCyclicPred_ne_cyclicSucc_of_three_le hn q)
        (hPred.trans hh.symm)
    have hQSuc := hOther (cyclicSucc q) hSucc
    exact hqAfter (hQ.trans hQSuc.symm)
  · have hQPred := hOther (trainCyclicPred q) hPred
    exact hqBefore (hQPred.trans hQ.symm)

open StructuralRamsey.RelStructure

universe u
section ActualTwoCutCoreOwnerUniqueness

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
variable (μ : Fin (m + 1))

local notation "CoreEdge" => OldACarrierEdge A R
local notation "Out" => attachedSelectedPictureOrderOneData
  A hA B D C family selected e R f T U hShared μ
local notation "GeomAllowed" => selectedOutputGeometricOwnerAllowed
  A hA B D C family selected e R f T U hShared μ


/-- Two separate physical CORE-EDGE-owned occurrences cannot both
occur in an acceptable selected source cycle of length>=3 with
exactly two geometric owner cuts. Both would be isolated, contrary
to the pure finite two-cut lemma. -/
theorem attachedSelectedPicture_two_cut_core_owner_unique
    {n : ℕ} (K : (Out).BigCycle n)
    (hn : 3 ≤ n)
    (owner : Fin n → I ⊕ CoreEdge)
    (hAllowed : ∀ k, GeomAllowed (K.label k) (owner k))
    (hTwo : cyclicOwnerChanges owner = 2)
    (p q : Fin n) (bp bq : CoreEdge)
    (hp : owner p = Sum.inr bp)
    (hq : owner q = Sum.inr bq) :
    p = q := by
  obtain ⟨hpBefore, hpAfter⟩ :=
    attachedSelectedPicture_geometric_core_owner_isolated
      A hA B D C family selected e R f T U hShared μ
      K owner hAllowed p bp hp
  obtain ⟨hqBefore, hqAfter⟩ :=
    attachedSelectedPicture_geometric_core_owner_isolated
      A hA B D C family selected e R f T U hShared μ
      K owner hAllowed q bq hq
  exact cyclicOwner_two_cut_isolated_unique owner hn hTwo p q
    (by rw [hp]; exact hpBefore)
    (by rw [hp]; exact hpAfter.symm)
    (by rw [hq]; exact hqBefore)
    (by rw [hq]; exact hqAfter.symm)

/-- The exactly-two-owner-cut reduced witness at source length>=3
has a genuine designated STANDARD owner: otherwise every original
position would have to be core-edge-owned, but two distinct such
positions are impossible by the preceding theorem. -/
theorem attachedSelectedPicture_two_cut_has_standard_owner
    {n : ℕ} (K : (Out).BigCycle n)
    (hn : 3 ≤ n)
    (owner : Fin n → I ⊕ CoreEdge)
    (hAllowed : ∀ k, GeomAllowed (K.label k) (owner k))
    (hTwo : cyclicOwnerChanges owner = 2) :
    ∃ k : Fin n, ∃ i : I, owner k = Sum.inl i := by
  by_contra h
  have hAllCore : ∀ k : Fin n, ∃ b : CoreEdge,
      owner k = Sum.inr b := by
    intro k
    cases ho : owner k with
    | inl i =>
        exact (h ⟨k, i, ho⟩).elim
    | inr b =>
        exact ⟨b, ho⟩
  let p : Fin n := ⟨0, by omega⟩
  let q : Fin n := ⟨1, by omega⟩
  have hpq : p ≠ q := by
    intro hh
    have hv := congrArg Fin.val hh
    simp [p, q] at hv
  obtain ⟨bp, hp⟩ := hAllCore p
  obtain ⟨bq, hq⟩ := hAllCore q
  exact hpq (attachedSelectedPicture_two_cut_core_owner_unique
    A hA B D C family selected e R f T U hShared μ
    K hn owner hAllowed hTwo p q bp bq hp hq)

end ActualTwoCutCoreOwnerUniqueness
end StructuralRamsey.Girth
