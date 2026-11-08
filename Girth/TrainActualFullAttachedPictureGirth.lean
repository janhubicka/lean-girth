import Girth.TrainActualTwoCutSourceTwoComplete
import Girth.TrainActualTwoCutThreeLeFullSupreme
import Mathlib.Tactic

set_option autoImplicit false
set_option Elab.async false

/-!
# Path A: complete original selected-picture attached FULL system girth

This is the final circulation picture-step composition: given true old
SupremeCycleBound at cutoff q, true lower shared-witness FullSystemGirthGT
at the SAME cutoff q, real output LinearPretrain, source B-strongness,
two old A-support edges per selected source copy, and genuine old/core
gluing-image AStrongness, the attached selected output has the FULL
global simultaneous-supreme FullSystemGirthGT at cutoff q.

The proof uses an ACTUAL minimum geometric owner assignment, not an
arbitrary owner assignment. The zero-cut and >=3-cut source branches
were previously merged. For exactly two owner cuts:

* original length two: an exhaustive proof uses true original
  designated labels, pair/non-pair two-vertex local physical transfers,
  exact mixed vertex/wagon old shared edge and wagon class reflection,
  and lower-witness exclusion of double wagons;
* original length >=3: the independent already drafted physical
  two-standard/standard-core and fresh/old wagon source transfer.

No original B-label is identified with its chosen geometric owner.
No source cycle is falsely pulled back through one standard.
No Hales-Jewett power is presumed high-girth, no A-edge pruning,
no new abstract picture-compatibility axiom, and no appendix proof.

This file is an UNVERIFIED integration of unmerged Path A proof
branches, not a validation marker. Lean + strict no-sorry/axiom CI,
regressions and adversarial audit are required before circulation.
-/

namespace StructuralRamsey.Girth
open StructuralRamsey.RelStructure

universe u v
section FullAttachedSelectedPictureGirth

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
variable (hShared : ∀ j : I, Nonempty
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
local notation "Selected" =>
  {q : DesignatedCopy B D C family // q ∈ selected}
local notation "OldEdge" => OldACarrierEdge A C.toRelStructure
local notation "Old" => selectedPictureOrderOneData
  A B D C family selected T μ
local notation "Out" => attachedSelectedPictureOrderOneData
  A hA B D C family selected e R f T U hShared μ
local notation "CoreEdge" => OldACarrierEdge A R
local notation "Wit" => sharedWitnessOrderOneData U μ
  (sharedOldACarrierCoreEmbedding A C.toRelStructure S R f)
  (Subtype.val : CoreEdge → Set Y)
local notation "GeomAllowed" => selectedOutputGeometricOwnerAllowed
  A hA B D C family selected e R f T U hShared μ

include hRel

/-- Full attached original selected-picture system girth under ONLY
the real old/lower witness and standard physical geometry hypotheses,
including global legal simultaneous replacement plans. This depends
on the separately formalized source n=2 and n>=3 two-cut branches;
it assumes no replacement-existence callback. -/
theorem attachedSelectedPicture_fullSystemGirthGT_of_old_and_witness
    [Finite UA]
    (qcut : ℕ) (hq : 1 ≤ qcut)
    (hLinear : (Out).LinearPretrain)
    (hStrong : ∀ r : RelStructure.Embedding B D, r ∈ family →
      AStrong A D (copyCarrier r))
    (hTwoCopies : ∀ r : Selected, ∃ a b : OldEdge,
      a ≠ b ∧ a.1 ⊆ copyCarrier r.1.embedding ∧
        b.1 ⊆ copyCarrier r.1.embedding)
    (hOldStrong : AStrong A C.toRelStructure S)
    (hCoreStrong : ∀ j : I, AStrong A R (copyCarrier (f j)))
    (hOldSupreme : (Old).SupremeCycleBound qcut)
    (hWitness : (Wit).FullSystemGirthGT qcut) :
    (Out).FullSystemGirthGT qcut := by
  apply attachedSelectedPicture_fullSystemGirth_of_three_le_two_cut
    A hA B D C family selected e R f T U hShared hRel μ
    qcut hq hLinear hStrong hTwoCopies hOldStrong hCoreStrong
    hOldSupreme hWitness
  intro n K hn hAccept owner hAllowed _hMinimal hTwo hOrder
  exact attachedSelectedPicture_two_cut_three_le_full_supreme
    A hA B D C family selected e R f T U hShared hRel μ
    hStrong hTwoCopies hOldStrong hCoreStrong
    K hAccept hLinear hn hOrder
    owner hAllowed hTwo hWitness hOldSupreme

end FullAttachedSelectedPictureGirth
end StructuralRamsey.Girth
