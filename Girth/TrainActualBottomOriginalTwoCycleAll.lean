import Girth.TrainActualBottomOriginalTwoCycleCore
import Girth.TrainActualZeroCutGlobalSupreme
import Mathlib.Tactic

set_option autoImplicit false
set_option Elab.async false

/-!
# Complete original source length-two bottom preservation

The actual n=2 cycle has a minimum GEOMETRIC owner word. Either
there are NO cuts, in which case the existing checked one-standard
old-picture transfer applies, or there is a cut, in which case the
two owners differ and their ORIGINAL label pieces have an allowed
core intersection, giving an ORIGINAL B-labelled global supreme plan.
No lower witness full-system-girth or even local forest premise
is used in this n=2 case.

The old selected-copy bound remains an explicit hypothesis for the
zero-cut case, and all original physical labels are retained.
-/

namespace StructuralRamsey.Girth
open StructuralRamsey.RelStructure

universe u v

/-- In a two-position cyclic word, any positive number of owner
changes implies that the two owner values differ, including the
closing boundary. No finiteness hypothesis on the owner type. -/
theorem two_cyclic_owner_changes_pos_implies_distinct
    {Owner : Type v} (owner : Fin 2 → Owner)
    (hPos : 0 < cyclicOwnerChanges owner) :
    owner 0 ≠ owner 1 := by
  intro hEq
  have hAll : ∀ j : Fin 2,
      owner j = owner (cyclicSucc j) := by
    intro j
    fin_cases j
    · simpa [cyclicSucc] using hEq
    · simpa [cyclicSucc] using hEq.symm
  have hZero := (cyclicOwnerChanges_eq_zero_iff owner).2 hAll
  omega

section OriginalTwoBottomAll

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
variable (hShared : ∀ _i : I, Nonempty
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

local notation "S" => activeCarrier A C e.toFunctionEmbedding
local notation "Actual" => RelStructure.Attachment.attach C.toRelStructure S R f
local notation "CoreEdge" => OldACarrierEdge A R
local notation "Selected" => {q : DesignatedCopy B D C family // q ∈ selected}
local notation "μBottom" => (⟨0, Nat.zero_lt_succ m⟩ : Fin (m + 1))
local notation "Old" => selectedPictureOrderOneData
  A B D C family selected T μBottom
local notation "Out" => attachedSelectedPictureOrderOneData
  A hA B D C family selected e R f T U hShared μBottom
local notation "GeomAllowed" => selectedOutputGeometricOwnerAllowed
  A hA B D C family selected e R f T U hShared μBottom

include hRel

/-- ALL genuine original output cycles with exactly two occurrences
have globally supreme ORIGINAL selected B-labels at the bottom cut.
The two-owner case uses only physical free-attachment geometry; the
one-owner case uses the existing old selected picture bound. -/
theorem attachedSelectedPicture_bottom_two_cycle_supreme
    [Finite UA] [Nontrivial UA]
    (hPhysical : ALinear A Actual)
    (hStrong : ∀ b : RelStructure.Embedding B D, b ∈ family →
      AStrong A D (copyCarrier b))
    (hTwoCopies : ∀ r : Selected,
      ∃ a b : OldACarrierEdge A C.toRelStructure,
        a ≠ b ∧ a.1 ⊆ copyCarrier r.1.embedding ∧
          b.1 ⊆ copyCarrier r.1.embedding)
    (hOldStrong : AStrong A C.toRelStructure S)
    (hCoreStrong : ∀ j : I, AStrong A R (copyCarrier (f j)))
    (q : ℕ) (hOldSupreme : (Old).SupremeCycleBound q)
    (K : (Out).BigCycle 2) (hAccept : K.Acceptable)
    (hOrder : K.twiceOrder ≤ 2 * q) :
    K.HasSimultaneousSupreme := by
  obtain ⟨owner, hAllowed, _hMin⟩ :=
    attachedSelectedPicture_cycle_exists_minimal_geometric_owners
      A hA B D C family selected e R f T U hShared μBottom K
  by_cases hZero : cyclicOwnerChanges owner = 0
  · exact attachedSelectedPicture_zero_cut_supreme_of_old_bound
      A hA B D C family selected e R f T U hShared hRel μBottom
      hStrong hTwoCopies hOldStrong hCoreStrong
      K hAccept hOldSupreme hOrder owner hAllowed hZero
  · have hDistinct : owner 0 ≠ owner 1 :=
      two_cyclic_owner_changes_pos_implies_distinct
        owner (Nat.pos_of_ne_zero hZero)
    exact attachedSelectedPicture_bottom_two_cycle_distinct_owner_supreme
      A hA B D C family selected e R f T U hShared
      hPhysical hOldStrong (fun r => hStrong r.1.base r.1.base_mem)
      K owner hAllowed hDistinct

end OriginalTwoBottomAll
end StructuralRamsey.Girth
