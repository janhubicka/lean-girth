import Girth.TrainSelectedCycleGeometricOwners
import Girth.TrainActualCycleDesignatedRank
import Girth.TrainDesignatedLabelLexRank

set_option autoImplicit false
set_option Elab.async false

/-!
# Canonical rank of an actual selected output cycle

The final positive-cut argument compares the minimum number of
GEOMETRIC cyclic owner changes, not the number for an arbitrarily
chosen literal source-label assignment. The existing selected-cycle
minimizer proves this minimum is attained, even for infinite owner
types and for foreign designated labels within one standard.

We package that minimum as a number independent of the choice of
minimizing assignment, pair it with the already verified exact
designated-occurrence count, and transport any proved lexicographic
decrease between minimizing owners to the resulting canonical
cycle rank. This is the precise rank required for the final
well-founded induction, with no extra geometric rank hypothesis.

No output cycle or rank-decreasing move is constructed here; the
positive-cut short/long/bridge alternatives still need to supply
them. No appendix.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v

section ActualSelectedOutputRank

variable {L : RelLanguage.{u}} {UA VB P X Y I : Type v}
variable (A : RelStructure L UA) (hA : A.Irreducible)
variable (B : RelStructure L VB) (D : RelStructure L P)
variable (C : StructuralRamsey.Partite.System L P X)
variable (family : Set (Embedding B D))
variable (selected : Set (DesignatedCopy B D C family))
variable (e : Embedding A D) (R : RelStructure L Y)
variable (f : I → Embedding
  (C.toRelStructure.induce (activeCarrier A C e.toFunctionEmbedding)) R)
variable {m : ℕ}
variable (T : EdgeTrainLevels (OldACarrierEdge A C.toRelStructure) m)
variable (U : EdgeTrainLevels (OldACarrierEdge A R) m)
variable (hShared : ∀ _i : I,
  Nonempty (SharedOldACarrierEdge A C.toRelStructure
    (activeCarrier A C e.toFunctionEmbedding)))
variable (μ : Fin (m + 1))

local notation "CoreEdge" => OldACarrierEdge A R
local notation "Out" => attachedSelectedPictureOrderOneData
  A hA B D C family selected e R f T U hShared μ
local notation "GeomAllowed" => selectedOutputGeometricOwnerAllowed
  A hA B D C family selected e R f T U hShared μ

/-- Least number of cyclic changes among all actual geometric
standard/core-edge owners of the given literal output BigCycle. -/
noncomputable def attachedSelectedPicture_minGeometricCuts
    {n : ℕ} (K : (Out).BigCycle n) : ℕ :=
  cyclicOwnerChanges (Classical.choose
    (attachedSelectedPicture_cycle_exists_minimal_geometric_owners
      A hA B D C family selected e R f T U hShared μ K))

/-- An arbitrary admissible geometric assignment cannot have fewer
changes than the true minimum. -/
theorem attachedSelectedPicture_minGeometricCuts_le
    {n : ℕ} (K : (Out).BigCycle n)
    (owner : Fin n → I ⊕ CoreEdge)
    (hAllowed : ∀ j, GeomAllowed (K.label j) (owner j)) :
    attachedSelectedPicture_minGeometricCuts
      A hA B D C family selected e R f T U hShared μ K ≤
      cyclicOwnerChanges owner := by
  classical
  unfold attachedSelectedPicture_minGeometricCuts
  exact (Classical.choose_spec
    (attachedSelectedPicture_cycle_exists_minimal_geometric_owners
      A hA B D C family selected e R f T U hShared μ K)).2
    owner hAllowed

/-- Every admitted *minimizing* geometric owner assignment has
exactly the canonical minimum number of changes. This makes the
cycle rank independent of the arbitrary minimizer's labels. -/
theorem attachedSelectedPicture_minGeometricCuts_eq_of_minimal
    {n : ℕ} (K : (Out).BigCycle n)
    (owner : Fin n → I ⊕ CoreEdge)
    (hAllowed : ∀ j, GeomAllowed (K.label j) (owner j))
    (hMinimal : ∀ other : Fin n → I ⊕ CoreEdge,
      (∀ j, GeomAllowed (K.label j) (other j)) →
      cyclicOwnerChanges owner ≤ cyclicOwnerChanges other) :
    attachedSelectedPicture_minGeometricCuts
      A hA B D C family selected e R f T U hShared μ K =
      cyclicOwnerChanges owner := by
  classical
  apply Nat.le_antisymm
  · exact attachedSelectedPicture_minGeometricCuts_le
      A hA B D C family selected e R f T U hShared μ
      K owner hAllowed
  · unfold attachedSelectedPicture_minGeometricCuts
    exact hMinimal (Classical.choose
      (attachedSelectedPicture_cycle_exists_minimal_geometric_owners
        A hA B D C family selected e R f T U hShared μ K))
      (Classical.choose_spec
        (attachedSelectedPicture_cycle_exists_minimal_geometric_owners
          A hA B D C family selected e R f T U hShared μ K)).1

/-- Actual output-cycle lexicographic rank: minimum geometric owner
cuts and number of designated literal occurrences. The second
coordinate is NOT the number of distinct designated labels. -/
noncomputable def attachedSelectedPicture_geometricLexRank
    {n : ℕ} (K : (Out).BigCycle n) : ℕ × ℕ :=
  (attachedSelectedPicture_minGeometricCuts
    A hA B D C family selected e R f T U hShared μ K,
   K.designatedOccurrenceCount Out)

/-- Evaluate the canonical cycle rank from any genuine minimal
geometric assignment; no choice of designated source is needed. -/
theorem attachedSelectedPicture_geometricLexRank_eq_of_minimal
    {n : ℕ} (K : (Out).BigCycle n)
    (owner : Fin n → I ⊕ CoreEdge)
    (hAllowed : ∀ j, GeomAllowed (K.label j) (owner j))
    (hMinimal : ∀ other : Fin n → I ⊕ CoreEdge,
      (∀ j, GeomAllowed (K.label j) (other j)) →
      cyclicOwnerChanges owner ≤ cyclicOwnerChanges other) :
    attachedSelectedPicture_geometricLexRank
      A hA B D C family selected e R f T U hShared μ K =
    (cyclicOwnerChanges owner, K.designatedOccurrenceCount Out) := by
  apply Prod.ext
  · exact attachedSelectedPicture_minGeometricCuts_eq_of_minimal
      A hA B D C family selected e R f T U hShared μ
      K owner hAllowed hMinimal
  · rfl

/-- A REAL lex-rank drop between minimizing geometric owner
assignments is precisely a strict drop of the intrinsic cycle rank.
The lengths of the two physical BigCycles may differ. -/
theorem attachedSelectedPicture_geometricLexRank_drop
    {n k : ℕ} (K : (Out).BigCycle n) (H : (Out).BigCycle k)
    (owner : Fin n → I ⊕ CoreEdge)
    (hAllowed : ∀ j, GeomAllowed (K.label j) (owner j))
    (hMinimal : ∀ other : Fin n → I ⊕ CoreEdge,
      (∀ j, GeomAllowed (K.label j) (other j)) →
      cyclicOwnerChanges owner ≤ cyclicOwnerChanges other)
    (newOwner : Fin k → I ⊕ CoreEdge)
    (hNewAllowed : ∀ j, GeomAllowed (H.label j) (newOwner j))
    (hNewMinimal : ∀ other : Fin k → I ⊕ CoreEdge,
      (∀ j, GeomAllowed (H.label j) (other j)) →
      cyclicOwnerChanges newOwner ≤ cyclicOwnerChanges other)
    (hDrop : Prod.Lex (· < ·) (· < ·)
      (cyclicOwnerChanges newOwner, H.designatedOccurrenceCount Out)
      (cyclicOwnerChanges owner, K.designatedOccurrenceCount Out)) :
    Prod.Lex (· < ·) (· < ·)
      (attachedSelectedPicture_geometricLexRank
        A hA B D C family selected e R f T U hShared μ H)
      (attachedSelectedPicture_geometricLexRank
        A hA B D C family selected e R f T U hShared μ K) := by
  rw [attachedSelectedPicture_geometricLexRank_eq_of_minimal
    A hA B D C family selected e R f T U hShared μ
      H newOwner hNewAllowed hNewMinimal]
  rw [attachedSelectedPicture_geometricLexRank_eq_of_minimal
    A hA B D C family selected e R f T U hShared μ
      K owner hAllowed hMinimal]
  exact hDrop

end ActualSelectedOutputRank

end StructuralRamsey.Girth
