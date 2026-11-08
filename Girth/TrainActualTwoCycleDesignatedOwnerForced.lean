import Girth.TrainActualGeometricDesignatedOwnerUnique
import Girth.TrainSelectedCycleGeometricOwners
import Mathlib.Tactic

set_option autoImplicit false
set_option Elab.async false

/-!
# The other owner at an original two-cycle differs from its B-standard
# WITHOUT minimality under genuine two-edge target strongness

The merged designated geometric ownership theorem identifies the
unique standard containing a genuine selected B-copy label, under
the final circulation assumptions of A-strong prescribed base
and two distinct physical A-support edges per selected B-copy.

For an ORIGINAL selected output BigCycle on TWO occurrences with
exactly TWO geometric owner changes, every index is a cut. Hence
the opposite owner is different from the designated source's
LITERAL standard index. This does not require choosing a MINIMAL
owner word: every admissible exactly-two-cut assignment qualifies.

The conclusion is the genuine lower-shadow distinction needed
to probe an old selected B-copy against the other witness
standard/core edge label. It removes the extra minimality
parameter introduced by the earlier n=2 draft #962, allowing
a direct application of the merged full-output two-cut closure
#910 once the original physical short/long transfer is complete.

This neither constructs a lower witness nor proves an output
SupremeCycleBound on its own. Circulation only; no appendix.
-/

namespace StructuralRamsey.Girth
open StructuralRamsey.RelStructure

universe u v
section ActualN2NonminimalShadow

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
variable (hShared : ∀ _i : I, Nonempty
  (SharedOldACarrierEdge A C.toRelStructure
    (activeCarrier A C e.toFunctionEmbedding)))
variable (μ : Fin (m + 1))

local notation "OldEdge" => OldACarrierEdge A C.toRelStructure
local notation "CoreEdge" => OldACarrierEdge A R
local notation "Selected" =>
  {q : DesignatedCopy B D C family // q ∈ selected}
local notation "Out" => attachedSelectedPictureOrderOneData
  A hA B D C family selected e R f T U hShared μ
local notation "GeomAllowed" => selectedOutputGeometricOwnerAllowed
  A hA B D C family selected e R f T U hShared μ

/-- Genuine designated source (i,q) has owner i, and therefore
its OTHER original position has a DIFFERENT owner when all two
positions are cuts. The owner word need NOT be minimal. -/
theorem attachedSelectedPicture_two_cycle_original_standard_diff_other_of_two_edges
    [Finite UA]
    (hBaseStrong : ∀ q : Selected,
      AStrong A D (copyCarrier q.1.base))
    (hTwoEdges : ∀ q : Selected, ∃ r s : OldEdge,
      r ≠ s ∧ r.1 ⊆ copyCarrier q.1.embedding ∧
        s.1 ⊆ copyCarrier q.1.embedding)
    (K : (Out).BigCycle 2)
    (owner : Fin 2 → I ⊕ CoreEdge)
    (hAllowed : ∀ j, GeomAllowed (K.label j) (owner j))
    (hTwo : cyclicOwnerChanges owner = 2)
    (target : Fin 2) (i : I) (q : Selected)
    (hOriginal : K.label target = Sum.inl (i, q)) :
    (Sum.inl i : I ⊕ CoreEdge) ≠ owner (cyclicSucc target) := by
  obtain ⟨j, hj⟩ :=
    attachedSelectedPicture_geometric_designated_has_standard_owner
      A hA B D C family selected e R f T U hShared μ
      K owner hAllowed target i q hOriginal
  have hij : i = j :=
    attachedSelectedPicture_designated_occurrence_owner_eq
      A hA B D C family selected e R f T U hShared μ
      hBaseStrong hTwoEdges K owner hAllowed
      target i j q hOriginal hj
  have hOwn : owner target = Sum.inl i := by
    rw [← hij] at hj
    exact hj
  have hDifferent : owner target ≠ owner (cyclicSucc target) := by
    intro heq
    have hNoCut : ∀ k : Fin 2,
        owner k = owner (cyclicSucc k) := by
      intro k
      have hk : k = target ∨ k = cyclicSucc target := by
        fin_cases target <;> fin_cases k <;> simp [cyclicSucc]
      rcases hk with hk | hk
      · subst k
        exact heq
      · subst k
        have hWrap : cyclicSucc (cyclicSucc target) = target := by
          fin_cases target <;> decide
        rw [hWrap]
        exact heq.symm
    have hZero := (cyclicOwnerChanges_eq_zero_iff owner).2 hNoCut
    omega
  intro hOther
  apply hDifferent
  calc
    owner target = Sum.inl i := hOwn
    _ = owner (cyclicSucc target) := hOther.symm

end ActualN2NonminimalShadow
end StructuralRamsey.Girth
