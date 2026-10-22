import Girth.TrainCyclicOwnerFourCases
import Mathlib.Data.Finset.Sort

/-!
# Circulation: enumerate all genuine cyclic owner boundaries

The verified owner minimizer yields a concrete finite set of
positions immediately BEFORE an owner change. This file turns that
Finset into a canonical increasing Fin-indexed list, using the
standard Finset order embedding. The index length is EXACTLY the
number of cyclic changes, and its image is EXACTLY the cut set,
including the last-to-first wrap position if it is a cut.

This is the indexing input for maximal owner runs, NOT a proof that
owners are constant between successive indexed cuts, nor a
construction of the legal witness BigCycle or A1--A3.
No appendix result is used.
-/

namespace StructuralRamsey.Girth

universe v

variable {Owner : Type v} {n : ℕ}

/-- Canonical increasing enumeration of ALL cyclic owner cut positions.
The empty cut set gives an empty domain Fin 0. -/
noncomputable def cyclicOwnerCutIndex (owner : Fin n → Owner) :
    Fin (cyclicOwnerChanges owner) ↪o Fin n :=
  (cyclicOwnerCutPositions owner).orderEmbOfFin
    (cyclicOwnerCutPositions_card owner)

/-- Every finite cut position appears exactly once in this enumeration:
there are no spurious positions and no lost cyclic wrap boundary. -/
theorem cyclicOwnerCutIndex_image (owner : Fin n → Owner) :
    Finset.image (cyclicOwnerCutIndex owner)
        (Finset.univ : Finset (Fin (cyclicOwnerChanges owner))) =
      cyclicOwnerCutPositions owner := by
  classical
  unfold cyclicOwnerCutIndex
  exact Finset.image_orderEmbOfFin_univ
    (cyclicOwnerCutPositions owner)
    (cyclicOwnerCutPositions_card owner)

/-- Exact membership criterion for the indexed cyclic cut positions. -/
theorem cyclicOwnerCutIndex_mem_iff (owner : Fin n → Owner) (k : Fin n) :
    k ∈ cyclicOwnerCutPositions owner ↔
      ∃ j : Fin (cyclicOwnerChanges owner),
        cyclicOwnerCutIndex owner j = k := by
  classical
  rw [← cyclicOwnerCutIndex_image owner]
  constructor
  · intro h
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp h
    exact ⟨j, hj⟩
  · rintro ⟨j, hj⟩
    exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, hj⟩

/-- Every enumerated position is a GENUINE owner change. -/
theorem cyclicOwnerCutIndex_is_change (owner : Fin n → Owner)
    (j : Fin (cyclicOwnerChanges owner)) :
    owner (cyclicOwnerCutIndex owner j) ≠
      owner (cyclicSucc (cyclicOwnerCutIndex owner j)) := by
  apply (mem_cyclicOwnerCutPositions_iff owner _).mp
  exact (cyclicOwnerCutIndex_mem_iff owner _).mpr ⟨j, rfl⟩

/-- The indexed cut sequence is strictly increasing in the ambient
Fin order; its successor is not YET identified with the cyclic
next owner-run boundary, including wrap. -/
theorem cyclicOwnerCutIndex_strictMono (owner : Fin n → Owner) :
    StrictMono (cyclicOwnerCutIndex owner) :=
  (cyclicOwnerCutIndex owner).strictMono

end StructuralRamsey.Girth
