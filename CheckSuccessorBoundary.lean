import Girth

#print axioms StructuralRamsey.Girth.SameMarkedKernel.refl
#print axioms StructuralRamsey.Girth.SameMarkedKernel.symm
#print axioms StructuralRamsey.Girth.SameMarkedKernel.trans
#print axioms StructuralRamsey.Girth.SameMarkedKernel.of_injective
#print axioms StructuralRamsey.Girth.SameMarkedKernel.image_subset_iff
#print axioms StructuralRamsey.Girth.SameMarkedKernel.image_eq_iff
#print axioms StructuralRamsey.Girth.SameMarkedKernel.carrier_injective_iff
#print axioms StructuralRamsey.Girth.markedRangeMap_mk
#print axioms StructuralRamsey.Girth.markedRangeEquiv
#print axioms StructuralRamsey.Girth.markedRangeEquiv_mk
#print axioms StructuralRamsey.Girth.markedRangeEquiv_unique
#print axioms StructuralRamsey.Girth.markedRangeEquiv_trans
#print axioms StructuralRamsey.Girth.markedRangeEquiv_fixed
#print axioms StructuralRamsey.Girth.sameMarkedKernel_of_observableProfile_eq
#print axioms StructuralRamsey.Girth.linearEdgeSet_insert_of_boundaryPairFree
#print axioms StructuralRamsey.Girth.linearEdgeSet_insert_iff
#print axioms StructuralRamsey.Girth.boundaryPairFree_image_iff
#print axioms StructuralRamsey.Girth.boundaryPairFree_iff_of_sameShadow
#print axioms StructuralRamsey.Girth.freshEdge_linearity_iff_of_sameBoundaryShadow
#print axioms StructuralRamsey.Girth.mem_boundaryShadowRecord
#print axioms StructuralRamsey.Girth.boundaryShadowRecord_mono
#print axioms StructuralRamsey.Girth.boundaryShadowChanges_bound
#print axioms StructuralRamsey.Girth.girthGT_insert_iff_noShortBergePath
#print axioms StructuralRamsey.Girth.markedBoundaryPath_mono
#print axioms StructuralRamsey.Girth.hasShortBergePath_image_iff
#print axioms StructuralRamsey.Girth.hasShortBergePath_image_congr
#print axioms StructuralRamsey.Girth.BergePath.endpoint_old_edges
#print axioms StructuralRamsey.Girth.hasShortBergePath_contact_iff
#print axioms StructuralRamsey.Girth.freshEdge_girth_iff_of_sameBoundaryPathShadow
#print axioms StructuralRamsey.Girth.mem_boundaryPathRecord
#print axioms StructuralRamsey.Girth.boundaryPathRecord_mono
#print axioms StructuralRamsey.Girth.boundaryPathChanges_bound

/-!
Regression: the retained copies are the disjoint triples {0,1,2} and
{3,4,5}. Adding the unmarked triple {0,3,6} leaves their marked equality
profile unchanged, but blocks the later fresh triple {0,3,7}.
-/
namespace StructuralRamsey.Girth.BoundaryShadowExample

def leftEdge : Set (Fin 8) := {0, 1, 2}
def rightEdge : Set (Fin 8) := {3, 4, 5}
def blocker : Set (Fin 8) := {0, 3, 6}
def candidate : Set (Fin 8) := {0, 3, 7}
def clearHost : Set (Set (Fin 8)) := {leftEdge, rightEdge}
def blockedHost : Set (Set (Fin 8)) := insert blocker clearHost

theorem clearHost_linear : LinearEdgeSet clearHost := by
  intro a b ha hb hab
  simp only [clearHost, Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  · exact False.elim (hab rfl)
  · intro x hx y hy
    fin_cases x <;> fin_cases y <;> norm_num [leftEdge, rightEdge] at *
  · intro x hx y hy
    fin_cases x <;> fin_cases y <;> norm_num [leftEdge, rightEdge] at *
  · exact False.elim (hab rfl)

theorem blocker_boundary_free : BoundaryPairFree clearHost blocker := by
  intro a ha
  simp only [clearHost, Set.mem_insert_iff, Set.mem_singleton_iff] at ha
  rcases ha with rfl | rfl <;> intro x hx y hy <;>
    fin_cases x <;> fin_cases y <;> norm_num [blocker, leftEdge, rightEdge] at *

theorem candidate_boundary_free : BoundaryPairFree clearHost candidate := by
  intro a ha
  simp only [clearHost, Set.mem_insert_iff, Set.mem_singleton_iff] at ha
  rcases ha with rfl | rfl <;> intro x hx y hy <;>
    fin_cases x <;> fin_cases y <;> norm_num [candidate, leftEdge, rightEdge] at *

theorem blockedHost_linear : LinearEdgeSet blockedHost :=
  linearEdgeSet_insert_of_boundaryPairFree clearHost_linear blocker_boundary_free

theorem candidate_clear_linear : LinearEdgeSet (insert candidate clearHost) :=
  linearEdgeSet_insert_of_boundaryPairFree clearHost_linear candidate_boundary_free

theorem candidate_blocked_not_linear : ¬ LinearEdgeSet (insert candidate blockedHost) := by
  intro hLinear
  have hEq : blocker = candidate :=
    linearEdge_eq_of_two_shared_vertices
      (insert candidate blockedHost) hLinear
      (by simp [blockedHost]) (by simp)
      (x := (0 : Fin 8)) (y := (3 : Fin 8)) (by decide)
      (by simp [blocker]) (by simp [candidate])
      (by simp [blocker]) (by simp [candidate])
  have hSix : (6 : Fin 8) ∈ candidate := hEq ▸ (by simp [blocker])
  norm_num [candidate] at hSix

/-- This is the contact missed by a profile of the retained copies alone. -/
theorem new_shadow_contact :
    markedBoundaryShadow blockedHost (id : Fin 8 → Fin 8) 0 3 ∧
      ¬ markedBoundaryShadow clearHost (id : Fin 8 → Fin 8) 0 3 := by
  constructor
  · refine ⟨by decide, blocker, ?_, ?_, ?_⟩ <;> simp [blockedHost, blocker]
  · rintro ⟨_, a, ha, hZero, hThree⟩
    simp only [clearHost, Set.mem_insert_iff, Set.mem_singleton_iff] at ha
    rcases ha with rfl | rfl
    · norm_num [leftEdge, id] at hThree
    · norm_num [rightEdge, id] at hZero

end StructuralRamsey.Girth.BoundaryShadowExample

#print axioms StructuralRamsey.Girth.BoundaryShadowExample.clearHost_linear
#print axioms StructuralRamsey.Girth.BoundaryShadowExample.blocker_boundary_free
#print axioms StructuralRamsey.Girth.BoundaryShadowExample.candidate_boundary_free
#print axioms StructuralRamsey.Girth.BoundaryShadowExample.blockedHost_linear
#print axioms StructuralRamsey.Girth.BoundaryShadowExample.candidate_clear_linear
#print axioms StructuralRamsey.Girth.BoundaryShadowExample.candidate_blocked_not_linear
#print axioms StructuralRamsey.Girth.BoundaryShadowExample.new_shadow_contact
