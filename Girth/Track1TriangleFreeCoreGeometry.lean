import Girth.ForestShortCycleProjection
import Girth.TrainRecursiveCutoffTwoCoreGeometry
import Girth.TrainRecursiveBaseRamsey

set_option autoImplicit false
set_option quotPrecheck false
set_option Elab.async false

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v

namespace CutoffTwoLiftData

variable {L : RelLanguage.{u}} {U V W I : Type v}
variable {A : RelStructure L U} {D : RelStructure L W}

variable (Target : StructuralRamsey.Partite.System L U V)
variable (C : CutoffTwoLiftData A Target.toRelStructure D I)
variable (hPart : C.part = Target.part)

local notation "f" => C.liftedEmbedding Target hPart
local notation "Core" => (C.system Target hPart).toRelStructure

private theorem project_image_liftedCopy (i : I) :
    C.project '' copyCarrier (f i) = copyCarrier (C.original i) := by
  rw [copyCarrier, copyCarrier, ← Set.range_comp]
  rfl

private theorem project_image_liftedEdge (i : I)
    (a : Embedding A Target.toRelStructure) :
    C.project '' copyCarrier ((f i).comp a) = copyCarrier ((C.original i).comp a) := by
  rw [copyCarrier, copyCarrier, ← Set.range_comp]
  rfl

private theorem project_injOn_liftedCopy (i : I) :
    Set.InjOn C.project (copyCarrier (f i)) := by
  rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩ h
  exact congrArg (f i) ((C.original i).injective h)

/-- The literal lifted copies stay physically distinct, since their
projected carriers are the corresponding old selected carriers. -/
theorem lifted_support_injective
    (hDistinct : Function.Injective (fun i => copyCarrier (C.original i))) :
    Function.Injective (fun i => bSupportPiece A (f i)) := by
  intro i j h
  apply hDistinct
  change copyCarrier (C.original i) = copyCarrier (C.original j)
  rw [← C.project_image_liftedCopy Target hPart i, ← C.project_image_liftedCopy Target hPart j]
  exact congrArg (fun P : HypergraphPiece C.Vertex => C.project '' P.carrier) h

variable (hPartOnA : ∀ (a : Embedding A Target.toRelStructure) (u : U), C.part (a u) = u)
variable (hOwner : ∀ (a : Embedding A Target.toRelStructure) (u : U),
  u ∉ C.allowed → C.owner (a u) = a)

include hPartOnA hOwner in
/-- The lifted core has the same two- and three-cycle exclusion as the
old witness. Distinct physical core edges cannot project to one old edge. -/
theorem core_girthGT_three
    (hLifted : ∀ e : Embedding A Core, ∃ (i : I) (a : Embedding A Target.toRelStructure),
      e = (f i).comp a)
    (hRigid : ∀ a b : Embedding A D, SameCopy a b → a = b)
    (hGirth : GirthGT (supportCopies A D) 3) : GirthGT (supportCopies A Core) 3 := by
  apply girthGT_three_of_edgeProjection C.project _ _ _ hGirth
  · rintro _ ⟨e, rfl⟩
    obtain ⟨i, a, rfl⟩ := hLifted e
    rw [C.project_image_liftedEdge Target hPart]
    exact ⟨(C.original i).comp a, rfl⟩
  · rintro _ ⟨e, rfl⟩ _ ⟨g, rfl⟩ h
    obtain ⟨i, a, rfl⟩ := hLifted e
    obtain ⟨j, b, rfl⟩ := hLifted g
    change C.project '' copyCarrier ((f i).comp a) =
      C.project '' copyCarrier ((f j).comp b) at h
    rw [C.project_image_liftedEdge Target hPart, C.project_image_liftedEdge Target hPart] at h
    have hOld := hRigid _ _ h
    apply congrArg copyCarrier
    apply Embedding.ext
    intro u
    exact congrFun (C.lift_compatible hPartOnA hOwner i j a b hOld) u
  · rintro _ ⟨e, rfl⟩
    obtain ⟨i, a, rfl⟩ := hLifted e
    apply (C.project_injOn_liftedCopy Target hPart i).mono
    rintro _ ⟨u, rfl⟩
    exact ⟨a u, rfl⟩

include hPartOnA hOwner in
/-- The projection of an intersection determines its lift inside either
selected copy. A shared old A-edge has one compatible lift in both copies. -/
theorem lifted_controlledIntersection
    (hOld : ∀ i j : I, i ≠ j →
      (copyCarrier (C.original i) ∩ copyCarrier (C.original j)).Subsingleton ∨
      ∃ a : Embedding A D, copyCarrier (C.original i) ∩ copyCarrier (C.original j) = copyCarrier a)
    (i j : I) (hNe : ¬ SameCopy (f i) (f j)) :
    (copyCarrier (f i) ∩ copyCarrier (f j)).Subsingleton ∨
    ∃ a : Embedding A Core, copyCarrier (f i) ∩ copyCarrier (f j) = copyCarrier a := by
  classical
  have hij : i ≠ j := by
    intro h
    subst j
    exact hNe (sameCopy_refl _)
  have hProject (r : I) {z : C.Vertex} (hz : z ∈ copyCarrier (f r)) :
      C.project z ∈ copyCarrier (C.original r) := by
    rw [← C.project_image_liftedCopy Target hPart]
    exact ⟨z, hz, rfl⟩
  rcases hOld i j hij with hSmall | ⟨a, ha⟩
  · left
    intro x hx y hy
    exact C.project_injOn_liftedCopy Target hPart i hx.1 hy.1
      (hSmall ⟨hProject i hx.1, hProject j hx.2⟩ ⟨hProject i hy.1, hProject j hy.2⟩)
  · right
    have hFactor (r : I) (hSub : copyCarrier a ⊆ copyCarrier (C.original r))
        (u : U) : ∃ x : V, a u = C.original r x := by
      obtain ⟨x, hx⟩ := hSub ⟨u, rfl⟩
      exact ⟨x, hx.symm⟩
    have hSubI : copyCarrier a ⊆ copyCarrier (C.original i) := by
      rw [← ha]
      exact Set.inter_subset_left
    have hSubJ : copyCarrier a ⊆ copyCarrier (C.original j) := by
      rw [← ha]
      exact Set.inter_subset_right
    let ai := a.factorThroughRange (C.original i) (hFactor i hSubI)
    let aj := a.factorThroughRange (C.original j) (hFactor j hSubJ)
    have hi : (C.original i).comp ai = a := by
      apply Embedding.ext
      intro u
      exact (Classical.choose_spec (hFactor i hSubI u)).symm
    have hj : (C.original j).comp aj = a := by
      apply Embedding.ext
      intro u
      exact (Classical.choose_spec (hFactor j hSubJ u)).symm
    have hCommon : (f i).comp ai = (f j).comp aj := by
      apply Embedding.ext
      intro u
      exact congrFun (C.lift_compatible hPartOnA hOwner i j ai aj (hi.trans hj.symm)) u
    refine ⟨(f i).comp ai, Set.Subset.antisymm ?_ ?_⟩
    · intro z hz
      have hProjected : C.project z ∈ copyCarrier a := ha ▸ ⟨hProject i hz.1, hProject j hz.2⟩
      obtain ⟨u, hu⟩ := hProjected
      have hProjectedEq : C.project ((f i).comp ai u) = C.project z := by
        change ((C.original i).comp ai) u = C.project z
        rw [hi]
        exact hu
      exact ⟨u, C.project_injOn_liftedCopy Target hPart i ⟨ai u, rfl⟩ hz.1 hProjectedEq⟩
    · rintro z ⟨u, rfl⟩
      refine ⟨⟨ai u, rfl⟩, ?_⟩
      rw [hCommon]
      exact ⟨aj u, rfl⟩

end CutoffTwoLiftData

#print axioms StructuralRamsey.Girth.CutoffTwoLiftData.lifted_support_injective
#print axioms StructuralRamsey.Girth.CutoffTwoLiftData.core_girthGT_three
#print axioms StructuralRamsey.Girth.CutoffTwoLiftData.lifted_controlledIntersection

end StructuralRamsey.Girth
