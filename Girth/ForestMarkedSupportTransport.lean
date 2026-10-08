import Girth.ForestMarkedJoinTransport
import Mathlib.Tactic

/-!
# Complete forest geometry from jointly labelled carriers and A-support

A full marked equality kernel determines intersections of the realised
carrier images, including whether they are subsingletons and whether
an intersection is exactly an image of a named support edge.

For two evaluated families whose carriers and local A-support edges
are images of the same labelled vertex and edge records, equality
of their joint marked kernels therefore preserves pairwise allowed
intersections. Combining this with the finite incidence-mask join-tree
theorem proves that the *entire* forest predicate is invariant.

This is a complete semantic transport result for a fixed finite
family, not an admissible free-successor-tree map and not a global
reservoir construction.
-/

namespace StructuralRamsey.Girth

universe v

variable {I C W Z : Type v} [Fintype C]

/-- If a labelled image intersection is exactly a labelled image
U, the same equality holds for any evaluation with the same kernel. -/
private theorem markedImage_inter_eq_image_transfer
    (f : I → W) (g : I → Z) (h : SameMarkedKernel f g)
    (S T U : Set I)
    (hEq : f '' S ∩ f '' T = f '' U) :
    g '' S ∩ g '' T = g '' U := by
  apply Set.Subset.antisymm
  · rintro x ⟨⟨i, hi, hix⟩, hxT⟩
    have hiF : f i ∈ f '' S ∩ f '' T := by
      constructor
      · exact ⟨i, hi, rfl⟩
      · apply (markedImage_mem_iff_sameKernel f g h T i).mpr
        simpa [hix] using hxT
    have hiU : f i ∈ f '' U := by
      rw [← hEq]
      exact hiF
    have hiGU : g i ∈ g '' U :=
      (markedImage_mem_iff_sameKernel f g h U i).mp hiU
    simpa [hix] using hiGU
  · rintro x ⟨i, hi, hix⟩
    have hiU : f i ∈ f '' U := ⟨i, hi, rfl⟩
    have hiST : f i ∈ f '' S ∩ f '' T := by
      rw [hEq]
      exact hiU
    have hiGS : g i ∈ g '' S :=
      (markedImage_mem_iff_sameKernel f g h S i).mp hiST.1
    have hiGT : g i ∈ g '' T :=
      (markedImage_mem_iff_sameKernel f g h T i).mp hiST.2
    simpa [hix] using (show g i ∈ g '' S ∩ g '' T from ⟨hiGS, hiGT⟩)

/-- Exact intersections with labelled support edges transport in both
directions, without requiring f or g to be injective on all labels. -/
theorem markedImage_inter_eq_image_iff
    (f : I → W) (g : I → Z) (h : SameMarkedKernel f g)
    (S T U : Set I) :
    (f '' S ∩ f '' T = f '' U) ↔
      (g '' S ∩ g '' T = g '' U) := by
  constructor
  · exact markedImage_inter_eq_image_transfer f g h S T U
  · exact markedImage_inter_eq_image_transfer g f h.symm S T U

/-- Subsingleton intersections are also invariant under equality
of the joint marked kernel. -/
private theorem markedImage_inter_subsingleton_transfer
    (f : I → W) (g : I → Z) (h : SameMarkedKernel f g)
    (S T : Set I)
    (hSmall : (f '' S ∩ f '' T).Subsingleton) :
    (g '' S ∩ g '' T).Subsingleton := by
  intro x hx y hy
  obtain ⟨i, hi, hix⟩ := hx.1
  obtain ⟨j, hj, hjy⟩ := hy.1
  have hiT : f i ∈ f '' T := by
    apply (markedImage_mem_iff_sameKernel f g h T i).mpr
    simpa [hix] using hx.2
  have hjT : f j ∈ f '' T := by
    apply (markedImage_mem_iff_sameKernel f g h T j).mpr
    simpa [hjy] using hy.2
  have hij : f i = f j :=
    hSmall ⟨⟨i, hi, rfl⟩, hiT⟩ ⟨⟨j, hj, rfl⟩, hjT⟩
  calc
    x = g i := hix.symm
    _ = g j := (h i j).mp hij
    _ = y := hjy

theorem markedImage_inter_subsingleton_iff
    (f : I → W) (g : I → Z) (h : SameMarkedKernel f g)
    (S T : Set I) :
    (f '' S ∩ f '' T).Subsingleton ↔
      (g '' S ∩ g '' T).Subsingleton := by
  constructor
  · exact markedImage_inter_subsingleton_transfer f g h S T
  · exact markedImage_inter_subsingleton_transfer g f h.symm S T

/-- Every local support edge is an image of one of the same labelled
intrinsic A-edges in both evaluated copies. This hypothesis does NOT
say that the whole ambient host has no extra edges. -/
def SameMarkedSupportPresentation
    (F : C → HypergraphPiece W) (G : C → HypergraphPiece Z)
    (f : I → W) (g : I → Z)
    (carriers : C → Set I) (atoms : C → Set (Set I)) : Prop :=
  (∀ c, (F c).carrier = f '' carriers c) ∧
  (∀ c, (G c).carrier = g '' carriers c) ∧
  (∀ c e, e ∈ (F c).edges ↔
    ∃ a ∈ atoms c, e = f '' a) ∧
  (∀ c e, e ∈ (G c).edges ↔
    ∃ a ∈ atoms c, e = g '' a)

/-- One pair of B-pieces has an allowed intersection in one evaluated
host exactly when it does in the other. The only hypothesis linking
different carriers is the full *joint* vertex-equality kernel. -/
private theorem allowedIntersection_transfer_marked
    (F : C → HypergraphPiece W) (G : C → HypergraphPiece Z)
    (f : I → W) (g : I → Z) (h : SameMarkedKernel f g)
    (carriers : C → Set I) (atoms : C → Set (Set I))
    (hPresent : SameMarkedSupportPresentation F G f g carriers atoms)
    (c d : C)
    (hAllowed : AllowedIntersection (F c) (F d)) :
    AllowedIntersection (G c) (G d) := by
  obtain ⟨hCF, hCG, hEF, hEG⟩ := hPresent
  rcases hAllowed with hSmall | ⟨e, heC, heD, hInter⟩
  · left
    rw [hCG c, hCG d]
    exact (markedImage_inter_subsingleton_iff f g h
      (carriers c) (carriers d)).mp (by
        simpa only [← hCF c, ← hCF d] using hSmall)
  · obtain ⟨a, ha, heqa⟩ := (hEF c e).mp heC
    obtain ⟨b, hb, heqb⟩ := (hEF d e).mp heD
    have hab : f '' a = f '' b := heqa.symm.trans heqb
    have habG : g '' a = g '' b :=
      (h.image_eq_iff a b).mp hab
    have hImageInter :
        f '' carriers c ∩ f '' carriers d = f '' a := by
      calc
        f '' carriers c ∩ f '' carriers d =
          (F c).carrier ∩ (F d).carrier := by rw [hCF c, hCF d]
        _ = e := hInter
        _ = f '' a := heqa
    have hImageInterG :
        g '' carriers c ∩ g '' carriers d = g '' a :=
      (markedImage_inter_eq_image_iff f g h
        (carriers c) (carriers d) a).mp hImageInter
    right
    refine ⟨g '' a, (hEG c _).mpr ⟨a, ha, rfl⟩, ?_, ?_⟩
    · exact (hEG d _).mpr ⟨b, hb, habG⟩
    · simpa only [hCG c, hCG d] using hImageInterG

theorem markedFamily_allowedIntersection_iff
    (F : C → HypergraphPiece W) (G : C → HypergraphPiece Z)
    (f : I → W) (g : I → Z) (h : SameMarkedKernel f g)
    (carriers : C → Set I) (atoms : C → Set (Set I))
    (hPresent : SameMarkedSupportPresentation F G f g carriers atoms)
    (c d : C) :
    AllowedIntersection (F c) (F d) ↔
      AllowedIntersection (G c) (G d) := by
  constructor
  · exact allowedIntersection_transfer_marked
      F G f g h carriers atoms hPresent c d
  · have hSwap :
        SameMarkedSupportPresentation G F g f carriers atoms :=
      ⟨hPresent.2.1, hPresent.1, hPresent.2.2.2, hPresent.2.2.1⟩
    exact allowedIntersection_transfer_marked
      G F g f h.symm carriers atoms hSwap c d

/-- All pairwise allowed overlaps are transported simultaneously. -/
theorem markedFamily_pairwiseAllowed_iff
    (F : C → HypergraphPiece W) (G : C → HypergraphPiece Z)
    (f : I → W) (g : I → Z) (h : SameMarkedKernel f g)
    (carriers : C → Set I) (atoms : C → Set (Set I))
    (hPresent : SameMarkedSupportPresentation F G f g carriers atoms) :
    PairwiseAllowed F ↔ PairwiseAllowed G := by
  constructor
  · intro hAll c d hcd
    exact (markedFamily_allowedIntersection_iff
      F G f g h carriers atoms hPresent c d).mp (hAll hcd)
  · intro hAll c d hcd
    exact (markedFamily_allowedIntersection_iff
      F G f g h carriers atoms hPresent c d).mpr (hAll hcd)

/-- The FULL forest condition of two finitely many B-copies is identical
under a joint marked kernel whenever each copy has the same intrinsic
labelled carrier and A-support edges. Unlike a kernel-only assertion,
this verifies both permitted pairwise intersections and the join tree. -/
theorem markedFamily_forest_iff_of_supportPresentation
    (F : C → HypergraphPiece W) (G : C → HypergraphPiece Z)
    (f : I → W) (g : I → Z) (h : SameMarkedKernel f g)
    (carriers : C → Set I) (atoms : C → Set (Set I))
    (hPresent : SameMarkedSupportPresentation F G f g carriers atoms) :
    ForestOfCopies F ↔ ForestOfCopies G := by
  exact markedFamily_forest_iff F G f g h carriers
    hPresent.1 hPresent.2.1
    (markedFamily_pairwiseAllowed_iff F G f g h carriers atoms hPresent)

end StructuralRamsey.Girth
