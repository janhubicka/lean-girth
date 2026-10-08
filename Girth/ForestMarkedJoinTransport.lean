import Girth.ForestFiniteJoinMasks
import Girth.ForestMarkedTransport
import Mathlib.Tactic

/-!
# Join-tree invariance under coherent marked-vertex transport

Given two jointly labelled families of carriers, equality of their
marked-vertex kernels determines every *nonempty* vertex-occurrence
mask. Empty occurrence masks can differ because unrelated ambient
vertices need not be retained. They impose no join-tree condition.

Thus the existence of a running-intersection join tree is invariant
under one coherent marked-union transport, rather than independent
per-copy maps. If pairwise allowed intersections are also preserved,
the complete forest predicate is invariant.

These are semantic transport theorems, not an assertion that the
transport is a permissible free-successor-tree shape map.
-/

namespace StructuralRamsey.Girth

universe v

variable {I C W Z : Type v} [Fintype C]

/-- For a fixed marked label, image membership in any labelled
carrier is invariant under equality of the full marked kernel. -/
theorem markedImage_mem_iff_sameKernel
    (f : I → W) (g : I → Z) (h : SameMarkedKernel f g)
    (S : Set I) (i : I) :
    f i ∈ f '' S ↔ g i ∈ g '' S := by
  constructor
  · rintro ⟨j, hj, hji⟩
    exact ⟨j, hj, (h j i).mp hji⟩
  · rintro ⟨j, hj, hji⟩
    exact ⟨j, hj, (h j i).mpr hji⟩

/-- Nonempty masks are the only incidence constraints relevant for
running intersections. Empty masks impose no restriction on a graph. -/
theorem joinTree_iff_sameNonemptyMasks
    (F : C → HypergraphPiece W) (G : C → HypergraphPiece Z)
    (hMasks : ∀ mask : Finset C, mask.Nonempty →
      (ForestVertexMaskRealised F mask ↔ ForestVertexMaskRealised G mask)) :
    Nonempty (JoinTree F) ↔ Nonempty (JoinTree G) := by
  rw [nonempty_joinTree_iff_finiteMasks,
      nonempty_joinTree_iff_finiteMasks]
  constructor
  · rintro ⟨T, hT, hRun⟩
    refine ⟨T, hT, ?_⟩
    intro mask hReal
    by_cases hNE : mask.Nonempty
    · exact hRun mask ((hMasks mask hNE).mpr hReal)
    · letI : Subsingleton {c : C // c ∈ (↑mask : Set C)} :=
        ⟨by
          intro a b
          exfalso
          apply hNE
          exact ⟨a.1, by simpa using a.property⟩⟩
      exact SimpleGraph.Preconnected.of_subsingleton
  · rintro ⟨T, hT, hRun⟩
    refine ⟨T, hT, ?_⟩
    intro mask hReal
    by_cases hNE : mask.Nonempty
    · exact hRun mask ((hMasks mask hNE).mp hReal)
    · letI : Subsingleton {c : C // c ∈ (↑mask : Set C)} :=
        ⟨by
          intro a b
          exfalso
          apply hNE
          exact ⟨a.1, by simpa using a.property⟩⟩
      exact SimpleGraph.Preconnected.of_subsingleton

/-- Every vertex of the jointly marked union has the same mask
under the two evaluations. Labels can be noninjective as long as
both evaluations identify exactly the same pairs. -/
theorem markedFamily_vertexMask_eq
    (F : C → HypergraphPiece W) (G : C → HypergraphPiece Z)
    (f : I → W) (g : I → Z) (h : SameMarkedKernel f g)
    (labels : C → Set I)
    (hF : ∀ c, (F c).carrier = f '' labels c)
    (hG : ∀ c, (G c).carrier = g '' labels c)
    (i : I) :
    forestVertexMask F (f i) = forestVertexMask G (g i) := by
  ext c
  simp only [mem_forestVertexMask, hF c, hG c]
  exact markedImage_mem_iff_sameKernel f g h (labels c) i

/-- Apart from the possible empty mask coming from unmarked ambient
vertices, all realised occurrence masks are preserved by coherent
marked-union transport. -/
theorem markedFamily_nonemptyMasks_iff
    (F : C → HypergraphPiece W) (G : C → HypergraphPiece Z)
    (f : I → W) (g : I → Z) (h : SameMarkedKernel f g)
    (labels : C → Set I)
    (hF : ∀ c, (F c).carrier = f '' labels c)
    (hG : ∀ c, (G c).carrier = g '' labels c)
    (mask : Finset C) (hNE : mask.Nonempty) :
    ForestVertexMaskRealised F mask ↔ ForestVertexMaskRealised G mask := by
  constructor
  · rintro ⟨x, hx⟩
    obtain ⟨c, hc⟩ := hNE
    have hxC : x ∈ (F c).carrier := by
      have hcMem : c ∈ forestVertexMask F x := by rw [hx]; exact hc
      exact (mem_forestVertexMask F x c).mp hcMem
    rw [hF c] at hxC
    obtain ⟨i, _, hi⟩ := hxC
    refine ⟨g i, ?_⟩
    calc
      forestVertexMask G (g i) = forestVertexMask F (f i) :=
        (markedFamily_vertexMask_eq F G f g h labels hF hG i).symm
      _ = forestVertexMask F x := by rw [hi]
      _ = mask := hx
  · rintro ⟨z, hz⟩
    obtain ⟨c, hc⟩ := hNE
    have hzC : z ∈ (G c).carrier := by
      have hcMem : c ∈ forestVertexMask G z := by rw [hz]; exact hc
      exact (mem_forestVertexMask G z c).mp hcMem
    rw [hG c] at hzC
    obtain ⟨i, _, hi⟩ := hzC
    refine ⟨f i, ?_⟩
    calc
      forestVertexMask F (f i) = forestVertexMask G (g i) :=
        markedFamily_vertexMask_eq F G f g h labels hF hG i
      _ = forestVertexMask G z := by rw [hi]
      _ = mask := hz

/-- The actual join-tree existence property is a geometric invariant
of the *joint* equality kernel of all named B-copy vertex positions. -/
theorem markedFamily_joinTree_iff
    (F : C → HypergraphPiece W) (G : C → HypergraphPiece Z)
    (f : I → W) (g : I → Z) (h : SameMarkedKernel f g)
    (labels : C → Set I)
    (hF : ∀ c, (F c).carrier = f '' labels c)
    (hG : ∀ c, (G c).carrier = g '' labels c) :
    Nonempty (JoinTree F) ↔ Nonempty (JoinTree G) := by
  exact joinTree_iff_sameNonemptyMasks F G
    (markedFamily_nonemptyMasks_iff F G f g h labels hF hG)

/-- Full foresthood transfers when its other ingredient (permitted
pairwise intersections) is also respected. The latter must be proved
using actual support-edge data, not merely the vertex kernel. -/
theorem markedFamily_forest_iff
    (F : C → HypergraphPiece W) (G : C → HypergraphPiece Z)
    (f : I → W) (g : I → Z) (h : SameMarkedKernel f g)
    (labels : C → Set I)
    (hF : ∀ c, (F c).carrier = f '' labels c)
    (hG : ∀ c, (G c).carrier = g '' labels c)
    (hAllowed : PairwiseAllowed F ↔ PairwiseAllowed G) :
    ForestOfCopies F ↔ ForestOfCopies G := by
  unfold ForestOfCopies
  exact and_congr hAllowed
    (or_congr Iff.rfl
      (markedFamily_joinTree_iff F G f g h labels hF hG))

end StructuralRamsey.Girth
