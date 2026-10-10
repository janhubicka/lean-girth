import Girth.LocalForestBridge
import Girth.LocalForestPieces
import Girth.ForestUsedOwnerLocalForest
import Girth.Berge

/-!
# Noncircular edge-coverage normalization of a local Ramsey witness

The circulation proof's forest increment assigns each selected core
A-edge to a designated local gluing B-copy. The recursive FF theorem
does NOT itself assert that every ambient edge is so covered.

The correct local normalization discards the support edges which
belong to no designated source copy. The existing strong support
embeddings restrict to that support reduct, its girth does not
decrease, the surviving family covers every retained edge, and the
edge Ramsey arrow survives by extending colours to the old support.

The vertex/core-train restriction and its parent maps are separate
next formalization steps. No theorem below claims that the entire
train-recursion statement is now proved.
-/

namespace StructuralRamsey.Girth

universe v w
variable {X Y : Type v}

/-- Retain precisely those actual target support edges that occur
inside at least one designated strong image of the source. -/
def coveredLocalEdges
    (H : Set (Set X)) {K : Set (Set Y)}
    (family : Set (StrongSupportEmbedding H K)) :
    Set (Set Y) :=
  {E | ∃ f : StrongSupportEmbedding H K, f ∈ family ∧
    ∃ e : Set X, e ∈ H ∧ E = f '' e}

/-- Coverage reduction never introduces an ambient support edge. -/
theorem coveredLocalEdges_subset
    (H : Set (Set X)) {K : Set (Set Y)}
    (family : Set (StrongSupportEmbedding H K)) :
    coveredLocalEdges H family ⊆ K := by
  intro E hE
  obtain ⟨f, _hf, e, he, hEq⟩ := hE
  obtain ⟨E0, hE0, hMap⟩ := f.map_edge e he
  have hSame : E = E0 := hEq.trans hMap.symm
  rw [hSame]
  exact hE0

/-- Any chosen strong support embedding remains strong after retaining
only the edges that belong to some designated image. -/
def StrongSupportEmbedding.restrictCovered
    (H : Set (Set X)) {K : Set (Set Y)}
    (family : Set (StrongSupportEmbedding H K))
    (f : StrongSupportEmbedding H K) (hf : f ∈ family) :
    StrongSupportEmbedding H (coveredLocalEdges H family) where
  toFun := f.toFun
  injective := f.injective
  map_edge := by
    intro e he
    exact ⟨f '' e, ⟨f, hf, e, he, rfl⟩, rfl⟩
  reflect_edge := by
    intro E hE hMeet
    exact f.reflect_edge E
      (coveredLocalEdges_subset H family hE) hMeet

/-- The intrinsic support piece of a retained designated copy is
unchanged: pruning modifies the ambient edge family, not the
source edge set or the image map of the designated copy. -/
theorem StrongSupportEmbedding.restrictCovered_supportPiece
    (H : Set (Set X)) {K : Set (Set Y)}
    (family : Set (StrongSupportEmbedding H K))
    (f : StrongSupportEmbedding H K) (hf : f ∈ family) :
    (f.restrictCovered H family hf).supportPiece = f.supportPiece := by
  rfl

/-- Designated restricted embeddings, indexed by their original
family labels. No distinctness or finiteness assumption is needed. -/
def coveredLocalFamily
    (H : Set (Set X)) {K : Set (Set Y)}
    (family : Set (StrongSupportEmbedding H K)) :
    Set (StrongSupportEmbedding H (coveredLocalEdges H family)) :=
  Set.range (fun f : {f : StrongSupportEmbedding H K // f ∈ family} =>
    f.1.restrictCovered H family f.2)

/-- The reduced local witness satisfies EXACT designated edge
coverage, without using the final local forest partite theorem. -/
theorem coveredLocalFamily_covers
    (H : Set (Set X)) {K : Set (Set Y)}
    (family : Set (StrongSupportEmbedding H K)) :
    StrongSupportCoversEdges H (coveredLocalEdges H family)
      (coveredLocalFamily H family) := by
  intro E hE
  obtain ⟨f, hf, e, he, hEq⟩ := hE
  let g := f.restrictCovered H family hf
  refine ⟨g, ?_, e, he, ?_⟩
  · exact ⟨⟨f, hf⟩, rfl⟩
  · exact hEq

/-- Ordinary Berge girth only improves after coverage normalization. -/
theorem girthGT_coveredLocalEdges
    (H : Set (Set X)) {K : Set (Set Y)}
    (family : Set (StrongSupportEmbedding H K))
    (q : ℕ) (hGirth : GirthGT K q) :
    GirthGT (coveredLocalEdges H family) q :=
  girthGT_of_subset (coveredLocalEdges_subset H family) hGirth

/-- A labelled designated-copy support edge is automatically retained
in the covered reduct. This is the key input for Ramsey transfer. -/
theorem StrongSupportEmbedding.edge_mem_covered
    (H : Set (Set X)) {K : Set (Set Y)}
    (family : Set (StrongSupportEmbedding H K))
    (f : StrongSupportEmbedding H K) (hf : f ∈ family)
    (e : Set X) (he : e ∈ H) :
    f '' e ∈ coveredLocalEdges H family :=
  ⟨f, hf, e, he, rfl⟩

/-- A strong support embedding maps every source edge to an ACTUAL
target edge, with no need to choose a target-edge witness. -/
theorem StrongSupportEmbedding.mappedEdge_mem
    {H : Set (Set X)} {K : Set (Set Y)}
    (f : StrongSupportEmbedding H K)
    (e : Set X) (he : e ∈ H) :
    f '' e ∈ K := by
  obtain ⟨E, hE, hEq⟩ := f.map_edge e he
  rw [← hEq]
  exact hE

/-- Edge Ramsey arrow coloured only on ACTUAL target edges. -/
def StrongSupportEdgeArrow
    (H : Set (Set X)) {K : Set (Set Y)}
    (family : Set (StrongSupportEmbedding H K))
    (κ : Type w) : Prop :=
  ∀ χ : K → κ,
    ∃ f : StrongSupportEmbedding H K, f ∈ family ∧
      ∃ c : κ, ∀ (e : Set X) (he : e ∈ H),
        χ ⟨f '' e, f.mappedEdge_mem e he⟩ = c

/-- Every colouring of the RETAINED support edges extends arbitrarily
to the original support; the old Ramsey arrow then gives a
monochromatic designated copy, all of whose edges were retained. -/
theorem strongSupportEdgeArrow_covered
    (H : Set (Set X)) {K : Set (Set Y)}
    (family : Set (StrongSupportEmbedding H K))
    (κ : Type w) [Inhabited κ]
    (hArrow : StrongSupportEdgeArrow H family κ) :
    StrongSupportEdgeArrow H (coveredLocalFamily H family) κ := by
  classical
  intro χ
  let oldColour : K → κ := fun x =>
    if hx : x.1 ∈ coveredLocalEdges H family then
      χ ⟨x.1, hx⟩
    else default
  obtain ⟨f, hf, c, hMono⟩ := hArrow oldColour
  let g := f.restrictCovered H family hf
  refine ⟨g, ⟨⟨f, hf⟩, rfl⟩, c, ?_⟩
  intro e he
  have hRetained : f '' e ∈ coveredLocalEdges H family :=
    f.edge_mem_covered H family hf e he
  have hOld : oldColour ⟨f '' e, f.mappedEdge_mem e he⟩ = c :=
    hMono e he
  simpa [oldColour, g, hRetained,
    StrongSupportEmbedding.restrictCovered] using hOld


/-- Every bounded designated-copy forest statement is inherited by
the same labelled image family after covered-edge normalization.
Its pieces and their support edges are literally unchanged. -/
theorem localForestThrough_restrictCovered
    {I : Type v}
    (H : Set (Set X)) {K : Set (Set Y)}
    (family : Set (StrongSupportEmbedding H K))
    (copies : I → StrongSupportEmbedding H K)
    (hCopies : ∀ i, copies i ∈ family)
    (m : ℕ)
    (hLocal :
      LocalForestThrough
        (fun i : I => (copies i).supportPiece) m) :
    LocalForestThrough
      (fun i : I =>
        ((copies i).restrictCovered H family (hCopies i)).supportPiece) m := by
  intro J hFinite idx hBound
  have hEq :
      (fun j : J =>
        ((copies (idx j)).restrictCovered H family
          (hCopies (idx j))).supportPiece) =
      (fun j : J => (copies (idx j)).supportPiece) := by
    funext j
    exact (copies (idx j)).restrictCovered_supportPiece
      H family (hCopies (idx j))
  rw [hEq]
  exact hLocal J idx hBound

end StructuralRamsey.Girth
