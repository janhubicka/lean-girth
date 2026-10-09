import Girth.ForestAttach
import Girth.ForestImage
import Mathlib.Tactic

/-!
# An explicit two-copy B-carrier gluing with a prescribed separator

This is the elementary carrier-faithful geometric model missing from a
purely syntactic pre-birth split. Given a hypergraph piece P and any
allowed separator S ⊆ P.carrier, embed two copies into W × Bool. The
first is at tag false; the second shares the false tag exactly at S
and otherwise uses tag true.

Thus their physical intersection is precisely the copied S, and any
private vertex outside S witnesses physically different carriers.
If S is a singleton or a complete intrinsic A-edge of P, the two
copies form a genuine ForestOfCopies with a two-node join tree.

This is a fixed *one-separator* geometric construction, not a
globally linear Ramsey reservoir admitting all successor shape maps.
In particular it does not realize incompatible multi-contact records.
-/

namespace StructuralRamsey.Girth

universe v
variable {W : Type v}

/-- First physical copy, retaining the false side of every port. -/
def twoCopyPortLeft (S : Set W) : W ↪ W × Bool where
  toFun x := (x, false)
  inj' := by
    intro x y h
    exact congrArg Prod.fst h

/-- Second physical copy, gluing exactly the vertices of S to the
first copy while keeping every other vertex private. -/
noncomputable def twoCopyPortRight (S : Set W) : W ↪ W × Bool := by
  classical
  exact
    { toFun := fun x => (x, if x ∈ S then false else true)
      inj' := by
        intro x y h
        exact congrArg Prod.fst h }

/-- Exactly the intended separator identifications occur between
the two copies: no other vertices are accidentally glued. -/
theorem twoCopyPort_cross_eq_iff
    (S : Set W) (x y : W) :
    twoCopyPortLeft S x = twoCopyPortRight S y ↔
      x = y ∧ x ∈ S := by
  classical
  constructor
  · intro h
    have hxy : x = y := congrArg Prod.fst h
    subst y
    have hs : x ∈ S := by
      by_contra hnot
      have hBool := congrArg Prod.snd h
      have hContra : False := by
        simpa [twoCopyPortLeft, twoCopyPortRight, hnot] using hBool
      exact hContra
    exact ⟨rfl, hs⟩
  · rintro ⟨rfl, hs⟩
    change (x, false) = (x, if x ∈ S then false else true)
    simp [hs]

/-- Every point of the separator has the same physical image under
both embeddings. -/
theorem twoCopyPort_agree_on_separator
    (S : Set W) {x : W} (hx : x ∈ S) :
    twoCopyPortLeft S x = twoCopyPortRight S x :=
  (twoCopyPort_cross_eq_iff S x x).mpr ⟨rfl, hx⟩

/-- A two-copy gluing creates precisely the prescribed physical
carrier overlap and nothing else, even for infinite pieces. -/
theorem twoCopyPort_images_inter
    (S C : Set W) :
    (twoCopyPortLeft S) '' C ∩
      (twoCopyPortRight S) '' C =
      (twoCopyPortLeft S) '' (C ∩ S) := by
  apply Set.Subset.antisymm
  · rintro z ⟨⟨x, hx, hxz⟩, ⟨y, hy, hyz⟩⟩
    have hCross :
        twoCopyPortLeft S x = twoCopyPortRight S y :=
      hxz.trans hyz.symm
    obtain ⟨hxy, hs⟩ := (twoCopyPort_cross_eq_iff S x y).mp hCross
    exact ⟨x, ⟨hx, hs⟩, hxz⟩
  · rintro z ⟨x, ⟨hx, hs⟩, hxz⟩
    refine ⟨⟨x, hx, hxz⟩, ⟨x, hx, ?_⟩⟩
    exact (twoCopyPort_agree_on_separator S hs).symm.trans hxz

/-- When the selected B-carrier contains a vertex outside the
separator, its two physical images are genuinely distinct. -/
theorem twoCopyPort_carriers_distinct
    (S C : Set W)
    (x : W) (hx : x ∈ C) (hPrivate : x ∉ S) :
    (twoCopyPortLeft S) '' C ≠ (twoCopyPortRight S) '' C := by
  intro hEqual
  have hxLeft : twoCopyPortLeft S x ∈ (twoCopyPortLeft S) '' C :=
    ⟨x, hx, rfl⟩
  rw [hEqual] at hxLeft
  obtain ⟨y, _, hCross⟩ := hxLeft
  exact hPrivate ((twoCopyPort_cross_eq_iff S x y).mp hCross.symm).2

/-- On the separator itself, the sets of physical images coincide. -/
theorem twoCopyPort_image_separator
    (S : Set W) :
    (twoCopyPortLeft S) '' S = (twoCopyPortRight S) '' S := by
  apply Set.Subset.antisymm
  · rintro z ⟨x, hx, hxz⟩
    exact ⟨x, hx, (twoCopyPort_agree_on_separator S hx).symm.trans hxz⟩
  · rintro z ⟨x, hx, hxz⟩
    exact ⟨x, hx, (twoCopyPort_agree_on_separator S hx).trans hxz⟩

/-- If S is a singleton (possibly empty) or one COMPLETE A-support edge
of P, the two actual physical B-copies meet in a permitted separator. -/
theorem twoCopyPort_allowedIntersection
    (P : HypergraphPiece W) (S : Set W)
    (hSub : S ⊆ P.carrier)
    (hAllowed : S.Subsingleton ∨ S ∈ P.edges) :
    AllowedIntersection
      (P.map (twoCopyPortLeft S))
      (P.map (twoCopyPortRight S)) := by
  have hIntersect :
      (P.map (twoCopyPortLeft S)).carrier ∩
        (P.map (twoCopyPortRight S)).carrier =
        (twoCopyPortLeft S) '' S := by
    change (twoCopyPortLeft S) '' P.carrier ∩
      (twoCopyPortRight S) '' P.carrier =
      (twoCopyPortLeft S) '' S
    rw [twoCopyPort_images_inter]
    congr 1
    apply Set.Subset.antisymm
    · exact Set.inter_subset_right
    · intro x hx
      exact ⟨hSub hx, hx⟩
  rcases hAllowed with hSmall | hEdge
  · left
    rw [hIntersect]
    intro x hx y hy
    obtain ⟨a, ha, rfl⟩ := hx
    obtain ⟨b, hb, rfl⟩ := hy
    exact congrArg (twoCopyPortLeft S) (hSmall ha hb)
  · right
    refine ⟨(twoCopyPortLeft S) '' S, ?_, ?_, hIntersect⟩
    · exact ⟨S, hEdge, rfl⟩
    · exact ⟨S, hEdge, twoCopyPort_image_separator S⟩

/-- The explicit two-copy configuration is an actual forest.
It has both the allowed pairwise overlap and a two-vertex join tree. -/
theorem twoCopyPort_forest
    (P : HypergraphPiece W) (S : Set W)
    (hSub : S ⊆ P.carrier)
    (hAllowed : S.Subsingleton ∨ S ∈ P.edges) :
    ForestOfCopies
      (sumPieces
        (fun _ : PUnit.{v+1} => P.map (twoCopyPortLeft S))
        (fun _ : PUnit.{v+1} => P.map (twoCopyPortRight S))) := by
  classical
  let FL := P.map (twoCopyPortLeft S)
  let FR := P.map (twoCopyPortRight S)
  let JL : JoinTree (fun _ : PUnit.{v+1} => FL) :=
    joinTree_singlePiece FL
  let JR : JoinTree (fun _ : PUnit.{v+1} => FR) :=
    joinTree_singlePiece FR
  apply forestOfCopies_sumBridge JL JR
    (pairwiseAllowed_singlePiece FL)
    (pairwiseAllowed_singlePiece FR)
    PUnit.unit PUnit.unit
  · intro z i j hzL hzR
    exact ⟨hzL, hzR⟩
  · intro i j
    exact twoCopyPort_allowedIntersection P S hSub hAllowed

end StructuralRamsey.Girth
