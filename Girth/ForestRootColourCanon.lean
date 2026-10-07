import Girth.ForestParameterFreeOrbit
import Girth.ForestSuccessorBridge
import SuccessorTree.ShapeAction
import Mathlib.Tactic

/-!
# Ramsey canonisation of parameter-free event-base colours

The free ancestral SMTree allows arbitrary root-moving shape maps.  Its
finite-dimensional Ramsey theorem for n=0,k=1 homogenises any finite
colouring of the image of the root, across ALL shape-map choices.

Since an intrinsic parameter-free event has no data beyond its base and
label, this yields one uniform syntactic orbit for each fixed label.
The interpretation of real A-edge carriers as such parameter-free
events is an *extra geometric coding assumption*, not proved here.
-/

namespace StructuralRamsey.Girth

open SuccessorTree
open SuccessorTree.SMTree
open SuccessorTree.FreeAncestral

universe u v

variable {Label : Type u} [Fintype Label] [Nonempty Label]

/-- Every free shape map belongs to the full free ancestral monoid. -/
noncomputable def freeHistoryMMap (arity : ℕ)
    (F : ShapeMap
      (freeSTree (Label := Label) (arity := arity))) :
    MMap (forestHistorySMTree (Label := Label) arity) where
  map := F
  mem := by
    change F ∈ (Set.univ : Set (ShapeMap
      (freeSTree (Label := Label) (arity := arity))))
    exact Set.mem_univ F

/-- Every total free shape map determines a one-level approximation
whose canonical representative has the same image of the root. -/
theorem freeHistoryFiniteRoot_agrees
    (arity : ℕ)
    (F : ShapeMap
      (freeSTree (Label := Label) (arity := arity))) :
    let H := forestHistorySMTree (Label := Label) arity
    let MF := freeHistoryMMap (Label := Label) arity F
    let a : AM H 0 1 :=
      MF.toAM H 0 1 (by
        intro x hx
        omega)
    (a.representative H)
      (rootNode (Label := Label) (arity := arity)) =
      F (rootNode (Label := Label) (arity := arity)) := by
  dsimp
  let H := forestHistorySMTree (Label := Label) arity
  let MF := freeHistoryMMap (Label := Label) arity F
  have hFix : MF.FixesBelow H 0 := by
    intro x hx
    omega
  let a : AM H 0 1 := MF.toAM H 0 1 hFix
  have htop := a.representative_top H
  have hval := congrArg Subtype.val htop
  change (a.representative H).restrictLe H 0 =
    MF.restrictLe H 0 at hval
  have happ := congrFun hval
    ⟨rootNode (Label := Label) (arity := arity), by
      change Node.level (rootNode (Label := Label) (arity := arity)) ≤ 0
      rfl⟩
  exact happ

/-- The root-orbit colour of every pair of free shapes becomes equal
after a single shape reduction, by finite-dimensional Ramsey for 0,1. -/
theorem freeHistoryRootColour_homogeneous
    (arity : ℕ) {κ : Type v} [Fintype κ]
    (χ : Node Label arity → κ) :
    ∃ W : ShapeMap
        (freeSTree (Label := Label) (arity := arity)),
      ∀ F G : ShapeMap
          (freeSTree (Label := Label) (arity := arity)),
        χ (W (F (rootNode (Label := Label) (arity := arity)))) =
          χ (W (G (rootNode (Label := Label) (arity := arity)))) := by
  let H := forestHistorySMTree (Label := Label) arity
  let root : Node Label arity := rootNode
  let col : AM H 0 1 → κ :=
    fun a => χ (a.representative H root)
  obtain ⟨W, hW⟩ :=
    forestHistoryFiniteRamsey (Label := Label)
      arity 0 1 col
  refine ⟨W.1.map, ?_⟩
  intro F G
  let MF : MMap H := freeHistoryMMap (Label := Label) arity F
  let MG : MMap H := freeHistoryMMap (Label := Label) arity G
  have hFFix : MF.FixesBelow H 0 := by
    intro x hx
    omega
  have hGFix : MG.FixesBelow H 0 := by
    intro x hx
    omega
  let a : AM H 0 1 := MF.toAM H 0 1 hFFix
  let b : AM H 0 1 := MG.toAM H 0 1 hGFix
  have haRoot :
      a.representative H root = F root := by
    have htop := a.representative_top H
    have hval := congrArg Subtype.val htop
    change (a.representative H).restrictLe H 0 =
      MF.restrictLe H 0 at hval
    exact congrFun hval ⟨root, by rfl⟩
  have hbRoot :
      b.representative H root = G root := by
    have htop := b.representative_top H
    have hval := congrArg Subtype.val htop
    change (b.representative H).restrictLe H 0 =
      MG.restrictLe H 0 at hval
    exact congrFun hval ⟨root, by rfl⟩
  have hmono := hW a b
  rw [H.shapeActK_one 0 W, H.shapeActK_one 0 W] at hmono
  change
    χ ((H.shapeAct 0 W a).representative H root) =
      χ ((H.shapeAct 0 W b).representative H root) at hmono
  rw [H.shapeAct_representative_agrees 0 W a root (by rfl),
      H.shapeAct_representative_agrees 0 W b root (by rfl)] at hmono
  rw [haRoot, hbRoot] at hmono
  exact hmono

end StructuralRamsey.Girth
