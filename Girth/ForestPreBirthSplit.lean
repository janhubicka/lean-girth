import Girth.ForestSuccessorBridge
import SuccessorTree.FreeAncestralMonoid
import SuccessorTree.FreeAncestralGapShape
import SuccessorTree.ShapeEvents
import Mathlib.Tactic

/-!
# Splitting a carrier before its birth

The original two-copy proposal split *after* the moving carrier was born,
which need not change its intrinsic birth event.  This module shows the
correct syntactic alternative in the free ancestral tree: split a private
neutral prefix u, strictly before the base of the carrier-birth event.
Two one-gap maps then send every later event base in the u cone to
disjoint target cones. Every further shape map preserves that
distinction on intrinsic events.

This theorem does not construct the missing geometrically evaluated
linear/pairwise-clean universal reservoir, nor does it show agreement
with an old front outside the private cone.
-/

namespace StructuralRamsey.Girth

open SuccessorTree
open SuccessorTree.FreeAncestral

universe u

variable {Label : Type u} {arity : ℕ}
variable [Fintype Label] [Nonempty Label]

/-- Necessity of splitting the carrier ORIGIN rather than only a later
history endpoint. If two shape maps agree on the base and intrinsic
parameters of the same birth event, then their transported event is
identical, regardless of how the maps stretch the event's child. -/
theorem sameBirthEvent_of_fixed_inputs
    (F G : ShapeMap
      (freeSTree (Label := Label) (arity := arity)))
    (e : IntrinsicEvent
      (freeSTree (Label := Label) (arity := arity)))
    (hbase : F e.base = G e.base)
    (hparams : e.params.map F = e.params.map G) :
    F.mapEvent e = G.mapEvent e := by
  cases e with
  | mk base params label hex =>
      dsimp at hbase hparams
      change
        { base := F base, params := params.map F, label := label,
          has_child := _ } =
        { base := G base, params := params.map G, label := label,
          has_child := _ }
      cases hbase
      cases hparams
      rfl

/-- Once the birth inputs are frozen, a further successor reduction
cannot manufacture two different birth events. -/
theorem sameBirthEvent_after_reduction
    (F G W : ShapeMap
      (freeSTree (Label := Label) (arity := arity)))
    (e : IntrinsicEvent
      (freeSTree (Label := Label) (arity := arity)))
    (hbase : F e.base = G e.base)
    (hparams : e.params.map F = e.params.map G) :
    W.mapEvent (F.mapEvent e) = W.mapEvent (G.mapEvent e) :=
  congrArg W.mapEvent (sameBirthEvent_of_fixed_inputs F G e hbase hparams)

/-- First neutral insertion: always choose c0 at the selected gap level. -/
noncomputable def preBirthZero
    (m : ℕ) (c0 : Label) :
    ShapeMap (freeSTree (Label := Label) (arity := arity)) :=
  oneGapShapeMap m
    (fun _ => ⟨c0, emptyParamTuple arity m⟩)

/-- Second neutral insertion: choose c1 only at the designated private
history, and use the same c0 choice everywhere else. -/
noncomputable def preBirthOne
    (m : ℕ) (h0 : History Label arity m) (c0 c1 : Label) :
    ShapeMap (freeSTree (Label := Label) (arity := arity)) := by
  classical
  exact oneGapShapeMap m
    (fun h => if h = h0 then
      ⟨c1, emptyParamTuple arity m⟩
    else
      ⟨c0, emptyParamTuple arity m⟩)

theorem preBirthZero_at_gap
    (m : ℕ) (h0 : History Label arity m) (c0 : Label) :
    preBirthZero (arity := arity) m c0
        (⟨m, h0⟩ : Node Label arity) =
      child (⟨m, h0⟩ : Node Label arity)
        (emptyParamTuple arity m) c0 := by
  simp [preBirthZero, oneGapShapeMap_apply, gapNode_at_level]

theorem preBirthOne_at_gap
    (m : ℕ) (h0 : History Label arity m) (c0 c1 : Label) :
    preBirthOne (arity := arity) m h0 c0 c1
        (⟨m, h0⟩ : Node Label arity) =
      child (⟨m, h0⟩ : Node Label arity)
        (emptyParamTuple arity m) c1 := by
  classical
  simp [preBirthOne, oneGapShapeMap_apply, gapNode_at_level]

/-- The two test embeddings agree on every old-front node below
the private insertion level.  The stronger locality assertion for nodes
above the gap but outside the private cone is handled separately. -/
theorem preBirth_maps_agree_below_gap
    (m : ℕ) (h0 : History Label arity m) (c0 c1 : Label)
    (x : Node Label arity) (hx : x.level < m) :
    preBirthZero (arity := arity) m c0 x =
      preBirthOne (arity := arity) m h0 c0 c1 x := by
  have hz :
      preBirthZero (arity := arity) m c0 x = x := by
    change gapNode m
      (fun _ => ⟨c0, emptyParamTuple arity m⟩) x = x
    exact gapNode_eq_self_of_lt m _ hx
  have ho :
      preBirthOne (arity := arity) m h0 c0 c1 x = x := by
    classical
    change gapNode m
      (fun h : History Label arity m =>
        if h = h0 then ⟨c1, emptyParamTuple arity m⟩
        else ⟨c0, emptyParamTuple arity m⟩) x = x
    exact gapNode_eq_self_of_lt m _ hx
  exact hz.trans ho.symm

/-- Splitting strictly before a marked carrier's birth separates
all its future event bases, and not merely a padded endpoint. -/
theorem preBirthSplit_descendant_ne
    (m : ℕ) (h0 : History Label arity m)
    (c0 c1 : Label) (hne : c0 ≠ c1)
    (a : Node Label arity)
    (hua : (⟨m, h0⟩ : Node Label arity) ≤ a) :
    preBirthZero (arity := arity) m c0 a ≠
      preBirthOne (arity := arity) m h0 c0 c1 a := by
  let x : Node Label arity := ⟨m, h0⟩
  let D0 := preBirthZero (arity := arity) m c0
  let D1 := preBirthOne (arity := arity) m h0 c0 c1
  have h0Eq :
      D0 x = child x (emptyParamTuple arity m) c0 :=
    preBirthZero_at_gap m h0 c0
  have h1Eq :
      D1 x = child x (emptyParamTuple arity m) c1 :=
    preBirthOne_at_gap m h0 c0 c1
  have hdist : D0 x ≠ D1 x := by
    intro heq
    have heqChild :
        child x (emptyParamTuple arity m) c0 =
          child x (emptyParamTuple arity m) c1 := by
      calc
        child x (emptyParamTuple arity m) c0 = D0 x := h0Eq.symm
        _ = D1 x := heq
        _ = child x (emptyParamTuple arity m) c1 := h1Eq
    exact hne (child_eq_data heqChild).2
  have h0le : D0 x ≤ D0 a := D0.map_le_of_le hua
  have h1le : D1 x ≤ D1 a := D1.map_le_of_le hua
  have hlev : LevelTree.lev (D0 x) = LevelTree.lev (D1 x) := by
    change (D0 x).level = (D1 x).level
    rw [h0Eq, h1Eq]
    rfl
  intro heq
  have h0le' : D0 x ≤ D1 a := by
    rw [← heq]
    exact h0le
  rcases LevelTree.comparable_below h0le' h1le with h | h
  · exact hdist (LevelTree.same_level_of_le h hlev)
  · exact hdist ((LevelTree.same_level_of_le h hlev.symm).symm)

/-- Any later reduction preserves the distinction of moving
carrier *birth events*, provided their source event bases descend
from the private split node. -/
theorem preBirthSplit_event_ne_after
    (m : ℕ) (h0 : History Label arity m)
    (c0 c1 : Label) (hne : c0 ≠ c1)
    (e : IntrinsicEvent
      (freeSTree (Label := Label) (arity := arity)))
    (hua : (⟨m, h0⟩ : Node Label arity) ≤ e.base)
    (W : ShapeMap
      (freeSTree (Label := Label) (arity := arity))) :
    W.mapEvent
        ((preBirthZero (arity := arity) m c0).mapEvent e) ≠
      W.mapEvent
        ((preBirthOne (arity := arity) m h0 c0 c1).mapEvent e) := by
  have hbase :=
    preBirthSplit_descendant_ne
      (arity := arity) m h0 c0 c1 hne e.base hua
  intro heq
  have hbefore := W.mapEvent_injective heq
  apply hbase
  have hbaseEq :=
    congrArg (fun z : IntrinsicEvent
      (freeSTree (Label := Label) (arity := arity)) => z.base) hbefore
  exact hbaseEq

end StructuralRamsey.Girth
