import Girth.TrainFillingPieceLift
import Girth.TrainWagonStrongInduced
import Girth.TrainShortReplacementNeighbour

/-!
# Circulation Section 13: lifting a contracted block around its retained wagon

Consider an actual filled-cycle block x -- a -- W -- b -- y which was
contracted to an old edge f through x and y. An old supreme replacement of
that occurrence cannot be long because f already joins its boundaries.
Old edge linearity identifies its chosen short edge with f, proving that
f belongs to the old supreme designated copy.

The actual source incidences put x and y in the old wagon W. Old wagon
linearity then puts f in W. Covering supplies target edges under f through
the two boundaries, and the source A2 no-pair-edge clause makes them
distinct. They give TWO short replacements at the original adjacent
occurrences, with the original wagon connector retained between them.

This is the local lifting case (iii). No freshness premise for W is made:
W is already a source connector. Projection, the other simultaneous
replacement blocks, and their full global assembly remain separate.
-/

namespace StructuralRamsey.Girth.TrainFilling

universe v
variable {V I P : Type v}
variable (F : TrainFilling V) (copyCarrier : I → Set V)
variable (copyEdges : I → Set F.OldEdge) (parent : F.OldEdge → P)

local notation "O" => F.oldData copyCarrier copyEdges parent
local notation "H" => F.filledData copyCarrier copyEdges parent

/-- A contracting old edge already joins the two boundaries, excluding
every old long replacement piece between those boundaries. -/
theorem contracting_edge_excludes_oldLong
    (target : I) (f : F.OldEdge) (x y : V)
    (hxf : x ∈ f.1) (hyf : y ∈ f.1) :
    ¬ (O).LongPiece (.inl target) (.inl x) (.inl y) := by
  rintro ⟨u, z, w, a, b, hu, hz, _ha, _hb, _hab,
    _haw, _hbw, _hua, _hzb, hNoPair⟩
  have hux : u = x := (Sum.inl.inj hu).symm
  have hzy : z = y := (Sum.inl.inj hz).symm
  subst u
  subst z
  exact hNoPair ⟨f, hxf, hyf⟩

/-- Old edge linearity identifies the supreme short piece with the
contracting edge. Thus the contracting edge itself belongs to the
designated target, rather than merely having the same two endpoints. -/
theorem contracting_edge_mem_of_oldPiece
    (hLinear : (O).LinearPretrain)
    (target : I) (f : F.OldEdge) (x y : V) (hxy : x ≠ y)
    (hxf : x ∈ f.1) (hyf : y ∈ f.1)
    (hPiece : (O).ShortPiece (.inl target) (.inl x) (.inl y) ∨
      (O).LongPiece (.inl target) (.inl x) (.inl y)) :
    f ∈ copyEdges target := by
  have hShort := hPiece.resolve_right
    (F.contracting_edge_excludes_oldLong copyCarrier copyEdges parent target f x y hxf hyf)
  obtain ⟨g, hg, hxg, hyg⟩ := hShort
  change g ∈ copyEdges target at hg
  change x ∈ g.1 at hxg
  change y ∈ g.1 at hyg
  have hfg : f = g := by
    by_contra hne
    have hInter : (f.1 ∩ g.1).Subsingleton := hLinear.1 f g hne
    exact hxy (hInter ⟨hxf, hxg⟩ ⟨hyf, hyg⟩)
  rw [hfg]
  exact hg

/-- An actual contracted source block lifts to two distinct target short
pieces around the SAME already-retained wagon. The original designated
target index is kept explicit for the subsequent simultaneous plan.

Old edge and wagon linearity, source acceptability and actual incidence
derive the ownership, wagon membership and distinctness conclusions.
None of those conclusions is inserted as a new opaque premise. -/
theorem contractedBlock_short_lifts
    (hLinear : (O).LinearPretrain)
    {n : ℕ} (C : (H).BigCycle n) (hAccept : C.Acceptable) (hn : 3 ≤ n)
    (target : I) (k i : Fin n) (hk : C.label k = Sum.inl target)
    (a b : F.NewEdge)
    (ha : C.label i = Sum.inr a)
    (hb : C.label (cyclicSucc i) = Sum.inr b)
    (x y : V) (w : P)
    (hx : C.connector (trainCyclicPred i) = Sum.inl x)
    (hw : C.connector i = Sum.inr w)
    (hy : C.connector (cyclicSucc i) = Sum.inl y)
    (f : F.OldEdge) (hxf : x ∈ f.1) (hyf : y ∈ f.1)
    (hPiece : (O).ShortPiece (.inl target) (.inl x) (.inl y) ∨
      (O).LongPiece (.inl target) (.inl x) (.inl y)) :
    f ∈ copyEdges target ∧ parent f = w ∧
    ∃ a' b' : F.NewEdge,
      F.cover a' = f ∧ F.cover b' = f ∧ a' ≠ b' ∧
      (H).parent a' = w ∧ (H).parent b' = w ∧
      C.ShortValid H k i a' ∧ C.ShortValid H k (cyclicSucc i) b' := by
  have hPredSucc := trainCyclicPred_ne_cyclicSucc_of_three_le hn i
  have hxy : x ≠ y := by
    intro heq
    apply hPredSucc
    apply C.connector_injective
    exact hx.trans ((congrArg Sum.inl heq).trans hy.symm)
  have hxa : x ∈ a.1 := by
    have h := C.right_incident (trainCyclicPred i)
    rw [cyclicSucc_trainCyclicPred_of_two_le C.length_ge_two i, ha, hx] at h
    change x ∈ a.1 at h
    exact h
  have hyb : y ∈ b.1 := by
    have h := C.left_incident (cyclicSucc i)
    rw [hb, hy] at h
    change y ∈ b.1 at h
    exact h
  have haw : parent (F.cover a) = w := by
    have h := C.left_incident i
    rw [ha, hw] at h
    obtain ⟨e, he, hep⟩ := h
    change e = a at he
    subst e
    change parent (F.cover a) = w at hep
    exact hep
  have hbw : parent (F.cover b) = w := by
    have h := C.right_incident i
    rw [hb, hw] at h
    obtain ⟨e, he, hep⟩ := h
    change e = b at he
    subst e
    change parent (F.cover b) = w at hep
    exact hep
  have hxW : (H).WagonVertex w x := ⟨a, haw, hxa⟩
  have hyW : (H).WagonVertex w y := ⟨b, hbw, hyb⟩
  have hxOldW : (O).WagonVertex w x := ⟨F.cover a, haw, F.contained a hxa⟩
  have hyOldW : (O).WagonVertex w y := ⟨F.cover b, hbw, F.contained b hyb⟩
  have hParent := (O).parent_eq_of_two_vertices_in_wagon hLinear
    f w x y hxf hyf hxOldW hyOldW hxy
  change parent f = w at hParent
  have hOwned := F.contracting_edge_mem_of_oldPiece copyCarrier copyEdges parent
    hLinear target f x y hxy hxf hyf hPiece
  have hNoPair : ¬ (H).PairEdge x y :=
    hAccept.2.1.2 i w x y hw hx hy hPredSucc hxW hyW
  obtain ⟨a', hCoverA, hxa'⟩ := F.covering f x hxf
  obtain ⟨b', hCoverB, hyb'⟩ := F.covering f y hyf
  have hNe : a' ≠ b' := by
    intro heq
    apply hNoPair
    refine ⟨a', hxa', ?_⟩
    change y ∈ a'.1
    rw [heq]
    exact hyb'
  have hParentA : parent (F.cover a') = w := by
    rw [hCoverA]
    exact hParent
  have hParentB : parent (F.cover b') = w := by
    rw [hCoverB]
    exact hParent
  refine ⟨hOwned, hParent, a', b', hCoverA, hCoverB, hNe,
    hParentA, hParentB, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_⟩
    · rw [hk]
      change F.cover a' ∈ copyEdges target
      rw [hCoverA]
      exact hOwned
    · rw [hx]
      change x ∈ a'.1
      exact hxa'
    · rw [hw]
      change ∃ e, e = a' ∧ parent (F.cover e) = w
      exact ⟨a', rfl, hParentA⟩
  · refine ⟨?_, ?_, ?_⟩
    · rw [hk]
      change F.cover b' ∈ copyEdges target
      rw [hCoverB]
      exact hOwned
    · rw [trainCyclicPred_cyclicSucc_of_two_le C.length_ge_two i, hw]
      change ∃ e, e = b' ∧ parent (F.cover e) = w
      exact ⟨b', rfl, hParentB⟩
    · rw [hy]
      change y ∈ b'.1
      exact hyb'

end StructuralRamsey.Girth.TrainFilling
