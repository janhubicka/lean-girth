import Girth.TrainDesignatedSubcopyComponents
import Girth.TrainDesignatedSubcopyRefinement

/-!
# Circulation Section 13: system girth passes to designated subcopies

Enlarge the target labels of an acceptable cycle to their old designated
parents, choose an old supreme occurrence, and refine its genuine legal
replacement output back to the original target labels. The old plan's
edge ownership puts every output label in the chosen old parent. Actual
component disjointness then confines the output to the retained target's
component. Strong inducedness, inter-wagon intersections and pointwise
wagon coverage make that target supreme, and arbitrary replacement
pullback returns its supremeness to the original cycle.

The old output is refined at every length, including two. No resulting
cycle, component confinement, inserted-wagon freshness or target-girth
bound is assumed. All ambient edges and physical wagons are unchanged.
The hypotheses on the component geometry remain explicit, as in the
manuscript's scattering lemma; constructing a scattering with those
properties is a separate task.
-/

namespace StructuralRamsey.Girth.OrderOneData.DesignatedSubcopyFamily

universe v
variable {V E I J P : Type v}
variable {D : OrderOneData V E I P} (S : DesignatedSubcopyFamily D J)

/-- A supreme plan in the enlarged cycle contributes only targets with
the chosen old parent and actual edges belonging to that parent. This is
an assertion about every entry of the literal target-labelled word. -/
theorem resultWord_parent_contained_of_enlarged_plan
    {n : ℕ} (C : S.target.BigCycle n) (k : Fin n) (target : J)
    (hk : C.label k = Sum.inl target)
    (pieces : Fin n → TrainSupremePiece E P)
    (hPlan : (S.enlargeCycle C).PlanValid D k pieces)
    (a : J ⊕ E) (q : V ⊕ P)
    (hMem : (a, q) ∈ C.resultWord S.target pieces) :
    match (generalizing := false) a with
    | .inl j => S.containingCopy j = S.containingCopy target
    | .inr e => e ∈ D.copyEdges (S.containingCopy target) := by
  obtain ⟨block, hBlock, hEntry⟩ := List.mem_flatten.mp hMem
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hBlock
  cases hp : pieces i with
  | keep =>
      have hEq : (a, q) = (C.label i, C.connector i) := by
        simpa only [BigCycle.pieceWord, hp, List.mem_singleton] using hEntry
      have hLabels := (S.enlargeCycle C).label_eq_supreme_of_keep
        D k i pieces hPlan hp
      change S.enlargeLabel (C.label i) = S.enlargeLabel (C.label k) at hLabels
      rw [hk] at hLabels
      have ha : a = C.label i := congrArg Prod.fst hEq
      rw [ha]
      cases hi : C.label i with
      | inl j =>
          rw [hi] at hLabels
          exact Sum.inl.inj hLabels
      | inr e =>
          rw [hi] at hLabels
          cases hLabels
  | short e =>
      have hEq : (a, q) = (Sum.inr e, C.connector i) := by
        simpa only [BigCycle.pieceWord, hp, List.mem_singleton] using hEntry
      have hEdge := ((S.enlargeCycle C).shortValid_of_piece_eq_short
        D k i pieces hPlan e hp).1
      change e ∈ D.edges (S.enlargeLabel (C.label k)) at hEdge
      rw [hk] at hEdge
      have ha : a = Sum.inr e := congrArg Prod.fst hEq
      rw [ha]
      exact hEdge
  | long e p f =>
      obtain ⟨x, y, hBefore, hAfter, he, hf, hDistinct,
        hPe, hPf, hXe, hYf, hNoPair⟩ :=
        (S.enlargeCycle C).longValid_of_piece_eq_long
          D k i pieces hPlan e f p hp
      change e ∈ D.edges (S.enlargeLabel (C.label k)) at he
      change f ∈ D.edges (S.enlargeLabel (C.label k)) at hf
      rw [hk] at he hf
      have hCases :
          (a, q) = (Sum.inr e, Sum.inr p) ∨
          (a, q) = (Sum.inr f, C.connector i) := by
        simpa [BigCycle.pieceWord, hp] using hEntry
      rcases hCases with hEq | hEq
      · have ha : a = Sum.inr e := congrArg Prod.fst hEq
        rw [ha]
        exact he
      · have ha : a = Sum.inr f := congrArg Prod.fst hEq
        rw [ha]
        exact hf

/-- The old plan's long pieces give exactly the physical geometry needed
for arbitrary replacement pullback in the target system. -/
theorem localLongA2Geometry_of_enlarged_plan
    {n : ℕ} (C : S.target.BigCycle n) (k : Fin n)
    (pieces : Fin n → TrainSupremePiece E P)
    (hPlan : (S.enlargeCycle C).PlanValid D k pieces) :
    C.LocalLongA2Geometry S.target pieces := by
  intro i e f p hp
  obtain ⟨x, y, hBefore, hAfter, he, hf, hDistinct,
    hPe, hPf, hXe, hYf, hNoPair⟩ :=
    (S.enlargeCycle C).longValid_of_piece_eq_long
      D k i pieces hPlan e f p hp
  exact ⟨x, y, hBefore, hAfter, ⟨e, hPe, hXe⟩,
    ⟨f, hPf, hYf⟩, hNoPair⟩

/-- An indexed supreme old parent yields a genuinely supreme target
occurrence of the original cycle. The literal output and its component
confinement are constructed, not supplied as extra hypotheses. -/
theorem supreme_target_of_enlarged_supreme
    (K : S.ComponentDecomposition)
    {n : ℕ} (C : S.target.BigCycle n)
    (hAccept : C.Acceptable) (hLinear : D.LinearPretrain)
    (k : Fin n) (target : J) (hk : C.label k = Sum.inl target)
    (hSupreme : (S.enlargeCycle C).HasSupremeAt D k)
    (G : S.target.ComponentTargetGeometry target)
    (hComponentEdges : G.componentEdges = K.componentEdges target) :
    ∃ kC : Fin n, C.label kC = Sum.inl target ∧
      C.HasSupremeAt S.target kC := by
  obtain ⟨hDesignated, pieces, hPlan, hGlobal⟩ := hSupreme
  obtain ⟨m, B, hWord⟩ :=
    S.planProducesBigCycle_of_enlargeCycle C pieces hGlobal
  have hParentLabels : ∀ t : Fin m,
      match B.label t with
      | .inl j => S.containingCopy j = S.containingCopy target
      | .inr e => e ∈ D.copyEdges (S.containingCopy target) := by
    intro t
    apply S.resultWord_parent_contained_of_enlarged_plan
      C k target hk pieces hPlan (B.label t) (B.connector t)
    rw [← hWord]
    exact List.mem_ofFn.mpr ⟨t, rfl⟩
  have hKeep : pieces k = .keep := (hPlan k).1 rfl
  have hRetained : (Sum.inl target, C.connector k) ∈
      C.resultWord S.target pieces := by
    apply List.mem_flatten.mpr
    refine ⟨C.pieceWord S.target k (pieces k),
      List.mem_ofFn.mpr ⟨k, rfl⟩, ?_⟩
    simp only [BigCycle.pieceWord, hKeep, hk, List.mem_singleton]
  rw [← hWord] at hRetained
  obtain ⟨kB, hkB⟩ := List.mem_ofFn.mp hRetained
  exact K.supreme_of_parent_contained_replacement C B hAccept hLinear
    pieces (S.localLongA2Geometry_of_enlarged_plan C k pieces hPlan)
    hWord (S.containingCopy target) hParentLabels target G hComponentEdges
    kB (congrArg Prod.fst hkB)

/-- The full circulation system-girth bound passes from the old
designated family to its component targets under the manuscript's
scattering geometry, with global simultaneous supremeness at all lengths. -/
theorem fullSystemGirthGT_of_components
    (K : S.ComponentDecomposition)
    (G : ∀ target : J, S.target.ComponentTargetGeometry target)
    (hComponentEdges : ∀ target : J,
      (G target).componentEdges = K.componentEdges target)
    {g : ℕ} (hGirth : D.FullSystemGirthGT g) :
    S.target.FullSystemGirthGT g := by
  refine ⟨hGirth.1, ?_⟩
  intro n C hAccept hOrder
  obtain ⟨k, target, hk, hSupreme⟩ :=
    S.enlargeCycle_supreme_parent_of_fullSystemGirth hGirth C hAccept hOrder
  obtain ⟨kC, hLabel, hTargetSupreme⟩ :=
    S.supreme_target_of_enlarged_supreme K C hAccept hGirth.1
      k target hk hSupreme (G target) (hComponentEdges target)
  exact C.hasSimultaneousSupreme_of_hasSupremeAt S.target kC hTargetSupreme

end StructuralRamsey.Girth.OrderOneData.DesignatedSubcopyFamily
