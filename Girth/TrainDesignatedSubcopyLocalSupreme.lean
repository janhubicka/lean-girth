import Girth.TrainShortOnlyPlanGlobal

/-!
# Circulation Section 13: the target inside one component is supreme

After the scattering argument has placed a cycle inside one component,
only that component's target label and its ambient edges remain. The
geometric assumptions used here are exactly the last paragraph of the
manuscript: intersections of distinct component wagons lie in the target,
the target is strongly induced in the component, and its edges cover each
target vertex in every component wagon containing that vertex.

Acceptability forces two adjacent edge occurrences at a vertex to have
different parent wagons at length at least three. Hence every vertex
connector lies in the target. At length two the retained target occurrence
gives this directly. Strong inducedness and pointwise wagon coverage then
give short replacements, and the existing short-only theorem constructs
their globally legal simultaneous word.

This proves the final local component step. It does not assume or prove
that the original enlarged cycle has already been moved into one component;
that localization and the pullback to the original target cycle remain
separate obligations. No ambient edge or wagon is removed.
-/

namespace StructuralRamsey.Girth.OrderOneData

universe v
variable {V E I P : Type v} (D : OrderOneData V E I P)

/-- In an acceptable cycle, a wagon contains at most two distinct vertex
connector positions, whether or not it occurs as a wagon connector. -/
theorem BigCycle.not_wagon_vertex_three_distinct
    {n : ℕ} (C : D.BigCycle n) (hAccept : C.Acceptable)
    (p : P) (i j k : Fin n) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hi : C.InWagonAt p i) (hj : C.InWagonAt p j)
    (hk : C.InWagonAt p k) : False := by
  have notTwo (a b : Fin n) (hi' : i = a ∨ i = b)
      (hj' : j = a ∨ j = b) (hk' : k = a ∨ k = b) : False := by
    rcases hi' with hi' | hi' <;>
      rcases hj' with hj' | hj' <;>
      rcases hk' with hk' | hk' <;> subst_vars <;> contradiction
  by_cases hOccurs : ∃ t : Fin n, C.connector t = Sum.inr p
  · obtain ⟨t, ht⟩ := hOccurs
    exact notTwo (trainCyclicPred t) (cyclicSucc t)
      (hAccept.2.1.1 t p ht i hi)
      (hAccept.2.1.1 t p ht j hj)
      (hAccept.2.1.1 t p ht k hk)
  · obtain ⟨t, ht⟩ := hAccept.2.2 p (by
      intro s hs
      exact hOccurs ⟨s, hs⟩)
    exact notTwo t (cyclicSucc t) (ht i hi) (ht j hj) (ht k hk)

/-- Two actual edges adjacent at a vertex of an acceptable cycle of
length at least three belong to different wagons. No linearity or
system-girth hypothesis is required for this consequence of A2--A3. -/
theorem BigCycle.edge_parents_ne_at_vertex
    {n : ℕ} (C : D.BigCycle n) (hAccept : C.Acceptable) (hn : 3 ≤ n)
    (i : Fin n) (e f : E) (x : V)
    (he : C.label i = Sum.inr e)
    (hf : C.label (cyclicSucc i) = Sum.inr f)
    (hx : C.connector i = Sum.inl x) : D.parent e ≠ D.parent f := by
  intro hParent
  have hiNext : i ≠ cyclicSucc i := by
    intro h
    exact C.adjacent_ne i (congrArg C.label h)
  have hPrevI : trainCyclicPred i ≠ i := by
    intro h
    have hs := cyclicSucc_trainCyclicPred_of_two_le C.length_ge_two i
    rw [h] at hs
    exact hiNext hs.symm
  have hPrevNext := trainCyclicPred_ne_cyclicSucc_of_three_le hn i
  have hPrev : D.Incident (.inr e) (C.connector (trainCyclicPred i)) := by
    have h := C.right_incident (trainCyclicPred i)
    rw [cyclicSucc_trainCyclicPred_of_two_le C.length_ge_two i, he] at h
    exact h
  have hHereE : D.Incident (.inr e) (C.connector i) := by
    simpa only [he] using C.left_incident i
  have hHereF : D.Incident (.inr f) (C.connector i) := by
    simpa only [hf] using C.right_incident i
  have hNext : D.Incident (.inr f) (C.connector (cyclicSucc i)) := by
    simpa only [hf] using C.left_incident (cyclicSucc i)
  cases hBefore : C.connector (trainCyclicPred i) with
  | inl y =>
      cases hAfter : C.connector (cyclicSucc i) with
      | inl z =>
          have hyE : y ∈ D.edgeCarrier e := by simpa only [hBefore] using hPrev
          have hxE : x ∈ D.edgeCarrier e := by simpa only [hx] using hHereE
          have hzF : z ∈ D.edgeCarrier f := by simpa only [hAfter] using hNext
          exact C.not_wagon_vertex_three_distinct D hAccept (D.parent e)
            (trainCyclicPred i) i (cyclicSucc i) hPrevI hPrevNext hiNext
            ⟨y, hBefore, e, rfl, hyE⟩
            ⟨x, hx, e, rfl, hxE⟩
            ⟨z, hAfter, f, hParent.symm, hzF⟩
      | inr p =>
          have hfp : D.parent f = p := by
            have h := hNext
            rw [hAfter] at h
            obtain ⟨a, ha, hap⟩ := h
            have haf : a = f := ha
            simpa only [haf] using hap
          have hNextE : D.Incident (.inr e) (C.connector (cyclicSucc i)) := by
            rw [hAfter]
            exact ⟨e, rfl, hParent.trans hfp⟩
          exact C.not_edge_incident_three_distinct D hAccept e
            (trainCyclicPred i) i (cyclicSucc i) hPrevI hPrevNext hiNext
            hPrev hHereE hNextE
  | inr p =>
      have hep : D.parent e = p := by
        have h := hPrev
        rw [hBefore] at h
        obtain ⟨a, ha, hap⟩ := h
        have hae : a = e := ha
        simpa only [hae] using hap
      have hPrevF : D.Incident (.inr f) (C.connector (trainCyclicPred i)) := by
        rw [hBefore]
        exact ⟨f, rfl, hParent.symm.trans hep⟩
      exact C.not_edge_incident_three_distinct D hAccept f
        (trainCyclicPred i) i (cyclicSucc i) hPrevI hPrevNext hiNext
        hPrevF hHereF hNext

/-- The concrete component geometry used by the final scattering step.
The edge family specifies the component, while the ambient incidence
system and its entire wagon partition stay unchanged. -/
structure ComponentTargetGeometry (target : I) where
  componentEdges : Set E
  inter_wagon_intersections : ∀ e ∈ componentEdges, ∀ f ∈ componentEdges,
    D.parent e ≠ D.parent f → ∀ x,
    x ∈ D.edgeCarrier e → x ∈ D.edgeCarrier f → x ∈ D.copyCarrier target
  strong_target : ∀ e ∈ componentEdges, ∀ x y,
    x ≠ y → x ∈ D.edgeCarrier e → y ∈ D.edgeCarrier e →
    x ∈ D.copyCarrier target → y ∈ D.copyCarrier target → e ∈ D.copyEdges target
  pointwise_cover : ∀ e ∈ componentEdges, ∀ x,
    x ∈ D.edgeCarrier e → x ∈ D.copyCarrier target →
    ∃ f, f ∈ D.copyEdges target ∧ D.parent f = D.parent e ∧ x ∈ D.edgeCarrier f

/-- Once an acceptable cycle lies in one component and retains its target,
every vertex connector belongs to that target. The two-occurrence case
uses the retained target directly, not the length-at-least-three lemma. -/
theorem BigCycle.component_target_contains_vertex_connectors
    {n : ℕ} (C : D.BigCycle n) (hAccept : C.Acceptable)
    (target : I) (G : D.ComponentTargetGeometry target)
    (k : Fin n) (hk : C.label k = Sum.inl target)
    (hLabels : ∀ j : Fin n, C.label j = Sum.inl target ∨
      ∃ e, C.label j = Sum.inr e ∧ e ∈ G.componentEdges)
    (i : Fin n) (x : V) (hx : C.connector i = Sum.inl x) :
    x ∈ D.copyCarrier target := by
  have hLeft := C.left_incident i
  have hRight := C.right_incident i
  rw [hx] at hLeft hRight
  by_cases hn : 3 ≤ n
  · rcases hLabels i with hTarget | ⟨e, he, hE⟩
    · simpa only [hTarget] using hLeft
    · rcases hLabels (cyclicSucc i) with hTarget | ⟨f, hf, hF⟩
      · simpa only [hTarget] using hRight
      · exact G.inter_wagon_intersections e hE f hF
          (C.edge_parents_ne_at_vertex D hAccept hn i e f x he hf hx) x
          (by simpa only [he] using hLeft)
          (by simpa only [hf] using hRight)
  · have hnTwo : n = 2 := by have h := C.length_ge_two; omega
    subst n
    have hIndex : k = i ∨ k = cyclicSucc i := by
      fin_cases i <;> fin_cases k <;> simp [cyclicSucc]
    rcases hIndex with hIndex | hIndex
    · rw [hIndex] at hk
      simpa only [hk] using hLeft
    · rw [hIndex] at hk
      simpa only [hk] using hRight

/-- The target of a localized component cycle is genuinely supreme:
all short replacements are constructed, including their global legality.
No local-piece-to-global shortcut and no ambient pruning is used. -/
theorem BigCycle.hasSupremeAt_of_component_target
    {n : ℕ} (C : D.BigCycle n) (hAccept : C.Acceptable)
    (target : I) (G : D.ComponentTargetGeometry target)
    (k : Fin n) (hk : C.label k = Sum.inl target)
    (hLabels : ∀ j : Fin n, C.label j = Sum.inl target ∨
      ∃ e, C.label j = Sum.inr e ∧ e ∈ G.componentEdges) :
    C.HasSupremeAt D k := by
  have hVertices := C.component_target_contains_vertex_connectors D hAccept
    target G k hk hLabels
  apply C.hasSupremeAt_of_all_shortValid D hAccept k
    (by simp only [hk, designated])
  intro j hne
  obtain ⟨e, he, hE⟩ : ∃ e, C.label j = Sum.inr e ∧ e ∈ G.componentEdges := by
    rcases hLabels j with hTarget | hEdge
    · exact False.elim (hne (hTarget.trans hk.symm))
    · exact hEdge
  have hPrev : D.Incident (.inr e) (C.connector (trainCyclicPred j)) := by
    have h := C.right_incident (trainCyclicPred j)
    rw [cyclicSucc_trainCyclicPred_of_two_le C.length_ge_two j, he] at h
    exact h
  have hHere : D.Incident (.inr e) (C.connector j) := by
    simpa only [he] using C.left_incident j
  have hPrevNe : trainCyclicPred j ≠ j := by
    intro h
    have hs := cyclicSucc_trainCyclicPred_of_two_le C.length_ge_two j
    rw [h] at hs
    exact C.adjacent_ne j (congrArg C.label hs.symm)
  have hConnNe : C.connector (trainCyclicPred j) ≠ C.connector j :=
    fun h => hPrevNe (C.connector_injective h)
  cases hBefore : C.connector (trainCyclicPred j) with
  | inl x =>
      have hxE : x ∈ D.edgeCarrier e := by simpa only [hBefore] using hPrev
      have hxT := hVertices (trainCyclicPred j) x hBefore
      cases hAfter : C.connector j with
      | inl y =>
          have hyE : y ∈ D.edgeCarrier e := by simpa only [hAfter] using hHere
          have hyT := hVertices j y hAfter
          have hxy : x ≠ y := by
            intro h
            exact hConnNe (hBefore.trans ((congrArg Sum.inl h).trans hAfter.symm))
          refine ⟨e, ?_, hPrev, hHere⟩
          simpa only [hk, edges] using G.strong_target e hE x y hxy hxE hyE hxT hyT
      | inr p =>
          have hep : D.parent e = p := by
            have h := hHere
            rw [hAfter] at h
            obtain ⟨a, ha, hap⟩ := h
            have hae : a = e := ha
            simpa only [hae] using hap
          obtain ⟨f, hf, hParent, hxf⟩ := G.pointwise_cover e hE x hxE hxT
          refine ⟨f, ?_, ?_, ?_⟩
          · simpa only [hk, edges] using hf
          · simpa only [hBefore] using hxf
          · rw [hAfter]
            exact ⟨f, rfl, hParent.trans hep⟩
  | inr p =>
      have hep : D.parent e = p := by
        have h := hPrev
        rw [hBefore] at h
        obtain ⟨a, ha, hap⟩ := h
        have hae : a = e := ha
        simpa only [hae] using hap
      cases hAfter : C.connector j with
      | inl y =>
          have hyE : y ∈ D.edgeCarrier e := by simpa only [hAfter] using hHere
          have hyT := hVertices j y hAfter
          obtain ⟨f, hf, hParent, hyf⟩ := G.pointwise_cover e hE y hyE hyT
          refine ⟨f, ?_, ?_, ?_⟩
          · simpa only [hk, edges] using hf
          · rw [hBefore]
            exact ⟨f, rfl, hParent.trans hep⟩
          · simpa only [hAfter] using hyf
      | inr q =>
          have heq : D.parent e = q := by
            have h := hHere
            rw [hAfter] at h
            obtain ⟨a, ha, haq⟩ := h
            have hae : a = e := ha
            simpa only [hae] using haq
          exact False.elim (hConnNe
            (hBefore.trans ((congrArg Sum.inr (hep.symm.trans heq)).trans hAfter.symm)))

end StructuralRamsey.Girth.OrderOneData
