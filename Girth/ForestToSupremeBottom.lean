import Girth.Forest
import Girth.TrainShortOnlyPlanGlobal

/-!
# Bottom forest geometry and genuine two-occurrence supreme plans

At the bottom level each wagon is one physical edge.  The forest intersection
axiom then turns two common, distinct connectors into one common short edge.
This includes mixed order-one reducts which need not satisfy A1.  The resulting
short edge constructs a globally legal supreme plan on every two-occurrence
cycle; it is not merely a local-piece or assumed order-bound interface.

Only physical incidence assumptions are recorded below.  In particular,
linearity is a property of ambient edges, parent injectivity says that we are
at the bottom level, and no supremeness or girth conclusion is an assumption.
-/

namespace StructuralRamsey.Girth.OrderOneData

universe v
variable {V E I P : Type v} (D : OrderOneData V E I P)

/-- Physical geometry at the bottom train coordinate. -/
structure BottomForestGeometry : Prop where
  edge_subset : ∀ (a : I ⊕ E) (e : E), e ∈ D.edges a →
    D.edgeCarrier e ⊆ D.carrier a
  edge_nontrivial : ∀ e : E, (D.edgeCarrier e).Nontrivial
  edge_linear : ∀ e f : E, e ≠ f →
    (D.edgeCarrier e ∩ D.edgeCarrier f).Subsingleton
  parent_injective : Function.Injective D.parent

variable (H : D.BottomForestGeometry)

/-- The physical support piece of a designated label or a genuine edge label. -/
def bottomForestPiece (a : I ⊕ E) : HypergraphPiece V where
  carrier := D.carrier a
  edges := D.edgeCarrier '' D.edges a
  edge_subset_carrier := by
    rintro s ⟨e, he, rfl⟩
    exact H.edge_subset a e he

/-- A nontrivial physical edge cannot be properly contained in another edge. -/
theorem BottomForestGeometry.edge_eq_of_subset
    (H : D.BottomForestGeometry)
    {e f : E} (h : D.edgeCarrier e ⊆ D.edgeCarrier f) : e = f := by
  by_contra hne
  obtain ⟨x, hx, y, hy, hxy⟩ := H.edge_nontrivial e
  exact hxy (H.edge_linear e f hne ⟨hx, h hx⟩ ⟨hy, h hy⟩)

/-- Two distinct common vertices in an allowed forest intersection lie on one
physical edge belonging to both members. -/
theorem BottomForestGeometry.common_edge_of_two_vertices
    {a b : I ⊕ E}
    (hAllowed : AllowedIntersection (D.bottomForestPiece H a)
      (D.bottomForestPiece H b))
    {x y : V} (hxy : x ≠ y)
    (hxa : x ∈ D.carrier a) (hxb : x ∈ D.carrier b)
    (hya : y ∈ D.carrier a) (hyb : y ∈ D.carrier b) :
    ∃ e : E, e ∈ D.edges a ∧ e ∈ D.edges b ∧
      x ∈ D.edgeCarrier e ∧ y ∈ D.edgeCarrier e := by
  rcases hAllowed with hs | ⟨s, hsA, hsB, hInter⟩
  · exact (hxy (hs ⟨hxa, hxb⟩ ⟨hya, hyb⟩)).elim
  · obtain ⟨e, he, hes⟩ := hsA
    obtain ⟨f, hf, hfs⟩ := hsB
    have hef : e = f := H.edge_eq_of_subset D (by rw [hes, hfs])
    subst f
    refine ⟨e, he, hf, ?_, ?_⟩
    · rw [hes, ← hInter]
      exact ⟨hxa, hxb⟩
    · rw [hes, ← hInter]
      exact ⟨hya, hyb⟩

/-- If both members contain an edge, that whole edge is their allowed
intersection.  Uncovered ambient edges are not removed. -/
theorem BottomForestGeometry.inter_eq_of_common_edge
    {a b : I ⊕ E}
    (hAllowed : AllowedIntersection (D.bottomForestPiece H a)
      (D.bottomForestPiece H b))
    {e : E} (hea : e ∈ D.edges a) (heb : e ∈ D.edges b) :
    D.carrier a ∩ D.carrier b = D.edgeCarrier e := by
  have hSub : D.edgeCarrier e ⊆ D.carrier a ∩ D.carrier b :=
    fun _ hx => ⟨H.edge_subset a e hea hx, H.edge_subset b e heb hx⟩
  rcases hAllowed with hs | ⟨s, hsA, _, hInter⟩
  · obtain ⟨x, hx, y, hy, hxy⟩ := H.edge_nontrivial e
    exact (hxy (hs (hSub hx) (hSub hy))).elim
  · obtain ⟨f, _, hfs⟩ := hsA
    have hef : e = f := H.edge_eq_of_subset D (by
      intro x hx
      rw [hfs, ← hInter]
      exact hSub hx)
    simpa [bottomForestPiece, hef, hfs] using hInter

/-- At the bottom level equal wagon labels identify the physical edge. -/
theorem BottomForestGeometry.common_edge_of_meets
    (H : D.BottomForestGeometry)
    {a b : I ⊕ E} {p : P} (ha : D.Meets a p) (hb : D.Meets b p) :
    ∃ e : E, e ∈ D.edges a ∧ e ∈ D.edges b ∧ D.parent e = p := by
  obtain ⟨e, he, hep⟩ := ha
  obtain ⟨f, hf, hfp⟩ := hb
  have hef : e = f := H.parent_injective (hep.trans hfp.symm)
  subst f
  exact ⟨e, he, hf, hep⟩

/-- The order-one forest bridge needs no acceptability/A1 premise. -/
theorem BottomForestGeometry.both_bridges_of_allowed
    {a b : I ⊕ E}
    (hAllowed : AllowedIntersection (D.bottomForestPiece H a)
      (D.bottomForestPiece H b))
    {x : V} {p : P}
    (hxa : x ∈ D.carrier a) (hxb : x ∈ D.carrier b)
    (hma : D.Meets a p) (hmb : D.Meets b p) :
    D.Bridge a x p ∧ D.Bridge b x p := by
  obtain ⟨e, hea, heb, hep⟩ := H.common_edge_of_meets D hma hmb
  have hxe : x ∈ D.edgeCarrier e := by
    rw [← H.inter_eq_of_common_edge D hAllowed hea heb]
    exact ⟨hxa, hxb⟩
  exact ⟨⟨e, hea, hep, hxe⟩, ⟨e, heb, hep, hxe⟩⟩

/-- Every two distinct connectors shared by allowed bottom members have one
common short edge.  The two-wagon case is ruled out by edge linearity. -/
theorem BottomForestGeometry.common_short_edge
    {a b : I ⊕ E}
    (hAllowed : AllowedIntersection (D.bottomForestPiece H a)
      (D.bottomForestPiece H b))
    {q r : V ⊕ P} (hqr : q ≠ r)
    (haq : D.Incident a q) (har : D.Incident a r)
    (hbq : D.Incident b q) (hbr : D.Incident b r) :
    ∃ e : E, e ∈ D.edges a ∧ e ∈ D.edges b ∧
      D.Incident (.inr e) q ∧ D.Incident (.inr e) r := by
  cases q with
  | inl x =>
      cases r with
      | inl y =>
          have hxy : x ≠ y := fun h => hqr (congrArg Sum.inl h)
          exact H.common_edge_of_two_vertices D hAllowed hxy haq hbq har hbr
      | inr p =>
          obtain ⟨e, hea, heb, hep⟩ := H.common_edge_of_meets D har hbr
          have hxe : x ∈ D.edgeCarrier e := by
            rw [← H.inter_eq_of_common_edge D hAllowed hea heb]
            exact ⟨haq, hbq⟩
          exact ⟨e, hea, heb, hxe, ⟨e, rfl, hep⟩⟩
  | inr p =>
      cases r with
      | inl x =>
          obtain ⟨e, hea, heb, hep⟩ := H.common_edge_of_meets D haq hbq
          have hxe : x ∈ D.edgeCarrier e := by
            rw [← H.inter_eq_of_common_edge D hAllowed hea heb]
            exact ⟨har, hbr⟩
          exact ⟨e, hea, heb, ⟨e, rfl, hep⟩, hxe⟩
      | inr s =>
          obtain ⟨e, hea, heb, hep⟩ := H.common_edge_of_meets D haq hbq
          obtain ⟨f, hfa, hfb, hfs⟩ := H.common_edge_of_meets D har hbr
          have hef : e = f := H.edge_eq_of_subset D (by
            rw [← H.inter_eq_of_common_edge D hAllowed hfa hfb]
            exact fun _ hx => ⟨H.edge_subset a e hea hx,
              H.edge_subset b e heb hx⟩)
          exact (hqr (congrArg Sum.inr (hep.symm.trans
            ((congrArg D.parent hef).trans hfs)))).elim

/-- A common physical edge in two distinct labels ensures one is designated. -/
theorem designated_or_of_common_edge
    {a b : I ⊕ E} (hab : a ≠ b) {e : E}
    (hea : e ∈ D.edges a) (heb : e ∈ D.edges b) :
    D.designated a ∨ D.designated b := by
  cases a with
  | inl i => exact Or.inl trivial
  | inr f =>
      cases b with
      | inl i => exact Or.inr trivial
      | inr g =>
          have hef : e = f := hea
          have heg : e = g := heb
          exact (hab (congrArg Sum.inr (hef.symm.trans heg))).elim

/-- Every two-occurrence cycle carried by an allowed bottom intersection has
a genuine simultaneous supreme copy.  Acceptability is proved, not assumed:
the common short edge supplies the designated occurrence required by A1. -/
theorem BigCycle.hasSimultaneousSupreme_of_two_bottom_forest
    (C : D.BigCycle 2)
    (hAllowed : AllowedIntersection (D.bottomForestPiece H (C.label 0))
      (D.bottomForestPiece H (C.label 1))) :
    C.HasSimultaneousSupreme := by
  have h01 : (0 : Fin 2) ≠ 1 := by decide
  have hq : C.connector 0 ≠ C.connector 1 :=
    fun h => h01 (C.connector_injective h)
  have hr0 : D.Incident (C.label 0) (C.connector 1) := by
    simpa [cyclicSucc] using C.right_incident 1
  have hr1 : D.Incident (C.label 1) (C.connector 0) := by
    simpa [cyclicSucc] using C.right_incident 0
  obtain ⟨e, he0, he1, heq, her⟩ := H.common_short_edge D hAllowed hq
    (C.left_incident 0) hr0 hr1 (C.left_incident 1)
  have hne : C.label 0 ≠ C.label 1 := by
    simpa [cyclicSucc] using C.adjacent_ne 0
  have hDes := D.designated_or_of_common_edge hne he0 he1
  have hAccept : C.Acceptable := by
    refine ⟨?_, D.twoCycle_A2 C, D.twoCycle_A3 C⟩
    intro _
    rcases hDes with h | h
    · exact ⟨0, h⟩
    · exact ⟨1, h⟩
  rcases hDes with h | h
  · apply C.hasSimultaneousSupreme_of_all_shortValid D hAccept 0 h
    intro j hj
    fin_cases j
    · exact (hj rfl).elim
    · refine ⟨e, he0, ?_, her⟩
      simpa [trainCyclicPred] using heq
  · apply C.hasSimultaneousSupreme_of_all_shortValid D hAccept 1 h
    intro j hj
    fin_cases j
    · refine ⟨e, he1, ?_, heq⟩
      simpa [trainCyclicPred] using her
    · exact (hj rfl).elim

end StructuralRamsey.Girth.OrderOneData
