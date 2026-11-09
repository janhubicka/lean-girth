import Girth.TrainTwoWagonFullSystemObstruction
import Girth.TrainShortOnlyPlanGlobal
import Girth.TrainTwoCycleOriginalLocalToGlobal
import Girth.TrainTwoCycleMixedActualBridges

set_option autoImplicit false
set_option Elab.async false

/-!
# The bottom reduced plan needs no full witness bound

At the bottom each wagon is one physical edge, expressed by injectivity
of `parent`. A chosen globally legal reduced supreme plan then has only
short foreign pieces. In the mixed two-label case its bridge is shared by
every incident label. These facts use the chosen plan, not system girth
of the witness that the forest-to-order conversion is constructing.
-/

namespace StructuralRamsey.Girth.OrderOneData
universe v
variable {V E I P : Type v} (D : OrderOneData V E I P)

/-- Singleton-edge wagons cannot support a long piece. -/
theorem BigCycle.longValid_absurd_of_parent_injective
    (hBottom : Function.Injective D.parent)
    {n : ℕ} (Z : D.BigCycle n) (target source : Fin n)
    (e : E) (p : P) (f : E)
    (hLong : Z.LongValid D target source e p f) : False := by
  obtain ⟨_, _, _, _, _, _, hne, hep, hfp, _, _, _⟩ := hLong
  exact hne (hBottom (hep.trans hfp.symm))

/-- Every foreign occurrence of the same fixed bottom supreme plan has a
short piece. The globally valid plan is not replaced by a new local choice. -/
theorem BigCycle.supreme_piece_short_of_parent_injective
    (hBottom : Function.Injective D.parent)
    {n : ℕ} (Z : D.BigCycle n) (target source : Fin n)
    (pieces : Fin n → TrainSupremePiece E P)
    (hPlan : Z.PlanValid D target pieces)
    (hDifferent : Z.label source ≠ Z.label target) :
    ∃ e : E, pieces source = .short e ∧ Z.ShortValid D target source e := by
  have h := (hPlan source).2 hDifferent
  cases hp : pieces source with
  | keep => exact False.elim (by simpa only [hp] using h)
  | short e => exact ⟨e, rfl, by simpa only [hp] using h⟩
  | long e p f =>
      exact False.elim (Z.longValid_absurd_of_parent_injective D
        hBottom target source e p f (by simpa only [hp] using h))

/-- A bridge in a singleton-edge wagon is a bridge of every label meeting
that wagon. No full witness order bound is used. -/
theorem bridge_of_parent_injective
    (hBottom : Function.Injective D.parent)
    (a b : I ⊕ E) (x : V) (p : P)
    (hBridge : D.Bridge a x p) (hMeets : D.Meets b p) :
    D.Bridge b x p := by
  obtain ⟨e, _, hep, hx⟩ := hBridge
  obtain ⟨f, hf, hfp⟩ := hMeets
  have hef : e = f := hBottom (hep.trans hfp.symm)
  subst f
  exact ⟨e, hf, hep, hx⟩

/-- A supreme bottom two-cycle has an actual edge incident with both
connectors. This implication retains the actual chosen reduced plan. -/
theorem BigCycle.two_common_edge_of_bottom_supreme
    (hBottom : Function.Injective D.parent)
    (Z : D.BigCycle 2) (hSupreme : Z.HasSimultaneousSupreme) :
    ∃ e : E, ∀ j : Fin 2, D.Incident (.inr e) (Z.connector j) := by
  obtain ⟨target, _, pieces, hPlan, _⟩ := hSupreme
  let source := cyclicSucc target
  have hDifferent : Z.label source ≠ Z.label target :=
    (Z.adjacent_ne target).symm
  obtain ⟨e, _, hShort⟩ := Z.supreme_piece_short_of_parent_injective
    D hBottom target source pieces hPlan hDifferent
  refine ⟨e, ?_⟩
  intro j
  have hPrev := hShort.2.1
  have hNext := hShort.2.2
  fin_cases target <;> fin_cases j <;>
    simp_all [source, cyclicSucc, trainCyclicPred]

/-- In the bottom mixed two-cycle a chosen supreme plan supplies both
bridges, even when no full witness order bound is available. -/
theorem BigCycle.two_mixed_bridges_of_bottom_supreme
    (hBottom : Function.Injective D.parent)
    (Z : D.BigCycle 2) (hSupreme : Z.HasSimultaneousSupreme)
    (x : V) (p : P)
    (hMixed : (Z.connector 0 = Sum.inl x ∧ Z.connector 1 = Sum.inr p) ∨
      (Z.connector 0 = Sum.inr p ∧ Z.connector 1 = Sum.inl x)) :
    ∀ j : Fin 2, D.Bridge (Z.label j) x p := by
  obtain ⟨e, he⟩ := Z.two_common_edge_of_bottom_supreme D hBottom hSupreme
  have hx : x ∈ D.edgeCarrier e := by
    rcases hMixed with h | h
    · simpa only [h.1, Incident, carrier] using he 0
    · simpa only [h.2, Incident, carrier] using he 1
  have hp : D.parent e = p := by
    have hm : D.Meets (.inr e) p := by
      rcases hMixed with h | h
      · simpa only [h.2, Incident] using he 1
      · simpa only [h.1, Incident] using he 0
    obtain ⟨f, hf, hfp⟩ := hm
    have hfe : f = e := hf
    simpa only [hfe] using hfp
  intro j
  have hm : D.Meets (Z.label j) p := by
    rcases hMixed with h | h
    · simpa only [h.2, Incident] using
        Z.two_every_label_incident_every_connector D j 1
    · simpa only [h.1, Incident] using
        Z.two_every_label_incident_every_connector D j 0
  exact D.bridge_of_parent_injective hBottom (.inr e) (Z.label j) x p
    ⟨e, rfl, hp, hx⟩ hm

/-- The same bridge result on the literal cut-index type of size two. -/
theorem BigCycle.two_mixed_bridges_of_bottom_supreme_of_length_two
    (hBottom : Function.Injective D.parent)
    {n : ℕ} (hn : n = 2) (Z : D.BigCycle n)
    (hSupreme : Z.HasSimultaneousSupreme) (x : V) (p : P)
    (hMixed :
      (Z.connector ⟨0, by omega⟩ = Sum.inl x ∧
       Z.connector ⟨1, by omega⟩ = Sum.inr p) ∨
      (Z.connector ⟨0, by omega⟩ = Sum.inr p ∧
       Z.connector ⟨1, by omega⟩ = Sum.inl x)) :
    ∀ j : Fin n, D.Bridge (Z.label j) x p := by
  subst n
  exact Z.two_mixed_bridges_of_bottom_supreme D hBottom hSupreme x p hMixed

/-- The same common-edge result on the literal cut-index type. -/
theorem BigCycle.two_common_edge_of_bottom_supreme_of_length_two
    (hBottom : Function.Injective D.parent)
    {n : ℕ} (hn : n = 2) (Z : D.BigCycle n)
    (hSupreme : Z.HasSimultaneousSupreme) :
    ∃ e : E, ∀ j : Fin n, D.Incident (.inr e) (Z.connector j) := by
  subst n
  exact Z.two_common_edge_of_bottom_supreme D hBottom hSupreme

/-- In a bottom mixed two-cycle explicit bridges force a designated label:
two physical edge labels would equal the same singleton wagon edge.
Consequently the bridge alternative itself gives a genuine global plan. -/
theorem BigCycle.two_supreme_of_bottom_mixed_bridges
    (hBottom : Function.Injective D.parent)
    (Z : D.BigCycle 2) (x : V) (p : P)
    (hMixed : (Z.connector 0 = Sum.inl x ∧ Z.connector 1 = Sum.inr p) ∨
      (Z.connector 0 = Sum.inr p ∧ Z.connector 1 = Sum.inl x))
    (hBridges : ∀ j : Fin 2, D.Bridge (Z.label j) x p) :
    Z.HasSimultaneousSupreme := by
  have hDesignated : ∃ target : Fin 2, D.designated (Z.label target) := by
    cases h0 : Z.label 0 with
    | inl i => exact ⟨0, by simp only [h0, designated]⟩
    | inr e =>
        cases h1 : Z.label 1 with
        | inl i => exact ⟨1, by simp only [h1, designated]⟩
        | inr f =>
            have he := hBridges 0
            have hf := hBridges 1
            rw [h0] at he
            rw [h1] at hf
            obtain ⟨a, ha, hap, _⟩ := he
            obtain ⟨b, hb, hbp, _⟩ := hf
            have hae : a = e := ha
            have hbf : b = f := hb
            have hef : e = f := by
              apply hBottom
              simpa only [hae, hbf] using hap.trans hbp.symm
            have hne : Z.label (0 : Fin 2) ≠ Z.label (1 : Fin 2) := by
              simpa [cyclicSucc] using Z.adjacent_ne (0 : Fin 2)
            exact False.elim (hne (h0.trans ((congrArg Sum.inr hef).trans h1.symm)))
  obtain ⟨target, hTarget⟩ := hDesignated
  have hAccept : Z.Acceptable := ⟨fun _ => ⟨target, hTarget⟩,
    D.twoCycle_A2 Z, D.twoCycle_A3 Z⟩
  obtain ⟨e, hOwned, hep, hx⟩ := hBridges target
  have hBoth : ∀ j : Fin 2, D.Incident (.inr e) (Z.connector j) := by
    have hV : D.Incident (.inr e) (.inl x) := hx
    have hW : D.Incident (.inr e) (.inr p) := ⟨e, rfl, hep⟩
    intro j
    rcases hMixed with h | h
    · fin_cases j
      · change D.Incident (.inr e) (Z.connector (0 : Fin 2))
        simpa only [h.1] using hV
      · change D.Incident (.inr e) (Z.connector (1 : Fin 2))
        simpa only [h.2] using hW
    · fin_cases j
      · change D.Incident (.inr e) (Z.connector (0 : Fin 2))
        simpa only [h.1] using hW
      · change D.Incident (.inr e) (Z.connector (1 : Fin 2))
        simpa only [h.2] using hV
  apply Z.hasSimultaneousSupreme_of_all_shortValid D hAccept target hTarget
  intro j _
  exact ⟨e, hOwned, hBoth _, hBoth _⟩

/-- Literal cut-index form of the bottom bridge alternative. -/
theorem BigCycle.two_supreme_of_bottom_mixed_bridges_of_length_two
    (hBottom : Function.Injective D.parent)
    {n : ℕ} (hn : n = 2) (Z : D.BigCycle n) (x : V) (p : P)
    (hMixed :
      (Z.connector ⟨0, by omega⟩ = Sum.inl x ∧
       Z.connector ⟨1, by omega⟩ = Sum.inr p) ∨
      (Z.connector ⟨0, by omega⟩ = Sum.inr p ∧
       Z.connector ⟨1, by omega⟩ = Sum.inl x))
    (hBridges : ∀ j : Fin n, D.Bridge (Z.label j) x p) :
    Z.HasSimultaneousSupreme := by
  subst n
  exact Z.two_supreme_of_bottom_mixed_bridges D hBottom x p hMixed hBridges

/-- Two distinct wagon boundaries admit no supreme reduced copy. -/
theorem BigCycle.two_wagon_absurd_of_supreme_of_length_two
    {n : ℕ} (hn : n = 2) (Z : D.BigCycle n)
    (hSupreme : Z.HasSimultaneousSupreme) (p r : P)
    (hp : Z.connector ⟨0, by omega⟩ = Sum.inr p)
    (hr : Z.connector ⟨1, by omega⟩ = Sum.inr r) : False := by
  subst n
  exact Z.two_wagon_no_localSupreme D p r hp hr
    (Z.localSupreme_of_simultaneous D hSupreme)

end StructuralRamsey.Girth.OrderOneData
