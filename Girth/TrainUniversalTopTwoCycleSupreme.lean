import Girth.TrainUniversalTopOrderOne
import Girth.TrainTwoCycleOriginalDesignatedOfLinear
import Girth.TrainTwoCycleOriginalLocalToGlobal
import Mathlib.Tactic

set_option autoImplicit false
set_option Elab.async false

/-!
# Two-occurrence system cycles at the universal parent wagon

At the universal top every physical edge has the same wagon parent.
Every designated selected copy is assumed A-strong and its whole
carrier covered by its own A-edges.

For an acceptable original length-two cycle, physical linearity
forces an ORIGINAL designated occurrence. If its two connectors
are a vertex and a wagon, vertex support supplies an owned short
edge in the unique wagon. If they are two vertices, either some
ambient A-edge joins them, in which case A-strongness makes that
edge owned by the designated label, or no edge joins them, in
which case two distinct owned edges in the universal wagon give
a legal long piece. Two different wagon connectors are impossible
at the universal top.

The checked local-to-global source theorem then supplies a genuine
global ORIGINAL designated supreme plan, including the necessary
global word legality. No local full system girth is assumed.

This is the source-length-two part of a possible structural
FullSystemGirthGT 2 certificate at the universal top; the
three-occurrence order-two case is separate.
-/

namespace StructuralRamsey.Girth.OrderOneData

universe v
variable {V E I P : Type v} (D : OrderOneData V E I P)

/-- The two actual wagon connectors of an original two-cycle cannot
be distinct when all physical edges have the same parent. -/
theorem BigCycle.two_no_double_wagon_of_constant_parent
    (Z : D.BigCycle 2)
    (hConst : ∀ e f : E, D.parent e = D.parent f)
    (p q : P)
    (hp : Z.connector 0 = Sum.inr p)
    (hq : Z.connector 1 = Sum.inr q) : False := by
  have hMeets0 : D.Meets (Z.label 0) p := by
    have h := Z.left_incident 0
    rw [hp] at h
    exact h
  have hMeets1 : D.Meets (Z.label 1) q := by
    have h := Z.left_incident 1
    rw [hq] at h
    exact h
  obtain ⟨a, _ha, hap⟩ := hMeets0
  obtain ⟨b, _hb, hbq⟩ := hMeets1
  have hpq : p = q := hap.symm.trans ((hConst a b).trans hbq)
  have hSame : Z.connector (0 : Fin 2) = Z.connector (1 : Fin 2) := by
    rw [hp, hq, hpq]
  exact (by decide : (0 : Fin 2) ≠ 1) (Z.connector_injective hSame)

/-- Under actual A-strongness of its designated copies and support
coverage of their entire carriers, any original designated label in
a two-cycle has either a genuine owned short piece or a legal owned
long piece through both of the original boundary connectors. -/
theorem BigCycle.two_designated_short_or_long_of_constant_parent
    (Z : D.BigCycle 2)
    (hConst : ∀ e f : E, D.parent e = D.parent f)
    (hCover : ∀ i : I, ∀ x ∈ D.copyCarrier i,
      ∃ e : E, e ∈ D.copyEdges i ∧ x ∈ D.edgeCarrier e)
    (hStrong : ∀ i : I, ∀ e : E,
      ¬ (D.edgeCarrier e ∩ D.copyCarrier i).Subsingleton →
        e ∈ D.copyEdges i)
    (k : Fin 2) (i : I)
    (hLabel : Z.label k = Sum.inl i) :
    D.ShortPiece (Z.label k)
        (Z.connector k) (Z.connector (cyclicSucc k)) ∨
      D.LongPiece (Z.label k)
        (Z.connector k) (Z.connector (cyclicSucc k)) := by
  have hSuccSucc : cyclicSucc (cyclicSucc k) = k := by
    fin_cases k <;> decide
  have hLeft : D.Incident (Z.label k) (Z.connector k) :=
    Z.left_incident k
  have hRight : D.Incident (Z.label k)
      (Z.connector (cyclicSucc k)) := by
    have h := Z.right_incident (cyclicSucc k)
    rw [hSuccSucc] at h
    exact h
  cases hQ : Z.connector k with
  | inl x =>
      cases hR : Z.connector (cyclicSucc k) with
      | inl y =>
          have hx : x ∈ D.copyCarrier i := by
            rw [hLabel, hQ] at hLeft
            exact hLeft
          have hy : y ∈ D.copyCarrier i := by
            rw [hLabel, hR] at hRight
            exact hRight
          by_cases hPair : D.PairEdge x y
          · obtain ⟨edge, heX, heY⟩ := hPair
            have hxy : x ≠ y := by
              intro heq
              have hSame : Z.connector k =
                  Z.connector (cyclicSucc k) := by
                rw [hQ, hR, heq]
              have hIndex := Z.connector_injective hSame
              fin_cases k <;> simp [cyclicSucc] at hIndex
            have hBig : ¬ (D.edgeCarrier edge ∩ D.copyCarrier i).Subsingleton := by
              intro hs
              exact hxy (hs ⟨heX, hx⟩ ⟨heY, hy⟩)
            have hOwned : edge ∈ D.copyEdges i := hStrong i edge hBig
            left
            refine ⟨edge, ?_, ?_, ?_⟩
            · rw [hLabel]
              exact hOwned
            · rw [hQ]
              exact heX
            · rw [hR]
              exact heY
          · obtain ⟨a, ha, hxa⟩ := hCover i x hx
            obtain ⟨b, hb, hyb⟩ := hCover i y hy
            have hab : a ≠ b := by
              intro heq
              apply hPair
              exact ⟨a, hxa, by simpa [heq] using hyb⟩
            right
            refine ⟨x, y, D.parent a, a, b,
              hQ, hR, ?_, ?_, hab, rfl, ?_, hxa, hyb, hPair⟩
            · rw [hLabel]
              exact ha
            · rw [hLabel]
              exact hb
            · exact (hConst b a).symm
      | inr p =>
          have hx : x ∈ D.copyCarrier i := by
            rw [hLabel, hQ] at hLeft
            exact hLeft
          have hMeet : D.Meets (Sum.inl i) p := by
            rw [hLabel, hR] at hRight
            exact hRight
          obtain ⟨edge, he, hxe⟩ := hCover i x hx
          obtain ⟨b, _hb, hbp⟩ := hMeet
          have heP : D.parent edge = p :=
            (hConst edge b).trans hbp
          left
          refine ⟨edge, ?_, ?_, ?_⟩
          · rw [hLabel]
            exact he
          · rw [hQ]
            exact hxe
          · rw [hR]
            exact ⟨edge, rfl, heP⟩
  | inr p =>
      cases hR : Z.connector (cyclicSucc k) with
      | inl x =>
          have hx : x ∈ D.copyCarrier i := by
            rw [hLabel, hR] at hRight
            exact hRight
          have hMeet : D.Meets (Sum.inl i) p := by
            rw [hLabel, hQ] at hLeft
            exact hLeft
          obtain ⟨edge, he, hxe⟩ := hCover i x hx
          obtain ⟨b, _hb, hbp⟩ := hMeet
          have heP : D.parent edge = p :=
            (hConst edge b).trans hbp
          left
          refine ⟨edge, ?_, ?_, ?_⟩
          · rw [hLabel]
            exact he
          · rw [hQ]
            exact ⟨edge, rfl, heP⟩
          · rw [hR]
            exact hxe
      | inr q =>
          have hMeet0 : D.Meets (Sum.inl i) p := by
            rw [hLabel, hQ] at hLeft
            exact hLeft
          have hMeet1 : D.Meets (Sum.inl i) q := by
            rw [hLabel, hR] at hRight
            exact hRight
          obtain ⟨a, _ha, hap⟩ := hMeet0
          obtain ⟨b, _hb, hbq⟩ := hMeet1
          have hpq : p = q := hap.symm.trans ((hConst a b).trans hbq)
          have hSame : Z.connector k =
              Z.connector (cyclicSucc k) := by
            rw [hQ, hR, hpq]
          have hIndex := Z.connector_injective hSame
          fin_cases k <;> simp [cyclicSucc] at hIndex

/-- A globally legal ORIGINAL designated supreme plan for every
acceptable length-two cycle at the universal top, without assuming
any witness system girth. FullSystemGirthGT 2 also has the n=3
order-two case, which is a separate remaining obligation. -/
theorem BigCycle.two_original_supreme_of_constant_parent
    (Z : D.BigCycle 2) (hAccept : Z.Acceptable)
    (hLinear : D.LinearPretrain)
    (hConst : ∀ e f : E, D.parent e = D.parent f)
    (hCover : ∀ i : I, ∀ x ∈ D.copyCarrier i,
      ∃ e : E, e ∈ D.copyEdges i ∧ x ∈ D.edgeCarrier e)
    (hStrong : ∀ i : I, ∀ e : E,
      ¬ (D.edgeCarrier e ∩ D.copyCarrier i).Subsingleton →
        e ∈ D.copyEdges i) :
    Z.HasSimultaneousSupreme := by
  obtain ⟨k, hk⟩ := Z.two_has_designated_of_linear D hAccept hLinear
  cases hLabel : Z.label k with
  | inr e =>
      have hImpossible : False := by
        rw [hLabel] at hk
        exact hk
      exact False.elim hImpossible
  | inl i =>
      have hPiece := Z.two_designated_short_or_long_of_constant_parent
        D hConst hCover hStrong k i hLabel
      have hPred : trainCyclicPred (cyclicSucc k) = k :=
        trainCyclicPred_cyclicSucc_of_two_le
          (by decide : 2 ≤ 2) k
      have hOriginal :
          D.ShortPiece (Z.label k)
              (Z.connector (trainCyclicPred (cyclicSucc k)))
              (Z.connector (cyclicSucc k)) ∨
          D.LongPiece (Z.label k)
              (Z.connector (trainCyclicPred (cyclicSucc k)))
              (Z.connector (cyclicSucc k)) := by
        simpa only [hPred] using hPiece
      exact Z.hasSimultaneousSupreme_of_hasSupremeAt D k
        (Z.two_hasSupremeAt_of_original_local_piece
          D hAccept hLinear k hk hOriginal)

end StructuralRamsey.Girth.OrderOneData
