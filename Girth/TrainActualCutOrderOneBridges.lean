import Girth.TrainActualCutIndexedBigCycle
import Girth.TrainBigCycleOrderBudget

/-!
# Order-one physical witness cuts: both owner labels have actual bridges

The genuine cut-indexed witness BigCycle is legal independently of A1.
When its order is one it has exactly two occurrences and one connector
of each kind. The order-one witness *bridge bound* then provides a bridge
for BOTH labels. Importantly, this does not require the reduct itself
to have a designated label: for physical edge labels the bridges are
automatic, while designated labels are covered by the usual probe
argument embedded in OrderOneData.both_bridges.

We do NOT assert A1 for an edge-only word. Nor does this provide the
higher-order simultaneous replacement / full cycle transfer.
-/

namespace StructuralRamsey.Girth
namespace OrderOneData

universe v
variable {V E I P : Type v} (D : OrderOneData V E I P)

/-- Exactly two actual labels with a vertex and a wagon connector have
the SAME pair of short physical bridge incidences whenever the
two-cycle numerical order is one. There is no A1 hypothesis. -/
theorem BigCycle.two_both_bridges_of_order_one
    (hBound : D.Bound) (Z : D.BigCycle 2)
    (hOrder : Z.twiceOrder = 2) :
    ∃ (x : V) (p : P),
      ((Z.connector 0 = Sum.inl x ∧ Z.connector 1 = Sum.inr p) ∨
       (Z.connector 0 = Sum.inr p ∧ Z.connector 1 = Sum.inl x)) ∧
      D.Bridge (Z.label 0) x p ∧ D.Bridge (Z.label 1) x p := by
  have hMixed := BigCycle.connectors_mixed_of_order_one D Z hOrder (0 : Fin 2)
  have hLabels : Z.label 0 ≠ Z.label 1 := by
    simpa [cyclicSucc] using Z.adjacent_ne (0 : Fin 2)
  cases h0 : Z.connector (0 : Fin 2) with
  | inl x =>
      cases h1 : Z.connector (1 : Fin 2) with
      | inl y =>
          have hh :
              connectorKind (Z.connector (0 : Fin 2)) =
                connectorKind (Z.connector (cyclicSucc (0 : Fin 2))) := by
            simp [h0, h1, cyclicSucc, connectorKind]
          exact False.elim (hMixed hh)
      | inr p =>
          have haV : x ∈ D.carrier (Z.label 0) := by
            simpa [Incident, h0] using Z.left_incident (0 : Fin 2)
          have hbV : x ∈ D.carrier (Z.label 1) := by
            simpa [Incident, cyclicSucc, h0] using
              Z.right_incident (0 : Fin 2)
          have haP : D.Meets (Z.label 0) p := by
            simpa [Incident, cyclicSucc, h1] using
              Z.right_incident (1 : Fin 2)
          have hbP : D.Meets (Z.label 1) p := by
            simpa [Incident, h1] using Z.left_incident (1 : Fin 2)
          obtain ⟨hb0, hb1⟩ :=
            D.both_bridges hBound (Z.label 0) (Z.label 1)
              x p hLabels haV hbV haP hbP
          exact ⟨x, p, Or.inl ⟨rfl, rfl⟩, hb0, hb1⟩
  | inr p =>
      cases h1 : Z.connector (1 : Fin 2) with
      | inl x =>
          have haV : x ∈ D.carrier (Z.label 0) := by
            simpa [Incident, cyclicSucc, h1] using
              Z.right_incident (1 : Fin 2)
          have hbV : x ∈ D.carrier (Z.label 1) := by
            simpa [Incident, h1] using Z.left_incident (1 : Fin 2)
          have haP : D.Meets (Z.label 0) p := by
            simpa [Incident, h0] using Z.left_incident (0 : Fin 2)
          have hbP : D.Meets (Z.label 1) p := by
            simpa [Incident, cyclicSucc, h0] using
              Z.right_incident (0 : Fin 2)
          obtain ⟨hb0, hb1⟩ :=
            D.both_bridges hBound (Z.label 0) (Z.label 1)
              x p hLabels haV hbV haP hbP
          exact ⟨x, p, Or.inr ⟨rfl, rfl⟩, hb0, hb1⟩
      | inr q =>
          have hh :
              connectorKind (Z.connector (0 : Fin 2)) =
                connectorKind (Z.connector (cyclicSucc (0 : Fin 2))) := by
            simp [h0, h1, cyclicSucc, connectorKind]
          exact False.elim (hMixed hh)

/-- A general numerical order-one BigCycle has just the two mixed
connectors and BOTH label bridges. We record their exact connector
positions and a bridge for every label, not an artificial A1 claim. -/
theorem BigCycle.both_bridges_of_order_one
    (hBound : D.Bound) {n : ℕ} (Z : D.BigCycle n)
    (hOrder : Z.twiceOrder = 2) :
    ∃ (x : V) (p : P),
      (∃ i j : Fin n, i ≠ j ∧
        Z.connector i = Sum.inl x ∧
        Z.connector j = Sum.inr p) ∧
      ∀ k : Fin n, D.Bridge (Z.label k) x p := by
  have hn : n = 2 := BigCycle.length_eq_two_of_order_one D Z hOrder
  subst n
  obtain ⟨x, p, hTypes, hb0, hb1⟩ :=
    BigCycle.two_both_bridges_of_order_one D hBound Z hOrder
  refine ⟨x, p, ?_, ?_⟩
  · rcases hTypes with ⟨h0, h1⟩ | ⟨h0, h1⟩
    · exact ⟨0, 1, by decide, h0, h1⟩
    · exact ⟨1, 0, by decide, h1, h0⟩
  · intro k
    fin_cases k
    · exact hb0
    · exact hb1

end OrderOneData

open StructuralRamsey.RelStructure

universe u v
section ActualCutOneBridges

variable {L : RelLanguage.{u}} {UA VB P X Y I : Type v}
variable (A : RelStructure L UA) (hA : A.Irreducible)
variable (B : RelStructure L VB) (D : RelStructure L P)
variable (C : StructuralRamsey.Partite.System L P X)
variable (family : Set (RelStructure.Embedding B D))
variable (selected : Set (DesignatedCopy B D C family))
variable (e : RelStructure.Embedding A D) (R : RelStructure L Y)
variable (f : I → RelStructure.Embedding
  (C.toRelStructure.induce (activeCarrier A C e.toFunctionEmbedding)) R)
variable {m : ℕ}
variable (T : EdgeTrainLevels (OldACarrierEdge A C.toRelStructure) m)
variable (U : EdgeTrainLevels (OldACarrierEdge A R) m)
variable (hShared : ∀ _i : I, Nonempty (SharedOldACarrierEdge A C.toRelStructure
  (activeCarrier A C e.toFunctionEmbedding)))
variable (hRel : ∀ (ν : Fin (m + 1)) (j : I)
  (p q : SharedOldACarrierEdge A C.toRelStructure
    (activeCarrier A C e.toFunctionEmbedding)),
  T.rel ν p.1 q.1 ↔
    U.rel ν (sharedOldACarrierCoreEmbedding A C.toRelStructure
      (activeCarrier A C e.toFunctionEmbedding) R f j p)
      (sharedOldACarrierCoreEmbedding A C.toRelStructure
        (activeCarrier A C e.toFunctionEmbedding) R f j q))
variable (μ : Fin (m + 1))
local notation "S" => activeCarrier A C e.toFunctionEmbedding
local notation "CoreEdge" => OldACarrierEdge A R
local notation "Out" => attachedSelectedPictureOrderOneData
  A hA B D C family selected e R f T U hShared μ
local notation "GeomAllowed" => selectedOutputGeometricOwnerAllowed
  A hA B D C family selected e R f T U hShared μ
local notation "Wit" => sharedWitnessOrderOneData U μ
  (sharedOldACarrierCoreEmbedding A C.toRelStructure S R f)
  (Subtype.val : CoreEdge → Set Y)

/-- Genuine geometric cut reducts at numerical order one have
two actual vertex/wagon connectors and a physical witness bridge
for EVERY label, assuming only the witness's order-one bridge bound.
The reduction need not itself be acceptable when both labels are edges. -/
theorem attachedSelectedPicture_geometric_cut_orderOne_bridges
    {n : ℕ} (K : (Out).BigCycle n)
    (owner : Fin n → I ⊕ CoreEdge)
    (hAllowed : ∀ k : Fin n, GeomAllowed (K.label k) (owner k))
    (hCuts : 2 ≤ cyclicOwnerChanges owner)
    (hBound : (Wit).Bound)
    (hOrder :
      (attachedSelectedPicture_geometric_cutBigCycle
        A hA B D C family selected e R f T U hShared hRel μ
        K owner hAllowed hCuts).twiceOrder = 2) :
    let Z := attachedSelectedPicture_geometric_cutBigCycle
      A hA B D C family selected e R f T U hShared hRel μ
      K owner hAllowed hCuts
    ∃ (x : Y) (p : Quotient (U.wagonSetoid μ)),
      (∃ i j : Fin (cyclicOwnerChanges owner), i ≠ j ∧
        Z.connector i = Sum.inl x ∧ Z.connector j = Sum.inr p) ∧
      ∀ k, (Wit).Bridge (Z.label k) x p :=
  OrderOneData.BigCycle.both_bridges_of_order_one (Wit) hBound
    (attachedSelectedPicture_geometric_cutBigCycle
      A hA B D C family selected e R f T U hShared hRel μ
      K owner hAllowed hCuts) hOrder

end ActualCutOneBridges
end StructuralRamsey.Girth
