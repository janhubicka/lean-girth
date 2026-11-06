import Girth.TrainTwoCommonEdgeSupremeSwitch
import Girth.TrainFullGirthCopyStrongness
import Mathlib.Tactic

set_option autoImplicit false
set_option Elab.async false

/-!
# Path A: full witness girth makes an ambient pair edge available in both standards

Consider an ACTUAL two-occurrence witness BigCycle with two distinct
designated standard labels and two distinct vertex connectors x,y.
By the BigCycle incidence fields, BOTH vertices lie in the carriers
of BOTH standards. If an ambient physical support edge e contains
x and y, full witness system girth at cutoff at least two already
forces e to belong to BOTH standard edge families (the previously
verified pair-edge ownership theorem).

Thus the checked literal one-short one-keep global plan can be
constructed at EITHER designated target index. No guessed synthetic
copy identity and no re-selection of the original chosen plan is
needed: the theorem constructs genuine alternative plans from
the same physical e, explicitly.

This is a reduction-level target-switching theorem. It does not
decide which source run should be kept, prove a physical source
replacement, address the long/no-pair branch, or establish the
original attached-output SupremeCycleBound. No appendix or TeX.
-/

namespace StructuralRamsey.Girth.OrderOneData

universe v
variable {V E I P : Type v} (D : OrderOneData V E I P)

/-- Under the actual witness FullSystemGirthGT at cutoff >= 2,
any physical pair edge between the two vertex connectors of
a two-standard reduced BigCycle belongs to both standards.
Consequently both standard occurrences admit genuine GLOBAL
simultaneous supreme plans as designated targets. -/
theorem BigCycle.two_standard_pairEdge_switch_both_supreme
    (Z : D.BigCycle 2)
    (hAccept : Z.Acceptable)
    {q : ℕ} (hq : 2 ≤ q)
    (hFull : D.FullSystemGirthGT q)
    (i j : I)
    (hLabel0 : Z.label 0 = Sum.inl i)
    (hLabel1 : Z.label 1 = Sum.inl j)
    (x y : V)
    (hConnector0 : Z.connector 0 = Sum.inl x)
    (hConnector1 : Z.connector 1 = Sum.inl y)
    (e : E)
    (hex : x ∈ D.edgeCarrier e)
    (hey : y ∈ D.edgeCarrier e) :
    ∀ k : Fin 2, Z.HasSupremeAt D k := by
  have hxy : x ≠ y := by
    intro hEq
    have hConnectors : Z.connector (0 : Fin 2) =
        Z.connector (1 : Fin 2) := by
      calc
        Z.connector 0 = Sum.inl x := hConnector0
        _ = Sum.inl y := by rw [hEq]
        _ = Z.connector 1 := hConnector1.symm
    have hIndex : (0 : Fin 2) = 1 :=
      Z.connector_injective hConnectors
    exact (by decide : (0 : Fin 2) ≠ 1) hIndex
  have hix : x ∈ D.copyCarrier i := by
    have h := Z.left_incident (0 : Fin 2)
    simpa [Incident, carrier, hLabel0, hConnector0] using h
  have hjx : x ∈ D.copyCarrier j := by
    have h := Z.right_incident (0 : Fin 2)
    simpa [Incident, carrier, hLabel1, hConnector0, cyclicSucc] using h
  have hiy : y ∈ D.copyCarrier i := by
    have h := Z.right_incident (1 : Fin 2)
    simpa [Incident, carrier, hLabel0, hConnector1, cyclicSucc] using h
  have hjy : y ∈ D.copyCarrier j := by
    have h := Z.left_incident (1 : Fin 2)
    simpa [Incident, carrier, hLabel1, hConnector1] using h
  have hiOwned : e ∈ D.copyEdges i :=
    D.copy_edge_of_pair_of_fullSystemGirth
      q hq hFull i e x y hxy hix hiy hex hey
  have hjOwned : e ∈ D.copyEdges j :=
    D.copy_edge_of_pair_of_fullSystemGirth
      q hq hFull j e x y hxy hjx hjy hex hey
  have hAllDesignated : ∀ k : Fin 2,
      D.designated (Z.label k) := by
    intro k
    fin_cases k
    · simp [hLabel0, designated]
    · simp [hLabel1, designated]
  have hBothOwn : ∀ k : Fin 2,
      e ∈ D.edges (Z.label k) := by
    intro k
    fin_cases k
    · simpa [hLabel0, edges] using hiOwned
    · simpa [hLabel1, edges] using hjOwned
  have hAllInc : ∀ k : Fin 2,
      D.Incident (.inr e) (Z.connector k) := by
    intro k
    fin_cases k
    · simpa [Incident, carrier, hConnector0] using hex
    · simpa [Incident, carrier, hConnector1] using hey
  exact BigCycle.two_both_designated_supreme_of_common_short
    D Z hAccept hFull.1 hAllDesignated e hBothOwn hAllInc

end StructuralRamsey.Girth.OrderOneData
