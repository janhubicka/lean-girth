import Girth.TrainFullGirthCopyStrongness
import Girth.TrainBigCycleOrderBudget
import Mathlib.Tactic

set_option autoImplicit false
set_option Elab.async false

/-!
# Path A: a physical pair edge gives ShortValid at both two-standard targets

This lemma works in the GENUINE two-occurrence big-cycle syntax.
Assume the two actual labelled occurrences are designated standards
i and j, and both actual connectors are distinct vertices x and y.

A real physical A-edge e containing x,y is forced by
FullSystemGirthGT at cutoff at least two to belong to the
physical edge families of BOTH designated standards: both copy
carriers contain both x,y by the four literal BigCycle incidences.

Consequently the SAME physical e is a ShortValid witness with
either designated occurrence chosen as target and the other as
the replaced occurrence. No existential replacement witness is
reselected. This is a source-ready interface used by the two-cut
singleton short transfer: after choosing the forward singleton
orientation, use the opposite standard as target.

No physical ORIGINAL-source replacement, no global output
supremeness, no nonedge/long or mixed order-one bridge claim.
No appendix or manuscript edits.
-/

namespace StructuralRamsey.Girth.OrderOneData

universe v
variable {V E I P : Type v} (D : OrderOneData V E I P)

/-- If a real physical support edge joins the two vertex connectors
of a two-standard reduced witness cycle, then it is a valid SHORT
piece at the other occurrence for EITHER designated supreme target.
Both physical edge-ownership claims follow from the existing full
system-girth pair-probe theorem, not from any false overlap identity. -/
theorem BigCycle.two_vertex_pairEdge_shortValid_both_targets
    (Z : D.BigCycle 2)
    (q : ℕ) (hq : 2 ≤ q)
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
    ∀ k : Fin 2, Z.ShortValid D k (cyclicSucc k) e := by
  have hxy : x ≠ y := by
    intro heq
    have hSame : Z.connector (0 : Fin 2) = Z.connector 1 := by
      calc
        Z.connector 0 = Sum.inl x := hConnector0
        _ = Sum.inl y := by rw [heq]
        _ = Z.connector 1 := hConnector1.symm
    exact (by decide : (0 : Fin 2) ≠ 1)
      (Z.connector_injective hSame)
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
  intro k
  fin_cases k
  · change e ∈ D.edges (Z.label (0 : Fin 2)) ∧
      D.Incident (Sum.inr e) (Z.connector (0 : Fin 2)) ∧
      D.Incident (Sum.inr e) (Z.connector (1 : Fin 2))
    exact ⟨by simpa [hLabel0, edges] using hiOwned,
      by simpa [Incident, carrier, hConnector0] using hex,
      by simpa [Incident, carrier, hConnector1] using hey⟩
  · change e ∈ D.edges (Z.label (1 : Fin 2)) ∧
      D.Incident (Sum.inr e) (Z.connector (1 : Fin 2)) ∧
      D.Incident (Sum.inr e) (Z.connector (0 : Fin 2))
    exact ⟨by simpa [hLabel1, edges] using hjOwned,
      by simpa [Incident, carrier, hConnector1] using hey,
      by simpa [Incident, carrier, hConnector0] using hex⟩


/-- The same result with an arbitrary indexed cut count known to be
two. Its conclusion is indexed by the non-target cut, so the actual
source-restriction API can use target = pred(cut) literally. -/
theorem BigCycle.two_vertex_pairEdge_shortValid_for_each_cut
    {c : ℕ} (hc : c = 2)
    (Z : D.BigCycle c)
    (q : ℕ) (hq : 2 ≤ q)
    (hFull : D.FullSystemGirthGT q)
    (i j : I)
    (hLabel0 : Z.label ⟨0, by omega⟩ = Sum.inl i)
    (hLabel1 : Z.label ⟨1, by omega⟩ = Sum.inl j)
    (x y : V)
    (hConnector0 : Z.connector ⟨0, by omega⟩ = Sum.inl x)
    (hConnector1 : Z.connector ⟨1, by omega⟩ = Sum.inl y)
    (e : E) (hex : x ∈ D.edgeCarrier e)
    (hey : y ∈ D.edgeCarrier e) :
    ∀ cut : Fin c, Z.ShortValid D (trainCyclicPred cut) cut e := by
  subst c
  have hBoth := BigCycle.two_vertex_pairEdge_shortValid_both_targets
    D Z q hq hFull i j hLabel0 hLabel1 x y
    hConnector0 hConnector1 e hex hey
  intro cut
  fin_cases cut
  · simpa [trainCyclicPred, cyclicSucc] using hBoth (1 : Fin 2)
  · simpa [trainCyclicPred, cyclicSucc] using hBoth (0 : Fin 2)

end StructuralRamsey.Girth.OrderOneData
