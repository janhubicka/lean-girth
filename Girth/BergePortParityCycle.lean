import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Tactic

/-!
# A nonzero even-degree finite graph contains a cycle

This is the generic parity-to-cycle ingredient needed for the
converse direction of the exact short Berge-port boundary criterion.
In the intended application the graph is an *incidence-edge chain*
formed by taking the symmetric difference of the selected witness
paths. Its boundary is zero; the side-change port vertex makes
the chain nonzero; hence a physical short cycle exists.

The present module proves ONLY the finite graph-theoretic last
step. It does not assume or state the as-yet-unverified
signed-incidence-chain construction or a new Ramsey arrow.

Mathlib supplies sum_degrees_eq_twice_card_edges and
exists_isCycle_of_card_le; combining them avoids a second
recursive proof of the finite forest leaf lemma.
-/

namespace StructuralRamsey.Girth
namespace BergePortParity

universe v

/-- A finite nonempty graph with all vertex degrees positive and
even must contain a simple cycle. -/
theorem exists_cycle_of_positive_even_degree
    {V : Type v} [Finite V] (G : SimpleGraph V)
    [DecidableRel G.Adj]
    (hV : Nonempty V)
    (hPositive : ∀ v : V, 0 < G.degree v)
    (hEven : ∀ v : V, Even (G.degree v)) :
    ∃ (v : V) (p : G.Walk v v), p.IsCycle := by
  classical
  letI : Nonempty V := hV
  letI : Fintype V := Fintype.ofFinite V
  letI : Fintype G.edgeSet := Fintype.ofFinite _
  have hTwo : ∀ v : V, 2 ≤ G.degree v := by
    intro v
    obtain ⟨k, hk⟩ := hEven v
    have hp : 0 < G.degree v := hPositive v
    omega
  have hSum : 2 * Fintype.card V ≤ ∑ v : V, G.degree v := by
    calc
      2 * Fintype.card V = ∑ _v : V, (2 : ℕ) := by simp
      _ ≤ ∑ v : V, G.degree v := by
        apply Finset.sum_le_sum
        intro v hv
        exact hTwo v
  have hHand : ∑ v : V, G.degree v = 2 * G.edgeFinset.card :=
    G.sum_degrees_eq_twice_card_edges
  have hEdges : G.edgeFinset.card = G.edgeSet.ncard := by
    calc
      G.edgeFinset.card = Fintype.card G.edgeSet :=
        G.edgeFinset_card
      _ = G.edgeSet.ncard := Set.fintypeCard_eq_ncard _
  have hCard : Nat.card V ≤ G.edgeSet.ncard := by
    rw [Nat.card_eq_fintype_card, ← hEdges]
    omega
  exact G.exists_isCycle_of_card_le hCard

/-- Any finite graph with a nonempty support and even degree at
every nonisolated vertex has a cycle. Isolated vertices are harmless:
restrict to the support and use the preceding degree-sum argument.
This is exactly the form a nonzero finite mod-two incidence
1-cycle will require. -/
theorem exists_cycle_of_nonempty_even_support
    {V : Type v} [Finite V] (G : SimpleGraph V)
    [DecidableRel G.Adj]
    (hSupp : G.support.Nonempty)
    (hEven : ∀ v ∈ G.support, Even (G.degree v)) :
    ∃ (v : V) (p : G.Walk v v), p.IsCycle := by
  classical
  letI : Fintype V := Fintype.ofFinite V
  obtain ⟨x, hx⟩ := hSupp
  letI : Nonempty G.support := ⟨⟨x, hx⟩⟩
  letI : Fintype G.support := Fintype.ofFinite _
  let J : SimpleGraph G.support := G.induce G.support
  letI : DecidableRel J.Adj := Classical.decRel _
  have hPositive : ∀ v : G.support, 0 < J.degree v := by
    intro v
    change 0 < (G.induce G.support).degree v
    rw [G.degree_induce_support]
    exact (G.degree_pos_iff_mem_support v.1).2 v.2
  have hEvenJ : ∀ v : G.support, Even (J.degree v) := by
    intro v
    change Even ((G.induce G.support).degree v)
    rw [G.degree_induce_support]
    exact hEven v.1 v.2
  obtain ⟨v, p, hp⟩ :=
    exists_cycle_of_positive_even_degree J
      (show Nonempty G.support from inferInstance)
      hPositive hEvenJ
  let inclusion : J →g G := {
    toFun := fun v => v.1
    map_rel' := by
      intro u w huw
      exact huw
  }
  refine ⟨v.1, p.map inclusion, ?_⟩
  exact hp.map (by intro u w huw; exact Subtype.ext huw)

end BergePortParity
end StructuralRamsey.Girth
