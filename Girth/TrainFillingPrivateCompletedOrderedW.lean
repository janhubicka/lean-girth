import Girth.TrainFillingPrivateRealUnionOrder
import Girth.TrainFillingColouredOrderedEdgePresentation

set_option Elab.async false

/-!
# The actual ORDERED first-wagon disjoint union for the EHN input

WARNING: the existing firstWagonDisjointUnion is a raw relational
coproduct. Its binary within-colour order relates ONLY vertices
in the same component. That structure need not embed inducedly
into a colouredOrderedEdgeTarget with a total within-colour order
when different F_p contain same-colour vertices (see
TrainFillingPrivateRawOrderObstruction).

The ordered disjoint union W used by the cutoff-two paper is
different: keep ALL k-ary coloured edges componentwise, but
complete the within-colour BINARY order across the disjoint
components using a chosen global predicate-block order.

This file constructs precisely that coloured relational
structure. Because every A-small copy contains the whole
k-ary edge tuple, its support remains inside ONE summand:
adding cross-component order comparisons cannot by itself
create a cross-component A-small edge.

The next EHN adapter must use THIS completed W, rather than
mistaking the raw relational coproduct plus an auxiliary
LinearOrder instance for a complete ordered relational W.
The actual ordered EHN/marked support transfer remains open
until Track 1's selected-family construction is validated.

Candidate Lean source; no kernel compilation/axiom audit.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v
variable {I : Type u} {V P : Type v}

/-- Genuine k-edges of the ordered disjoint union: choose
one first-wagon label p and one complete original physical
edge supported in the induced vertex carrier of F_p.
The target has no cross-summand hyperedges. -/
def taggedFirstWagonEdges
    (oldCarrier : P → Set V)
    (oldEdges : Set (Set V)) :
    Set (Set (FirstWagonUnionVertex oldCarrier)) :=
  {E | ∃ p : P,
    ∃ e : Set {v : V // v ∈ oldCarrier p},
      Subtype.val '' e ∈ oldEdges ∧
      E = (fun x : {v : V // v ∈ oldCarrier p} =>
        (⟨p, x⟩ : FirstWagonUnionVertex oldCarrier)) '' e}

/-- The actual cutoff-two ORDERED W:
  * the same tagged first-wagon vertices;
  * only the original componentwise k-hyperedges;
  * original unary predicate colours;
  * the COMPLETE within-colour binary order relation,
    using one global order extending every F_p order.

The latter is a relational order COMPLETION, not merely a
LinearOrder instance on the raw free-amalgamation coproduct.
No new hyperedge is introduced by the order completion. -/
noncomputable def completedFirstWagonColouredUnion
    [LinearOrder I] [LinearOrder V] [LinearOrder P]
    (k : ℕ)
    (oldEdges : Set (Set V)) (oldColour : V → I)
    (oldCarrier : P → Set V) :
    RelStructure (colouredOrderedEdgeLanguage I k)
      (FirstWagonUnionVertex oldCarrier) := by
  letI : LinearOrder (FirstWagonUnionVertex oldCarrier) :=
    firstWagonUnionOrder oldCarrier oldColour
  exact colouredOrderedEdgeTarget k
    (taggedFirstWagonEdges oldCarrier oldEdges)
    (firstWagonUnionColour oldCarrier oldColour)

/-- Every actual k-hyperedge of the completed W remains
inside ONE genuine first-wagon summand. Adding global
within-predicate order pairs creates NO cross-summand
hyperedge and cannot invalidate the original edge owners. -/
theorem completedFirstWagon_edge_in_one_summand
    [LinearOrder I] [LinearOrder V] [LinearOrder P]
    (k : ℕ)
    (oldEdges : Set (Set V)) (oldColour : V → I)
    (oldCarrier : P → Set V)
    (t : Fin k → FirstWagonUnionVertex oldCarrier)
    (h : (completedFirstWagonColouredUnion k oldEdges
      oldColour oldCarrier).rel (.inl (.inl ())) t) :
    ∃ p : P, ∀ i : Fin k,
      ∃ x : {v : V // v ∈ oldCarrier p},
        t i = (⟨p, x⟩ : FirstWagonUnionVertex oldCarrier) := by
  have hEdge :
      Set.range t ∈ taggedFirstWagonEdges oldCarrier oldEdges := by
    -- The full k-ary relation in the completed structure
    -- is the original componentwise tagged edge family.
    exact (show Function.Injective t ∧
      Set.range t ∈ taggedFirstWagonEdges oldCarrier oldEdges from h).2
  obtain ⟨p, e, _he, ht⟩ := hEdge
  refine ⟨p, ?_⟩
  intro i
  have hMem : t i ∈
      (fun x : {v : V // v ∈ oldCarrier p} =>
        (⟨p, x⟩ : FirstWagonUnionVertex oldCarrier)) '' e := by
    rw [← ht]
    exact ⟨i, rfl⟩
  obtain ⟨x, _hx, hEq⟩ := hMem
  exact ⟨x, hEq.symm⟩

/-- Every genuine k-edge of one induced first wagon
remains an ACTUAL k-edge in the ordered completed W.
The global order completion does not delete local
hyperedges. Combined with
completedFirstWagon_edge_in_one_summand, this gives
the full componentwise hyperedge membership principle.

The incidence conclusion uses the genuine edge relation,
not merely an equivalence of carrier cardinalities. -/
theorem completedFirstWagon_edge_of_local
    [LinearOrder I] [LinearOrder V] [LinearOrder P]
    (k : ℕ)
    (oldEdges : Set (Set V)) (oldColour : V → I)
    (oldCarrier : P → Set V)
    (p : P)
    (t : Fin k → {v : V // v ∈ oldCarrier p})
    (hInj : Function.Injective t)
    (hEdge : Set.range (fun i : Fin k => (t i).1) ∈ oldEdges) :
    (completedFirstWagonColouredUnion k oldEdges
      oldColour oldCarrier).rel (.inl (.inl ()))
        (fun i => (⟨p, t i⟩ : FirstWagonUnionVertex oldCarrier)) := by
  change
    Function.Injective
      (fun i : Fin k =>
        (⟨p, t i⟩ : FirstWagonUnionVertex oldCarrier)) ∧
    Set.range (fun i : Fin k =>
      (⟨p, t i⟩ : FirstWagonUnionVertex oldCarrier))
        ∈ taggedFirstWagonEdges oldCarrier oldEdges
  constructor
  · intro i j hij
    have hVal : (t i).1 = (t j).1 :=
      congrArg
        (fun z : FirstWagonUnionVertex oldCarrier => z.2.1) hij
    exact hInj (Subtype.ext hVal)
  · refine ⟨p, Set.range t, ?_, ?_⟩
    · simpa only [← Set.range_comp'] using hEdge
    · simp only [← Set.range_comp']

/-- Unlike the raw disjoint union, W's binary order relation
really compares same-colour vertices in different first
wagons whenever the chosen global order compares them. -/
theorem completedFirstWagon_cross_order
    [LinearOrder I] [LinearOrder V] [LinearOrder P]
    (k : ℕ)
    (oldEdges : Set (Set V)) (oldColour : V → I)
    (oldCarrier : P → Set V)
    (a b : FirstWagonUnionVertex oldCarrier)
    (hColour : oldColour a.2.1 = oldColour b.2.1)
    (hOrder : @LT.lt (FirstWagonUnionVertex oldCarrier)
      (firstWagonUnionOrder oldCarrier oldColour).toLT a b) :
    (completedFirstWagonColouredUnion k oldEdges
      oldColour oldCarrier).rel (.inr ()) ![a, b] := by
  change oldColour a.2.1 = oldColour b.2.1 ∧
    @LT.lt (FirstWagonUnionVertex oldCarrier)
      (firstWagonUnionOrder oldCarrier oldColour).toLT a b
  exact ⟨hColour, hOrder⟩

end StructuralRamsey.Girth
