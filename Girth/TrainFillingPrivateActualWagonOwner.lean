import Girth.TrainWagonClassRestriction
import Girth.TrainFillingPrivateRealUnionLocalCoverage

set_option Elab.async false

/-!
# The ACTUAL original train quotient gives every first-wagon owner

The direct cutoff-two first-wagon construction does not invent
an owner function on original A-support edges. It uses the
genuine wagon quotient of the ORIGINAL EdgeTrainLevels T
at its first-wagon level.

For every actual old edge e its owner is its quotient class
[e]_mu, and the vertex carrier of that class is the true
union of the complete physical carriers of all equivalent
edges. Hence each edge is contained in its owner's carrier;
conversely EVERY vertex of an actual wagon carrier lies
in an actual edge whose quotient owner is that wagon.

This discharges the former hOwnerCarrier and hWagonCover
data assumed by originalFirstWagonLocalCoverage, without
any old-output girth or arbitrary edge-ownership map.

At cutoff two specialize mu to the original first-wagon
index 1 (with height >=2), and use original labelled
W_1(T)-girth>2 for the separate wagon-CARRIER linearity.
The universal top and equality cut are not conflated.

Candidate source until local Lean compilation/axiom audit.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v
variable {E V : Type v}

/-- The actual wagon-owner label of a physical source edge
at a fixed horizontal cut: its own quotient class. -/
def EdgeTrainLevels.wagonClassOwner
    {m : ℕ} (T : EdgeTrainLevels E m)
    (μ : Fin (m + 1)) (e : E) :
    Quotient (T.wagonSetoid μ) :=
  Quotient.mk (T.wagonSetoid μ) e

/-- Every old physical edge is contained in its COMPLETE
actual owner wagon carrier, for every horizontal cut,
without any additional assumption on the train. -/
theorem EdgeTrainLevels.edge_subset_ownerWagonCarrier
    {m : ℕ} (T : EdgeTrainLevels E m)
    (edges : E → Set V) (μ : Fin (m + 1))
    (e : E) :
    edges e ⊆
      T.wagonClassCarrier edges μ (T.wagonClassOwner μ e) := by
  intro z hz
  change ∃ f : E, T.rel μ e f ∧ z ∈ edges f
  exact ⟨e, (T.equivalent μ).refl e, hz⟩

/-- EVERY vertex in a true quotient wagon belongs to
a complete OLD physical edge with that same owner label.
The quotient remembers labelled wagons even if carriers
of different wagons happen to coincide. -/
theorem EdgeTrainLevels.ownerEdge_covers_wagonVertex
    {m : ℕ} (T : EdgeTrainLevels E m)
    (edges : E → Set V) (μ : Fin (m + 1))
    (q : Quotient (T.wagonSetoid μ))
    (v : V)
    (hv : v ∈ T.wagonClassCarrier edges μ q) :
    ∃ e : E, T.wagonClassOwner μ e = q ∧ v ∈ edges e := by
  induction q using Quotient.inductionOn with
  | h a =>
    change v ∈ T.wagonCarrier edges μ a at hv
    obtain ⟨e, hae, hve⟩ := hv
    refine ⟨e, ?_, hve⟩
    exact Quotient.sound ((T.equivalent μ).symm hae)

/-- Specialize the actual quotient owner/copy carrier to the
source relational A-support edge type. This produces precisely
the local A-coverage of each induced wagon F_p required
by the real disjoint-union W, with NO independent owner,
old-carrier containment, or old-wagon coverage hypotheses.

A separate first-wagon carrier LINEARITY hypothesis is
needed to prove that no foreign induced A-edge is present;
it is not needed for vertex coverage itself. -/
theorem EdgeTrainLevels.inducedWagon_Acovered
    {L : RelLanguage.{u}} {UA : Type v}
    (A : RelStructure L UA) (D : RelStructure L V)
    {m : ℕ}
    (T : EdgeTrainLevels
      {e : Set V // e ∈ supportCopies A D} m)
    (μ : Fin (m + 1)) :
    ∀ (p : Quotient (T.wagonSetoid μ))
        (x : {v : V //
          v ∈ T.wagonClassCarrier
            (fun e : {e : Set V // e ∈ supportCopies A D} => e.1)
              μ p}),
      ∃ a : Embedding A
        (D.induce
          (T.wagonClassCarrier
            (fun e : {e : Set V // e ∈ supportCopies A D} => e.1)
              μ p)),
        x ∈ copyCarrier a := by
  let edges : {e : Set V // e ∈ supportCopies A D} → Set V :=
    fun e => e.1
  let oldCarrier :
      Quotient (T.wagonSetoid μ) → Set V :=
    T.wagonClassCarrier edges μ
  let owner : {e : Set V // e ∈ supportCopies A D} →
      Quotient (T.wagonSetoid μ) :=
    T.wagonClassOwner μ
  have hOwnerCarrier : ∀ e,
      e.1 ⊆ oldCarrier (owner e) := by
    intro e
    exact T.edge_subset_ownerWagonCarrier edges μ e
  have hWagonCover :
      ∀ p (x : {v : V // v ∈ oldCarrier p}),
        ∃ e : {e : Set V // e ∈ supportCopies A D},
          owner e = p ∧ x.1 ∈ e.1 := by
    intro p x
    exact T.ownerEdge_covers_wagonVertex edges μ p x.1 x.2
  exact originalFirstWagonLocalCoverage
    A D oldCarrier owner hOwnerCarrier hWagonCover


/-- A real nonempty old physical edge family, whose edges
all contain a vertex, gives a real vertex in the tagged
disjoint union of quotient wagon carriers at EVERY cut.
This is exactly the hNonempty input of the EHN W
selected-copy construction, not an arbitrary new point. -/
theorem EdgeTrainLevels.wagonUnion_nonempty
    {m : ℕ} (T : EdgeTrainLevels E m)
    (edges : E → Set V) (μ : Fin (m + 1))
    (hEdges : Nonempty E)
    (hEveryEdge : ∀ e : E, (edges e).Nonempty) :
    Nonempty (FirstWagonUnionVertex
      (T.wagonClassCarrier edges μ)) := by
  obtain ⟨e⟩ := hEdges
  obtain ⟨x, hx⟩ := hEveryEdge e
  exact ⟨⟨T.wagonClassOwner μ e,
    ⟨x, T.edge_subset_ownerWagonCarrier edges μ e hx⟩⟩⟩

/-- Every genuine old A-support edge contains a vertex when
its source coloured one-edge type A is nonempty. Hence a
nonempty old physical A-support family makes the actual
tagged W nonempty without a new EHN-stage hypothesis. -/
theorem EdgeTrainLevels.actualSupportWagonUnion_nonempty
    {L : RelLanguage.{u}} {UA : Type v}
    [Nonempty UA]
    (A : RelStructure L UA) (D : RelStructure L V)
    {m : ℕ}
    (T : EdgeTrainLevels
      {e : Set V // e ∈ supportCopies A D} m)
    (μ : Fin (m + 1))
    (hEdges :
      Nonempty {e : Set V // e ∈ supportCopies A D}) :
    Nonempty (FirstWagonUnionVertex
      (T.wagonClassCarrier
        (fun e : {e : Set V // e ∈ supportCopies A D} => e.1)
          μ)) := by
  apply T.wagonUnion_nonempty
    (fun e : {e : Set V // e ∈ supportCopies A D} => e.1)
    μ hEdges
  intro e
  obtain ⟨a, ha⟩ := e.2
  obtain ⟨u⟩ := (inferInstance : Nonempty UA)
  refine ⟨a u, ?_⟩
  rw [ha]
  exact ⟨u, rfl⟩

end StructuralRamsey.Girth
