import Girth.ForestSingleEdge
import Girth.ForestMixedLocalForestBridge
import Girth.SupportForestToTree

/-!
# A mixed forest certifies A-strongness of its designated copies

A hypergraph forest of full B-support pieces alone does not assert
anything about ambient support edges not among those B-pieces. The
MIXED condition includes every ambient one-A-edge piece. Pairwise
allowed intersections between one B-support piece and every actual
ambient A-edge immediately force strongness: an A-edge meeting the
B-carrier twice must be contained in that B-carrier, because the
one-edge piece's complete carrier is its unique support edge.

This is the exact missing implication needed by the circulation
one-standard LONG-piece argument: a witness gluing-copy image is
A-strong provided that the witness carries the mixed LF_2 invariant
INCLUDING all ambient A-support edges. No strongness is smuggled
into the definition of an ordinary relational embedding.

The more global question of whether the particular recursive witness
satisfies this mixed invariant remains separate. No appendix.
-/

namespace StructuralRamsey.Girth
open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {UA VB W : Type v}

/-- Mixed pairwise forest intersection tests against every genuine
ambient one-A-edge piece certify relational A-strongness of an
embedded B-copy. No size lower bound on A is needed: the strongness
conclusion is activated only by a TWO-vertex intersection. -/
theorem aStrong_of_mixed_support_intersections
    (A : RelStructure L UA)
    {B : RelStructure L VB} {R : RelStructure L W}
    (b : RelStructure.Embedding B R)
    (hMixed : ∀ a : RelStructure.Embedding A R,
      AllowedIntersection (bSupportPiece A b)
        (HypergraphPiece.oneEdge (copyCarrier a))) :
    AStrong A R (copyCarrier b) := by
  intro a hBig
  have hAllowed :
      AllowedIntersection (HypergraphPiece.oneEdge (copyCarrier a))
        (bSupportPiece A b) :=
    allowedIntersection_symm (hMixed a)
  have hOne :
      (HypergraphPiece.oneEdge (copyCarrier a)).IsOneEdge :=
    HypergraphPiece.oneEdge_isOneEdge (copyCarrier a)
  have hBig' :
      ¬(((HypergraphPiece.oneEdge (copyCarrier a)).carrier ∩
        (bSupportPiece A b).carrier).Subsingleton) := by
    simpa [HypergraphPiece.oneEdge, bSupportPiece] using hBig
  have hSub :=
    HypergraphPiece.carrier_subset_of_isOneEdge_of_allowed_not_subsingleton
      hOne hAllowed hBig'
  simpa [HypergraphPiece.oneEdge, bSupportPiece] using hSub

/-- A convenient family-wide interface for an actual finite collection
of genuine embedded B-copies and ALL physical support edges. Only
the mixed allowed-intersection component is needed; a join tree or
large girth threshold is not used in this step. -/
theorem aStrong_family_of_mixed_support_intersections
    (A : RelStructure L UA)
    {B : RelStructure L VB} {R : RelStructure L W}
    {I : Type v} (copies : I → RelStructure.Embedding B R)
    (hMixed : ∀ i : I, ∀ a : RelStructure.Embedding A R,
      AllowedIntersection (bSupportPiece A (copies i))
        (HypergraphPiece.oneEdge (copyCarrier a))) :
    ∀ i : I, AStrong A R (copyCarrier (copies i)) := by
  intro i
  exact aStrong_of_mixed_support_intersections
    A (copies i) (hMixed i)

end StructuralRamsey.Girth
