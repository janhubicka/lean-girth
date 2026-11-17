import Girth.TrainFillingPrivateRealUnionEHN
import Girth.TrainFillingPrivateRealUnionColouredMono
import Girth.TrainFillingPrivateRealUnionLocalCoverage

set_option Elab.async false

/-!
# RAW relational first-wagon union: preparatory EHN, NOT completed ordered W

This constructs an auxiliary-order EHN family for the RAW relational
coproduct. The completed ordered W of the manuscript additionally
contains within-colour binary comparisons ACROSS distinct summands.
Consequently this theorem is PREPARATION, not yet the actual
coloured-ordered EHN input for direct cutoff two.

This is a preparatory coloured EHN input:
A is the actual k-vertex ONE-EDGE structure, D is the
original ordered coloured support structure, and W is the
DEPENDENT DISJOINT UNION of its true first-wagon induced
structures. The original old edge owner records the first
wagon of every full A-support edge.

We derive from genuine T data:
- positive relational arities and the spanning A-edge;
- A-linearity of W from original D linearity;
- monotonicity of every A-embedding into W from unary
  predicates, within-colour order and the chosen block order;
- actual local F_p vertex coverage from the original
  wagon edge-owner cover;
- increasing, A-strong F_p -> W inclusions;
- a source A-copy of W from one nonempty old wagon vertex.

Then the checked-looking generic real-W EHN adapter yields
a single X and the entire family of different F_p private
templates selected by ONE increasing W-copy. There are no
independent assumptions F_p ≃ W, hBlin, hIncludeStrong,
hIncludeMono or hLocalCovered on unrelated structures.

This is a formal proof *candidate*, not kernel validated.
The standard irreducibility of the coloured one-edge source
is explicit until its exact coloured-language theorem is
connected. The later owner-splitting for allowed A_1
intersections remains Track 1's upstream obligation.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure
open StructuralRamsey.Girth.IndexedPrivateChoice

universe u v w
variable {I : Type u} {V P : Type v}
variable [LinearOrder I] [LinearOrder V] [Finite V]
variable [LinearOrder P] [Finite P]

/-- EHN from the REAL first wagons of the original
coloured edge train, with all selected unequal-summand
local embeddings and their common selected-edge arrow. -/
theorem realColouredFirstWagon_privateEHN
    {κ : Type w}
    (k : ℕ) (hk : 2 ≤ k)
    (profile : Fin k → I)
    (hProfileBlocks : ∀ i j : Fin k,
      i < j → profile i ≠ profile j → profile i < profile j)
    (E : Set (Set V)) (oldColour : V → I)
    (hOldBlocks : ∀ x y : V,
      oldColour x ≠ oldColour y →
      x < y → oldColour x < oldColour y)
    (hOldColourToOrder : ∀ x y : V,
      oldColour x < oldColour y → x < y)
    (hDlinear :
      ALinear (colouredOrderedEdgeSource.{u,v} k profile)
        (colouredOrderedEdgeTarget k E oldColour))
    (oldCarrier : P → Set V)
    (owner : {e : Set V //
        e ∈ supportCopies
          (colouredOrderedEdgeSource.{u,v} k profile)
          (colouredOrderedEdgeTarget k E oldColour)} → P)
    (hOwnerCarrier : ∀ e, e.1 ⊆ oldCarrier (owner e))
    (hWagonCover : ∀ p (x : {x : V // x ∈ oldCarrier p}),
      ∃ e : {e : Set V //
          e ∈ supportCopies
            (colouredOrderedEdgeSource.{u,v} k profile)
            (colouredOrderedEdgeTarget k E oldColour)},
        owner e = p ∧ x.1 ∈ e.1)
    (hNonempty : Nonempty (FirstWagonUnionVertex oldCarrier))
    [Fintype κ] [Nonempty κ] :
    let A := colouredOrderedEdgeSource.{u,v} k profile
    let D := colouredOrderedEdgeTarget k E oldColour
    let B := firstWagonDisjointUnion oldCarrier
      (fun p => D.induce (oldCarrier p))
    letI : LinearOrder (FirstWagonUnionVertex oldCarrier) :=
      firstWagonUnionOrder oldCarrier oldColour
    ∃ (X : Type v) (_ : Finite X) (o : LinearOrder X)
      (R : StructuralRamsey.Structure
        (closureLanguage (colouredOrderedEdgeLanguage I k)) X),
      ElementaryCAClass A R ∧
      (letI : LinearOrder X := o
       ∃ (U : SummandPrivateTemplate.MonotoneClosedChoice A B R →
           PrivateWagonInput V P X),
         ∃ (hTemplate : ∀ c, (U c).templateEdges =
               supportCopies A (closureRelReduct R)),
           (∀ c p, StrictMono ((U c).coordinate p)) ∧
           ∀ ρ : {e : Set X //
                    e ∈ supportCopies A (closureRelReduct R)} → κ,
             ∃ (c : SummandPrivateTemplate.MonotoneClosedChoice A B R)
               (colour : κ),
               ∀ p : P, ∀ e : {e : Set X //
                   e ∈ supportCopies A (closureRelReduct R)},
                 e ∈ selectedCommonEdges U
                   (supportCopies A (closureRelReduct R))
                   hTemplate c p → ρ e = colour) := by
  let A := colouredOrderedEdgeSource.{u,v} k profile
  let D := colouredOrderedEdgeTarget k E oldColour
  let local : (p : P) → RelStructure
      (colouredOrderedEdgeLanguage I k)
      {x : V // x ∈ oldCarrier p} :=
    fun p => D.induce (oldCarrier p)
  have hPositive :=
    colouredOrderedEdgeLanguage_positive_arity k hk
  have hSpan :=
    colouredOrderedEdgeSource_hasSpanningRelation k profile
  have hLocalLinear : ∀ p : P, ALinear A (local p) :=
    fun p => aLinear_induce hDlinear (oldCarrier p)
  have hLocalMono : ∀ p : P, ∀ a : Embedding A (local p),
      StrictMono a := by
    intro p a
    exact colouredFirstWagonACopy_strictMono k profile
      hProfileBlocks E oldColour hOldColourToOrder
        (oldCarrier p) a
  have hLocalCovered :
      ∀ p (x : {x : V // x ∈ oldCarrier p}),
        ∃ a : Embedding A (local p), x ∈ copyCarrier a :=
    originalFirstWagonLocalCoverage A D oldCarrier
      owner hOwnerCarrier hWagonCover
  exact realFirstWagonDisjointUnion_privateEHN
    A oldCarrier local hPositive hSpan
    oldColour hOldBlocks hLocalLinear hLocalMono
    hLocalCovered hNonempty

end StructuralRamsey.Girth
