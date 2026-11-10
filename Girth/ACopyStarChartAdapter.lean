import Girth.ACopyInducedLinkRelations

set_option autoImplicit false

/-!
# The actual family of relational charts on a decorated A-copy star

Instead of assuming induced core/standard chart maps as separate fields,
construct all of them from the genuine full induced gluing links.
The family is indexed by Option I: none is the core, some i is standard i.
This index retains distinct designated chart labels even if their carriers
happen to agree. Nothing here identifies a chart label with an A-edge.

This is a bridge toward the one-construction/one-support interface; it does
not prove all-chart irreducible coverage, nor the physical node map.
-/

namespace StructuralRamsey.Girth.ACopyStarChartAdapter

open StructuralRamsey.RelStructure
open ACopyLayeredStar ACopyDecoratedStar
open ACopyInducedLinkRelations ACopyDecoratedRelationalStar

universe u v

variable {L : RelLanguage.{u}}
variable {CN I K PC : Type v} {SN SH PS PQ : I → Type v}
variable {N : Diagram CN I SN SH}
variable (D : Data N K PC PS PQ)

/-- The core and sources have different point types. Every retained
unsupported record belongs to its full original point quotient. -/
def chartPoints : Option I → Type v
  | none => Quotient D.coreEq
  | some i => Quotient (D.sourceEq i)

/-- Literal source relational structures, without deleting relations or
selecting only physical A-covered points. -/
def chartStructure
    (C : RelStructure L (Quotient D.coreEq))
    (S : (i : I) → RelStructure L (Quotient (D.sourceEq i))) :
    (j : Option I) → RelStructure L (chartPoints D j)
  | none => C
  | some i => S i

/-- Every source is an induced relational chart in the free union. The
link relation-reflection theorem proves this, including nullary tuples.
There are no additional pairwise standard/standard assumptions. -/
noncomputable def chartEmbedding
    (C : RelStructure L (Quotient D.coreEq))
    (S : (i : I) → RelStructure L (Quotient (D.sourceEq i)))
    (Q : (i : I) → RelStructure L (PQ i))
    (embedCore : (i : I) → Embedding (Q i) C)
    (embedSource : (i : I) → Embedding (Q i) (S i))
    (hCoreCoord : ∀ i (p : PQ i),
      embedCore i p = Quotient.mk D.coreEq (D.alpha i p))
    (hSourceCoord : ∀ i (p : PQ i),
      embedSource i p = Quotient.mk (D.sourceEq i) (D.beta i p)) :
    (j : Option I) →
      Embedding (chartStructure D C S j) (relationalUnion D C S)
  | none => core_embedding_of_full_induced_links D C S Q
      embedCore embedSource hCoreCoord hSourceCoord
  | some i => source_embedding_of_full_induced_links D C S Q
      embedCore embedSource hCoreCoord hSourceCoord i

end StructuralRamsey.Girth.ACopyStarChartAdapter
