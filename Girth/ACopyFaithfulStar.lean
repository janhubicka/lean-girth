import Girth.ACopyStarChartCoverage

set_option autoImplicit false

/-!
# Conditional faithful decorated A-copy star

One final adapter combines the independent validated ingredients:
* point quotient and exact intersections with unsupported chart records,
* full induced link relations and induced core/standard embeddings,
* automatic irreducible coverage by those charts,
* complete physical A-node link domains from the actual link embeddings,
* source-local A-node completeness and source carrier faithfulness.

The output node quotient is consequently equivalent to ALL ACTUAL physical
A-copy carriers of the relational free star; no output A-linearity or
separate abstract FullNodeDomains/CoversIrreducibles hypotheses occur.

Actual A-embeddings for basic nodes and their coordinate equations remain
explicit premises. This interface does not supply parameters, bridges,
cycle bounds, the Ramsey arrow, or the recursive local witness.
-/

namespace StructuralRamsey.Girth.ACopyFaithfulStar

open StructuralRamsey.RelStructure
open ACopyLayeredStar ACopyDecoratedStar ACopyFullDomain
open ACopyChartCoverage ACopySupportAssembly ACopyInducedLinkSupport
open ACopyInducedLinkRelations ACopyDecoratedRelationalStar
open ACopyStarChartAdapter ACopyStarChartCoverage

universe u v

variable {L : RelLanguage.{u}}
variable {CN I K PC : Type v} {SN SH PS PQ : I → Type v}
variable {N : Diagram CN I SN SH}
variable (D : Data N K PC PS PQ)
variable {A : RelStructure L K}

/-- Local A-copy completeness for the two chart sorts supplies the
chartwise completeness field needed by the global physical-support
equivalence. No duplicate designated B-chart labels are identified. -/
theorem localACompleteness_of_core_and_sources
    (C : RelStructure L (Quotient D.coreEq))
    (S : (i : I) → RelStructure L (Quotient (D.sourceEq i)))
    (Q : (i : I) → RelStructure L (PQ i))
    (embedCore : (i : I) → Embedding (Q i) C)
    (embedSource : (i : I) → Embedding (Q i) (S i))
    (hCoreCoord : ∀ i (p : PQ i),
      embedCore i p = Quotient.mk D.coreEq (D.alpha i p))
    (hSourceCoord : ∀ i (p : PQ i),
      embedSource i p = Quotient.mk (D.sourceEq i) (D.beta i p))
    (node : Node N → Embedding A (relationalUnion D C S))
    (hCoreLocal : ∀ b : Embedding A C,
      ∃ e : CN, SameCopy
        ((chartEmbedding D C S Q embedCore embedSource
          hCoreCoord hSourceCoord none).comp b)
        (node (nodeCore N e)))
    (hSourceLocal : ∀ i (b : Embedding A (S i)),
      ∃ e : SN i, SameCopy
        ((chartEmbedding D C S Q embedCore embedSource
          hCoreCoord hSourceCoord (some i)).comp b)
        (node (nodeSource N i e))) :
    ∀ j (b : Embedding A (chartStructure D C S j)),
      ∃ e : Node N, SameCopy
        ((chartEmbedding D C S Q embedCore embedSource
          hCoreCoord hSourceCoord j).comp b) (node e) := by
  intro j b
  cases j with
  | none =>
      obtain ⟨e, he⟩ := hCoreLocal b
      exact ⟨nodeCore N e, he⟩
  | some i =>
      obtain ⟨e, he⟩ := hSourceLocal i b
      exact ⟨nodeSource N i e, he⟩

/-- Conditional faithful relational A-copy star, with its genuine induced
source links, node domains and irreducible chart coverage constructed
rather than added as independent output invariants. -/
noncomputable def actual_physical_support_equiv_of_full_links
    (C : RelStructure L (Quotient D.coreEq))
    (S : (i : I) → RelStructure L (Quotient (D.sourceEq i)))
    (Q : (i : I) → RelStructure L (PQ i))
    (embedCore : (i : I) → Embedding (Q i) C)
    (embedSource : (i : I) → Embedding (Q i) (S i))
    (hCoreCoord : ∀ i (p : PQ i),
      embedCore i p = Quotient.mk D.coreEq (D.alpha i p))
    (hSourceCoord : ∀ i (p : PQ i),
      embedSource i p = Quotient.mk (D.sourceEq i) (D.beta i p))
    (src : (i : I) → SN i → Embedding A (S i))
    (hSrcCarrier : ∀ i e,
      copyCarrier (src i e) = sourceNodeCarrier D i e)
    (hCore : Function.Injective (coreNodeCarrier D))
    (hSource : ∀ i, Function.Injective (sourceNodeCarrier D i))
    (linkNodes : (i : I) → SH i →
      Embedding A ((S i).induce (sharedSourcePoints D i)))
    (hLink : ∀ i (b : Embedding A
       ((S i).induce (sharedSourcePoints D i))),
      ∃ q : SH i, SameCopy b (linkNodes i q))
    (hBeta : ∀ i q,
      SameCopy ((RelStructure.inclusion (S i)
        (sharedSourcePoints D i)).comp (linkNodes i q))
        (src i (N.beta i q)))
    (hA : A.Irreducible)
    (node : Node N → Embedding A (relationalUnion D C S))
    (hCoord : ∀ e a, node e a = D.nodePoint e a)
    (hCoreLocal : ∀ b : Embedding A C,
      ∃ e : CN, SameCopy
        ((chartEmbedding D C S Q embedCore embedSource
          hCoreCoord hSourceCoord none).comp b)
        (node (nodeCore N e)))
    (hSourceLocal : ∀ i (b : Embedding A (S i)),
      ∃ e : SN i, SameCopy
        ((chartEmbedding D C S Q embedCore embedSource
          hCoreCoord hSourceCoord (some i)).comp b)
        (node (nodeSource N i e))) :
    Node N ≃ supportCopies A (relationalUnion D C S) :=
  ACopyInducedLinkSupport.decoratedSupportEquiv_of_induced_links
    (A := A) D S src hSrcCarrier hCore hSource
    linkNodes hLink hBeta
    (chartEmbedding D C S Q embedCore embedSource
      hCoreCoord hSourceCoord)
    (starChartCoversIrreducibles D C S Q embedCore embedSource
      hCoreCoord hSourceCoord)
    hA node hCoord
    (localACompleteness_of_core_and_sources D C S Q embedCore
      embedSource hCoreCoord hSourceCoord node
      hCoreLocal hSourceLocal)

end StructuralRamsey.Girth.ACopyFaithfulStar
