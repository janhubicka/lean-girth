import Girth.ACopyInducedLinkFull

set_option autoImplicit false

/-!
# A-copy support from genuine induced link data

Compose the checked decorated-star quotient/support equivalence with the
induced-link proof of FullNodeDomains. The resulting conditional interface
has no artificial FullNodeDomains input: it asks for the ordinary data of
actual full relational links and their A-copy nodes.

Still required from the actual picture: relational chart embeddings into
the point quotient, their irreducible coverage, the exact node-coordinate
equation, and chartwise local physical-node completeness.
-/

namespace StructuralRamsey.Girth.ACopyInducedLinkSupport

open StructuralRamsey.RelStructure
open ACopyLayeredStar ACopyDecoratedStar ACopyFullDomain
open ACopyChartCoverage ACopySupportAssembly ACopyInducedLinkFull

universe u v

variable {L : RelLanguage.{u}}
variable {K : Type v}
variable {A : RelStructure L K}
variable {Core I PC : Type v} {Source Shared PS PQ : I → Type v}
variable {N : Diagram Core I Source Shared}
variable (D : Data N K PC PS PQ)

/-- The source-link completeness and the exact star normal form identify
generated node classes with all actual physical A-copy carriers.
No output A-linearity assumption, completed ambient order, or
identification of designated B labels occurs in this statement. -/
noncomputable def decoratedSupportEquiv_of_induced_links
    {H : RelStructure L D.Point}
    {J : Type v} {V : J → Type v}
    {Charts : ∀ j, RelStructure L (V j)}
    (C : (i : I) → RelStructure L (Quotient (D.sourceEq i)))
    (src : (i : I) → Source i → Embedding A (C i))
    (hSrcCarrier : ∀ i e, copyCarrier (src i e) = sourceNodeCarrier D i e)
    (hCore : Function.Injective (coreNodeCarrier D))
    (hSource : ∀ i, Function.Injective (sourceNodeCarrier D i))
    (link : (i : I) → Shared i →
      Embedding A ((C i).induce (sharedSourcePoints D i)))
    (hLink : ∀ i (b : Embedding A ((C i).induce (sharedSourcePoints D i))),
      ∃ q : Shared i, SameCopy b (link i q))
    (hBeta : ∀ i q,
      SameCopy ((RelStructure.inclusion (C i) (sharedSourcePoints D i)).comp
          (link i q)) (src i (N.beta i q)))
    (chart : ∀ j, Embedding (Charts j) H)
    (hCover : CoversIrreducibles chart)
    (hA : A.Irreducible)
    (node : Node N → Embedding A H)
    (hCoord : ∀ e a, node e a = D.nodePoint e a)
    (hLocal : ∀ j (b : Embedding A (Charts j)),
      ∃ e : Node N, SameCopy ((chart j).comp b) (node e)) :
    Node N ≃ supportCopies A H :=
  ACopySupportAssembly.decoratedSupportEquiv D chart hCover hA node hCoord
    hCore hSource
    (ACopyInducedLinkFull.decorated_fullNodeDomains_of_induced_links
      D C src hSrcCarrier hSource link hLink hBeta)
    hLocal

end StructuralRamsey.Girth.ACopyInducedLinkSupport
