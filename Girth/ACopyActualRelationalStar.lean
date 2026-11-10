import Girth.ACopyFaithfulStar
import Girth.ACopyNodeRelationalLift

set_option autoImplicit false

/-!
# Full actual relational A-copy star from native source data

The generated free relational point quotient, full induced link maps, and
source physical A-copy embeddings suffice to CONSTRUCT the output physical
node embeddings and identify the generated node quotient with exactly the
actual image A-copies. No artificial output-node embedding, point-coordinate
field, core/source carrier-set equality, or global chart-coverage hypothesis
is independently assumed.

The source-local remaining geometric inputs are:
* one native A-embedding per physical source node, with exact coordinates;
* distinct node labels have distinct native A-carriers;
* native node labels cover all A-copies in each source;
* each full induced gluing link carries all of its actual A-copies.

This still does not provide A-linearity, the two-source bridge, train
parameters, the local Ramsey arrow or recursive cycle preservation.
-/

namespace StructuralRamsey.Girth.ACopyActualRelationalStar

open StructuralRamsey.RelStructure
open ACopyLayeredStar ACopyDecoratedStar ACopyFullDomain
open ACopyStarChartAdapter ACopyStarChartCoverage ACopyFaithfulStar
open ACopyNodeRelationalLift

universe u v
variable {L : RelLanguage.{u}}
variable {CN I K PC : Type v} {SN SH PS PQ : I → Type v}
variable {N : Diagram CN I SN SH}
variable (D : Data N K PC PS PQ)
variable {A : RelStructure L K}

/-- Image-copy equality is preserved by composition with a full
relational embedding. Designated chart labels are not identified. -/
theorem sameCopy_comp
    {X Y : Type v} {C : RelStructure L X} {H : RelStructure L Y}
    (j : Embedding C H) (b c : Embedding A C)
    (h : SameCopy b c) :
    SameCopy (j.comp b) (j.comp c) := by
  apply Set.Subset.antisymm
  · rintro z ⟨a, rfl⟩
    have ha : b a ∈ copyCarrier c := by
      rw [← h]
      exact ⟨a, rfl⟩
    obtain ⟨t, ht⟩ := ha
    exact ⟨t, congrArg j ht⟩
  · rintro z ⟨a, rfl⟩
    have ha : c a ∈ copyCarrier b := by
      rw [h]
      exact ⟨a, rfl⟩
    obtain ⟨t, ht⟩ := ha
    exact ⟨t, congrArg j ht⟩

/-- The source's native physical A-embeddings and their coordinate
equations identify the source node-carrier sets automatically. -/
theorem core_native_carrier_eq
    (C : RelStructure L (Quotient D.coreEq))
    (coreNode : CN → Embedding A C)
    (hCoreNodeCoord : ∀ e a,
      coreNode e a = Quotient.mk D.coreEq (D.coreCoord e a))
    (e : CN) :
    copyCarrier (coreNode e) = coreNodeCarrier D e := by
  ext p
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨a, (hCoreNodeCoord e a).symm⟩
  · rintro ⟨a, rfl⟩
    exact ⟨a, hCoreNodeCoord e a⟩

theorem source_native_carrier_eq
    (S : (i : I) → RelStructure L (Quotient (D.sourceEq i)))
    (sourceNode : (i : I) → SN i → Embedding A (S i))
    (hSourceNodeCoord : ∀ i e a,
      sourceNode i e a = Quotient.mk (D.sourceEq i) (D.sourceCoord i e a))
    (i : I) (e : SN i) :
    copyCarrier (sourceNode i e) = sourceNodeCarrier D i e := by
  ext p
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨a, (hSourceNodeCoord i e a).symm⟩
  · rintro ⟨a, rfl⟩
    exact ⟨a, hSourceNodeCoord i e a⟩

/-- One faithful, actual relational A-copy star, including all native
A-copy carriers. No extra abstract FullNodeDomains, CoversIrreducibles,
chart embeddings, output node embeddings, or output coordinate equations
are assumed; all follow from genuine source and induced-link data. -/
noncomputable def actual_support_equiv_of_native_star
    (C : RelStructure L (Quotient D.coreEq))
    (S : (i : I) → RelStructure L (Quotient (D.sourceEq i)))
    (Q : (i : I) → RelStructure L (PQ i))
    (embedCore : (i : I) → Embedding (Q i) C)
    (embedSource : (i : I) → Embedding (Q i) (S i))
    (hCoreCoord : ∀ i (p : PQ i),
      embedCore i p = Quotient.mk D.coreEq (D.alpha i p))
    (hSourceCoord : ∀ i (p : PQ i),
      embedSource i p = Quotient.mk (D.sourceEq i) (D.beta i p))
    (coreNode : CN → Embedding A C)
    (sourceNode : (i : I) → SN i → Embedding A (S i))
    (hCoreNodeCoord : ∀ e a,
      coreNode e a = Quotient.mk D.coreEq (D.coreCoord e a))
    (hSourceNodeCoord : ∀ i e a,
      sourceNode i e a = Quotient.mk (D.sourceEq i) (D.sourceCoord i e a))
    (hCoreUnique : Function.Injective (fun e => copyCarrier (coreNode e)))
    (hSourceUnique : ∀ i, Function.Injective (fun e => copyCarrier (sourceNode i e)))
    (hCoreComplete : ∀ b : Embedding A C,
      ∃ e : CN, SameCopy b (coreNode e))
    (hSourceComplete : ∀ i (b : Embedding A (S i)),
      ∃ e : SN i, SameCopy b (sourceNode i e))
    (linkNodes : (i : I) → SH i →
      Embedding A ((S i).induce (sharedSourcePoints D i)))
    (hLink : ∀ i (b : Embedding A ((S i).induce (sharedSourcePoints D i))),
      ∃ q : SH i, SameCopy b (linkNodes i q))
    (hBeta : ∀ i q,
      SameCopy ((RelStructure.inclusion (S i) (sharedSourcePoints D i)).comp
          (linkNodes i q)) (sourceNode i (N.beta i q)))
    (hA : A.Irreducible) :
    Node N ≃ supportCopies A (relationalUnion D C S) := by
  have hSourceCarrier : ∀ i e,
      copyCarrier (sourceNode i e) = sourceNodeCarrier D i e :=
    source_native_carrier_eq D S sourceNode hSourceNodeCoord
  have hCore : Function.Injective (coreNodeCarrier D) := by
    intro e f h
    apply hCoreUnique
    calc
      copyCarrier (coreNode e) = coreNodeCarrier D e :=
        core_native_carrier_eq D C coreNode hCoreNodeCoord e
      _ = coreNodeCarrier D f := h
      _ = copyCarrier (coreNode f) :=
        (core_native_carrier_eq D C coreNode hCoreNodeCoord f).symm
  have hSource : ∀ i, Function.Injective (sourceNodeCarrier D i) := by
    intro i e f h
    apply hSourceUnique i
    calc
      copyCarrier (sourceNode i e) = sourceNodeCarrier D i e :=
        hSourceCarrier i e
      _ = sourceNodeCarrier D i f := h
      _ = copyCarrier (sourceNode i f) := (hSourceCarrier i f).symm
  let node : Node N → Embedding A (relationalUnion D C S) :=
    nodeRelEmbedding D C S Q embedCore embedSource
      hCoreCoord hSourceCoord coreNode sourceNode
      hCoreNodeCoord hSourceNodeCoord
  have hNodeCoord : ∀ e a, node e a = D.nodePoint e a :=
    node_rel_embedding_coordinates D C S Q embedCore embedSource
      hCoreCoord hSourceCoord coreNode sourceNode
      hCoreNodeCoord hSourceNodeCoord
  have hCoreLocal : ∀ b : Embedding A C,
      ∃ e : CN, SameCopy
        ((chartEmbedding D C S Q embedCore embedSource
          hCoreCoord hSourceCoord none).comp b)
        (node (nodeCore N e)) := by
    intro b
    obtain ⟨e, he⟩ := hCoreComplete b
    refine ⟨e, ?_⟩
    change SameCopy
      ((chartEmbedding D C S Q embedCore embedSource
        hCoreCoord hSourceCoord none).comp b)
      ((chartEmbedding D C S Q embedCore embedSource
        hCoreCoord hSourceCoord none).comp (coreNode e))
    exact sameCopy_comp
      (chartEmbedding D C S Q embedCore embedSource
        hCoreCoord hSourceCoord none) b (coreNode e) he
  have hSourceLocal : ∀ i (b : Embedding A (S i)),
      ∃ e : SN i, SameCopy
        ((chartEmbedding D C S Q embedCore embedSource
          hCoreCoord hSourceCoord (some i)).comp b)
        (node (nodeSource N i e)) := by
    intro i b
    obtain ⟨e, he⟩ := hSourceComplete i b
    refine ⟨e, ?_⟩
    change SameCopy
      ((chartEmbedding D C S Q embedCore embedSource
        hCoreCoord hSourceCoord (some i)).comp b)
      ((chartEmbedding D C S Q embedCore embedSource
        hCoreCoord hSourceCoord (some i)).comp (sourceNode i e))
    exact sameCopy_comp
      (chartEmbedding D C S Q embedCore embedSource
        hCoreCoord hSourceCoord (some i)) b (sourceNode i e) he
  exact ACopyFaithfulStar.actual_physical_support_equiv_of_full_links
    D C S Q embedCore embedSource hCoreCoord hSourceCoord
    sourceNode hSourceCarrier hCore hSource
    linkNodes hLink hBeta hA node hNodeCoord hCoreLocal hSourceLocal

end StructuralRamsey.Girth.ACopyActualRelationalStar
