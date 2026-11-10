import Girth.ACopyStarChartAdapter

set_option autoImplicit false

/-!
# Actual relational embeddings of generated A-copy nodes

A decorated star has independently generated quotients of points and of
physical node labels. Given genuine local relational A-embeddings whose
coordinate maps agree with the decorated point presentations, compose
them with the previously derived induced core/standard chart embeddings.

The resulting local A-embeddings agree along every shared basic A-node.
They therefore descend through the *actual level-zero node quotient*,
not a quotient that merely identifies image carriers.

This discharges the construction of the output physical A-embedding
family and its exact node coordinate equation. It does not assume
output linearity, prescribe an arbitrary A-copy, or merge B-chart labels.
-/

namespace StructuralRamsey.Girth.ACopyNodeRelationalLift

open StructuralRamsey.RelStructure
open ACopyLayeredStar ACopyDecoratedStar
open ACopyStarChartAdapter ACopyDecoratedRelationalStar

universe u v

variable {L : RelLanguage.{u}}
variable {CN I K PC : Type v} {SN SH PS PQ : I → Type v}
variable {N : Diagram CN I SN SH}
variable (D : Data N K PC PS PQ)
variable {A : RelStructure L K}

/-- Before quotienting physical node labels, each local A-copy is composed
with the corresponding full relational chart embedding into the free star. -/
noncomputable def rawNodeRelEmbedding
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
    (sourceNode : (i : I) → SN i → Embedding A (S i)) :
    ACopyLayeredStar.Raw (Core := CN) (Source := SN) →
      Embedding A (relationalUnion D C S)
  | .inl e =>
      (chartEmbedding D C S Q embedCore embedSource
        hCoreCoord hSourceCoord none).comp (coreNode e)
  | .inr ⟨i, e⟩ =>
      (chartEmbedding D C S Q embedCore embedSource
        hCoreCoord hSourceCoord (some i)).comp (sourceNode i e)

/-- The local relational embedding's point map equals the *full* decorated
source point presentation, not just its A-supported point set. -/
theorem raw_node_coordinate_eq
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
    (raw : ACopyLayeredStar.Raw (Core := CN) (Source := SN))
    (a : K) :
    rawNodeRelEmbedding D C S Q embedCore embedSource
      hCoreCoord hSourceCoord coreNode sourceNode raw a =
        D.rawNodePoint raw a := by
  cases raw with
  | inl e =>
      change D.coreMap (coreNode e a) = D.corePoint e a
      rw [hCoreNodeCoord e a]
      rfl
  | inr r =>
      rcases r with ⟨i, e⟩
      change D.sourceMap i (sourceNode i e a) = D.sourcePoint i e a
      rw [hSourceNodeCoord i e a]
      rfl

/-- Genuine induced A-embeddings descend through the generated physical
node quotient. The well-definedness proof reuses the same three
generators as the checked point-quotient normal form. -/
noncomputable def nodeRelEmbedding
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
      sourceNode i e a = Quotient.mk (D.sourceEq i) (D.sourceCoord i e a)) :
    Node N → Embedding A (relationalUnion D C S) :=
  Quot.lift (rawNodeRelEmbedding D C S Q embedCore embedSource
    hCoreCoord hSourceCoord coreNode sourceNode) (by
      intro x y h
      apply Embedding.ext
      intro a
      calc
        (rawNodeRelEmbedding D C S Q embedCore embedSource
          hCoreCoord hSourceCoord coreNode sourceNode x) a =
            D.rawNodePoint x a :=
          raw_node_coordinate_eq D C S Q embedCore embedSource
            hCoreCoord hSourceCoord coreNode sourceNode
            hCoreNodeCoord hSourceNodeCoord x a
        _ = D.rawNodePoint y a := by
          cases h with
          | core e f h =>
              have hef := (N.core_zero e f).mp h
              subst f
              rfl
          | source i e f h =>
              have hef := (N.source_zero i e f).mp h
              subst f
              rfl
          | shared i s =>
              exact D.sharedPoint_eq i s a
        _ = (rawNodeRelEmbedding D C S Q embedCore embedSource
          hCoreCoord hSourceCoord coreNode sourceNode y) a :=
          (raw_node_coordinate_eq D C S Q embedCore embedSource
            hCoreCoord hSourceCoord coreNode sourceNode
            hCoreNodeCoord hSourceNodeCoord y a).symm)

/-- The output's actual A-embedding has exactly the generated point
coordinate map at *every* quotient physical node. -/
theorem node_rel_embedding_coordinates
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
    (e : Node N) (a : K) :
    nodeRelEmbedding D C S Q embedCore embedSource
      hCoreCoord hSourceCoord coreNode sourceNode
      hCoreNodeCoord hSourceNodeCoord e a = D.nodePoint e a := by
  refine Quot.inductionOn e ?_
  intro x
  exact raw_node_coordinate_eq D C S Q embedCore embedSource
    hCoreCoord hSourceCoord coreNode sourceNode
    hCoreNodeCoord hSourceNodeCoord x a

end StructuralRamsey.Girth.ACopyNodeRelationalLift
