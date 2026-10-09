import Girth.UntouchedProjectedGirth
import Girth.ActiveCarrierProjectedSupport
import Girth.SupportGirthEmbeddingEquiv

/-!
# Actual untouched active-subsystem girth after a picture step

Combine three independently checked interfaces:

1. The transversal bounded-forest argument gives girth of every A-edge
   with an untouched projection beta.
2. Every A-copy in the actual ordered active beta-subsystem projects
   to beta. The support of that induced subsystem therefore maps
   into the projected edge family.
3. A relational embedding reflects the girth of its transported
   support hypergraph.

The base intersection needed in (1) comes from the A-linearity of
the Ramsey base and the fact that beta is different from the active
projection alpha (rigidity turns equality of carriers into equality
of embeddings).

This proves the complete untouched-subsystem girth preservation
implication, conditional only on the genuine structural local
witness properties and already maintained picture-step data.
It does not prove existence of that local Ramsey witness nor the
other standing picture invariants.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {UA P X Y I Z : Type v}

/-- Every untouched active subsystem of the standard extension has
A-support girth greater than g. The carrier, transversality and
bounded-forest conditions are precisely those of the structural
local-forest witness; the base copy is linear and beta != alpha. -/
theorem untouched_activeSubsystem_girthGT_of_transversal_local
    (A₀ : RelStructure L UA)
    [LinearOrder UA] [Finite UA]
    (D : RelStructure L.withOrder P)
    (C : StructuralRamsey.Partite.System L.withOrder P X)
    (S : Set X)
    (E : StructuralRamsey.Partite.System L.withOrder P Y)
    (f : I → StructuralRamsey.Partite.Embedding (C.induce S) E)
    (hPartite : C.IsPartiteOver D)
    (hEPartite : E.IsPartiteOver D)
    (hBaseLinear : ALinear A₀.ordered D)
    (α β : RelStructure.Embedding A₀.ordered D)
    (hDifferent : α ≠ β)
    (u v : UA) (huv : u ≠ v)
    [Nonempty I]
    (part : Y → UA)
    (hFine : ∀ y, E.part y = α (part y))
    {H : Set (Set Z)} {K : Set (Set Y)}
    (family : I → StrongSupportEmbedding H K)
    (hTransK : EdgeTransversal K part)
    (g : ℕ)
    (hLocalForest :
      LocalForestThrough (fun i : I => (family i).supportPiece) g)
    (hCarrier :
      ∀ i : I,
        Set.range (family i) = copyCarrier ((f i).toEmbedding))
    (hOldBeta :
      GirthGT
        (supportCopies A₀.ordered
          (C.induce
            (activeCarrier A₀.ordered C β.toFunctionEmbedding)).toRelStructure) g) :
    GirthGT
      (supportCopies A₀.ordered
        ((StructuralRamsey.Partite.Attachment.attach C S E f).induce
          (activeCarrier A₀.ordered
            (StructuralRamsey.Partite.Attachment.attach C S E f)
            β.toFunctionEmbedding)).toRelStructure) g := by
  let W := StructuralRamsey.Partite.Attachment.attach C S E f
  have hDiffCarriers : ¬ SameCopy α β := by
    intro hs
    exact hDifferent (ordered_embedding_eq_of_sameCopy α β hs)
  have hInter :
      (Set.range α.toFunctionEmbedding ∩
       Set.range β.toFunctionEmbedding).Subsingleton := by
    change (copyCarrier α ∩ copyCarrier β).Subsingleton
    exact hBaseLinear α β hDiffCarriers
  have hA : A₀.ordered.Irreducible :=
    (RelStructure.ordered_hereditarilyIrreducible A₀).irreducible
  have hProjected :
      GirthGT
        (projectedSupportCopies A₀.ordered W β.toFunctionEmbedding) g :=
    untouched_projectedSupport_girthGT_of_transversal_local
      A₀.ordered C S E f α.toFunctionEmbedding β.toFunctionEmbedding
      hA hInter u v huv part hFine family hTransK g
      hLocalForest hCarrier hOldBeta
  have hWPartite : W.IsPartiteOver D :=
    StructuralRamsey.Partite.Attachment.attach_isPartiteOver
      C S E f hPartite hEPartite
  let T := activeCarrier A₀.ordered W β.toFunctionEmbedding
  let inc := (StructuralRamsey.Partite.System.inclusion W T).toEmbedding
  have hSubset :
      mappedSupportCopies A₀.ordered (W.induce T).toRelStructure
        W.toRelStructure inc ⊆
      projectedSupportCopies A₀.ordered W β.toFunctionEmbedding :=
    mapped_activeSupport_subset_projected_ordered
      A₀ D W hWPartite β
  have hMapped :
      GirthGT
        (mappedSupportCopies A₀.ordered
          (W.induce T).toRelStructure W.toRelStructure inc) g :=
    girthGT_of_subset hSubset hProjected
  exact girthGT_source_of_mappedSupportCopies
    A₀.ordered (W.induce T).toRelStructure W.toRelStructure
    inc g hMapped

end StructuralRamsey.Girth
