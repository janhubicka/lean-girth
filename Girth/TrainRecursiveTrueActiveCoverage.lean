import Girth.HypergraphClique
import Girth.SupportGirthEmbeddingEquiv
import Girth.ForestSelectedMixedCoverage
import Girth.TrainRecursiveNontrivialFibre

set_option autoImplicit false
set_option Elab.async false

/-!
# Irreducible A-coverage for the genuine active recursive target

The recursive q > 2 branch needs the local target to have every
irreducible substructure inside an actual A-copy. This is not a
formal consequence of A-generation alone: a triangle formed by
three A-edges is A-generated but need not extend to one A-edge.

The existing high-girth shadow-clique lemma resolves the obstruction.
For the true active subsystem of the old stage, mixed selected B-or-A
coverage and strongness of the selected BASE copies give A-generation.
The old complete mixed bottom forest supplies ambient support girth,
which restricts to the genuine induced active support. At q >= 3
the girth excludes Berge triangles, giving the required A-extension.

No ordinary source substructure is replaced by a larger part-fibre,
no support edge is pruned, and no additional selected-copy labels are
introduced. This proves a source-target geometry input only; it does
not construct the lower recursive Ramsey witness.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {UA P X : Type v}

/-- Girth of complete physical A-support passes to a relationally
induced source, because its support embeds into the ambient support. -/
theorem supportGirthGT_induce
    (A : RelStructure L UA) (R : RelStructure L X)
    (S : Set X) (g : ℕ)
    (hGirth : GirthGT (supportCopies A R) g) :
    GirthGT (supportCopies A (R.induce S)) g := by
  let incl : Embedding (R.induce S) R := RelStructure.inclusion R S
  have hSub :
      mappedSupportCopies A (R.induce S) R incl ⊆ supportCopies A R := by
    rintro e ⟨a, rfl⟩
    exact ⟨incl.comp a, rfl⟩
  have hMapped :
      GirthGT (mappedSupportCopies A (R.induce S) R incl) g :=
    girthGT_of_subset hSub hGirth
  exact girthGT_source_of_mappedSupportCopies A (R.induce S) R incl g hMapped

/-- A-generated relational structures with nonempty physical A-support
and girth greater than three have genuine A-extensions of all
irreducible substructures, including the empty induced substructure.
The nonempty support premise is essential for that empty case. -/
theorem irreduciblesExtendTo_of_aGenerated_girthThree
    (A : RelStructure L UA) (R : RelStructure L X)
    (hGen : AGenerated A R)
    (hNonempty : Nonempty (OldACarrierEdge A R))
    (hGirth : GirthGT (supportCopies A R) 3) :
    IrreduciblesExtendTo A R := by
  let H := supportCopies A R
  have hRel : RelationsCoveredBy H R := by
    intro sym x hx
    obtain ⟨a, ha⟩ := hGen.2 sym x hx
    exact ⟨copyCarrier a, ⟨a, rfl⟩, ha⟩
  have hVert : ∀ x : X, ∃ e : Set X, e ∈ H ∧ x ∈ e := by
    intro x
    obtain ⟨a, ha⟩ := hGen.1 x
    exact ⟨copyCarrier a, ⟨a, rfl⟩, ha⟩
  have hH : H.Nonempty := by
    obtain ⟨edge⟩ := hNonempty
    exact ⟨edge.1, edge.2⟩
  intro T hT
  obtain ⟨edge, he, hCover⟩ :=
    irreducible_induce_subset_edge_of_girthGT_three
      hGirth hRel hH hVert hT
  obtain ⟨a, rfl⟩ := he
  refine ⟨a, ?_⟩
  intro z
  obtain ⟨u, hu⟩ := hCover z
  exact ⟨u, hu.symm⟩

end StructuralRamsey.Girth

namespace StructuralRamsey.Girth.TrainRecursiveWitness

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {UA VB P : Type v}
variable {A : RelStructure L UA} {B : RelStructure L VB}
variable {D : RelStructure L P}
variable {family : Set (Embedding B D)} {t : List ℕ}
variable {targetTrain : EdgeTrainLevels (OldACarrierEdge A B) t.length}
variable {allowed : Fin (t.length + 1) → Set P}

/-- The real active local target of a finite q >= 3 stage has
irreducible A-coverage. Inputs are the OLD stage and genuine
selected-base strongness; no extra coverage is postulated for the
local target and no new lower recursive witness is used. -/
theorem ForestTailStage.trueActive_irreduciblesExtendTo
    (stage : ForestTailStage A B D family t targetTrain allowed)
    (hA : A.Irreducible) (hBaseLinear : ALinear A D)
    (hBaseStrong : ∀ b : DesignatedCopy B D stage.system family,
      b ∈ stage.selected → AStrong A D (copyCarrier b.base))
    (e : Embedding A D)
    (hRigid : ∀ b : Embedding A D, SameCopy b e → b = e)
    (hActive : (activeCarrier A stage.system e.toFunctionEmbedding).Nonempty)
    (projected : StructuralRamsey.Partite.ProjectedEmbedding
      A stage.system e.toFunctionEmbedding)
    (hq : 3 ≤ t.headD 0) :
    IrreduciblesExtendTo A
      (actualActiveSubsystemPartite A stage.system e.toFunctionEmbedding).toRelStructure := by
  let S := activeCarrier A stage.system e.toFunctionEmbedding
  have hGenerated : AGenerated A (stage.system.toRelStructure.induce S) :=
    activeSubsystem_aGenerated_of_selectedMixedCoverage
      A B D stage.system family stage.selected hA stage.isPartite
      hBaseLinear stage.mixedCoverage hBaseStrong e hRigid hActive
  have hAmbient : GirthGT
      (supportCopies A stage.system.toRelStructure) (t.headD 0) := by
    apply girthGT_of_finiteMixedForestThrough _ _ (t.headD 0) stage.bottomForest
    rintro edge ⟨a, rfl⟩
    exact Or.inl ⟨a, rfl⟩
  have hActiveGirth : GirthGT
      (supportCopies A (stage.system.toRelStructure.induce S)) 3 :=
    supportGirthGT_induce A stage.system.toRelStructure S 3
      (girthGT_mono hAmbient hq)
  have hSupport : Nonempty (OldACarrierEdge A
      (stage.system.toRelStructure.induce S)) := by
    let a := activeInduceProjected A projected
      (projected_mem_activeCarrier A stage.system e.toFunctionEmbedding projected)
    exact ⟨actualEdge a.val⟩
  change IrreduciblesExtendTo A (stage.system.toRelStructure.induce S)
  exact irreduciblesExtendTo_of_aGenerated_girthThree
    A (stage.system.toRelStructure.induce S)
    hGenerated hSupport hActiveGirth

end StructuralRamsey.Girth.TrainRecursiveWitness
