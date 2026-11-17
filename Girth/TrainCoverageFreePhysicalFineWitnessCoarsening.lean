import Girth.TrainCoverageFreePhysicalFinitePass
import Girth.TrainPhysicalPartiteForestData

set_option autoImplicit false
set_option Elab.async false

namespace StructuralRamsey.Partite

universe u v
variable {L : RelLanguage.{u}} {P Q X : Type v}

/-- Relabel a partite system through a partite base. Preservation of
relation tuples suffices for the coarser partition to be transversal. -/
def System.coarsenViaHom (E : System L P X) (D : System L Q P)
    (hProject : ∀ r z, E.rel r z → D.rel r (E.part ∘ z)) : System L Q X where
  toRelStructure := E.toRelStructure
  part := D.part ∘ E.part
  transversal := by
    intro r z hz i j hij
    exact E.transversal r z hz i j (D.transversal r (E.part ∘ z) (hProject r z hz) i j hij)

end StructuralRamsey.Partite

namespace StructuralRamsey.Girth.TrainRecursiveWitness.CoverageFree.Physical

open StructuralRamsey.RelStructure
open StructuralRamsey.Partite (System)

universe u v w
variable {L : RelLanguage.{u}} {UA VB P : Type v}
variable {A : RelStructure L UA} {t : List ℕ}

/-- Extract the standalone fine-partite witness from a completed physical
forest pass through a large base. Every edge, selected label, train cut,
and carrier stays the same. The relation-preserving projection is still
an explicit input here. A recursive pass must maintain it during attachment. -/
noncomputable def PhysicalForestStage.toFinePartiteFtWitness [Finite VB]
    (Target : System L UA VB) (Large : System L UA P)
    {family : Set (Embedding Target.toRelStructure Large.toRelStructure)}
    {targetTrain : EdgeTrainLevels (OldACarrierEdge A Target.toRelStructure) t.length}
    {allowed : Fin (t.length + 1) → Set P}
    (S : PhysicalForestStage A Target.toRelStructure Large.toRelStructure
      family t targetTrain allowed)
    (fineAllowed : Fin (t.length + 1) → Set UA)
    (hAllowed : ∀ ν, allowed ν = Large.part ⁻¹' fineAllowed ν)
    (hProject : ∀ r z, S.system.rel r z → Large.rel r (S.system.part ∘ z))
    (hBaseFine : ∀ (a : Embedding A Large.toRelStructure) (x : UA),
      Large.part (a x) = x)
    (hSelectedParts : ∀ b ∈ S.selected, ∀ x : VB,
      Large.part (b.base x) = Target.part x)
    {κ : Type w} (hArrow : DesignatedArrow S κ) :
    FinePartiteFtWitness A Target t targetTrain fineAllowed κ := by
  let Core := S.system.coarsenViaHom Large hProject
  let J := {b : DesignatedCopy Target.toRelStructure Large.toRelStructure
    S.system family // b ∈ S.selected}
  let f (i : J) : StructuralRamsey.Partite.Embedding Target Core := {
    toEmbedding := i.1.embedding
    map_part := fun x =>
      (congrArg Large.part (i.1.projects x)).trans (hSelectedParts i.1 i.2 x) }
  have hFinite : Finite J := by
    apply Finite.of_injective (fun i : J => i.1.embedding)
    intro i j hij
    exact S.selectedPhysicalInjective
      (congrArg (fun b : Embedding Target.toRelStructure S.system.toRelStructure =>
        bSupportPiece A b) hij)
  refine {
    Vertex := S.Vertex
    finiteVertex := S.finiteVertex
    Index := J
    finiteIndex := hFinite
    core := Core
    selected := f
    train := S.train
    fineEdges := ?_
    supportNonempty := S.supportNonempty
    supportCovers := S.supportCovers
    selectedSupports := S.selectedPhysicalInjective
    mixedForest := ?_
    selectedTrain := ?_
    fineParameters := ?_
    positiveFull := ?_
    physicalArrow := ?_ }
  · intro a x
    obtain ⟨b, hb⟩ := S.projectsACopies a
    change Large.part (S.system.part (a x)) = x
    rw [← hb x]
    exact hBaseFine b x
  · intro pieces hTest hSize
    apply S.bottomForest pieces ?_ hSize
    intro p hp
    rcases hTest p hp with ⟨i, hi⟩ | ⟨a, ha⟩
    · exact Or.inr ⟨i.1, i.2, hi⟩
    · exact Or.inl ⟨a, ha⟩
  · intro ν i a b
    exact S.targetRestriction i.1 i.2 ν a b
  · change S.train.AdjacentParameters (fun edge => edge.1)
      (fun ν => S.system.part ⁻¹' (Large.part ⁻¹' fineAllowed ν))
    simpa only [hAllowed] using S.parameters
  · intro j hj
    change (selectedPictureOrderOneData A Target.toRelStructure Large.toRelStructure
      S.system family S.selected S.train j.castSucc).FullSystemGirthGT (t.get j)
    exact S.tailGirth j hj
  · intro χ
    obtain ⟨b, hb, hMono⟩ := hArrow (fun a => χ (actualEdge a))
    exact ⟨⟨b, hb⟩, hMono⟩

end StructuralRamsey.Girth.TrainRecursiveWitness.CoverageFree.Physical
