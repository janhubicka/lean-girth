import Girth.Track1CoveredBaseThree
import Girth.TrainRecursiveSelectedWitnessConsequences
import Girth.LocalCoveredWitnessReduction
import Girth.TrainRecursiveRigidPartiteArrow

set_option autoImplicit false
set_option Elab.async false

namespace StructuralRamsey.Girth.TrainRecursiveWitness

open StructuralRamsey.RelStructure

universe u v w
variable {L : RelLanguage.{u}} {UA VB : Type v}

/-- The nontrivial A-generated target admits an actual finite relational
forest witness at cutoff three. The larger base is itself constructed by
the covered triangle-free local Ramsey theorem. Coarsening retains the
selected family, the arrow, and its complete mixed forest property. -/
theorem cutoffThree_partiteForestWitness
    (A₀ : RelStructure L UA) [LinearOrder UA] [Finite UA] [Nonempty UA]
    (Target : StructuralRamsey.Partite.System L.withOrder UA VB) [Finite VB]
    (hTarget : Target.IsPartiteOver A₀.ordered)
    (hGenerated : AGenerated A₀.ordered Target.toRelStructure)
    (hTwo : ∃ a b : Embedding A₀.ordered Target.toRelStructure, ¬ SameCopy a b)
    (hGirth : GirthGT (supportCopies A₀.ordered Target.toRelStructure) 3)
    (κ : Type w) [Fintype κ] [Nonempty κ] :
    ∃ (W I : Type v) (_ : Finite W)
      (Core : StructuralRamsey.Partite.System L.withOrder UA W)
      (f : I → StructuralRamsey.Partite.Embedding Target Core),
      Core.IsPartiteOver A₀.ordered ∧
      IrreduciblesExtendTo A₀.ordered Core.toRelStructure ∧
      GirthGT (supportCopies A₀.ordered Core.toRelStructure) 3 ∧
      (∀ i, AStrong A₀.ordered Core.toRelStructure (copyCarrier (f i).toEmbedding)) ∧
      FiniteMixedForestThrough
        (RelationalMixedSupportTest A₀.ordered (fun i => (f i).toEmbedding)) 3 ∧
      (∀ χ : Embedding A₀.ordered Core.toRelStructure → κ, ∃ i,
        ∀ a b : Embedding A₀.ordered Target.toRelStructure,
          χ ((f i).toEmbedding.comp a) = χ ((f i).toEmbedding.comp b)) := by
  classical
  let A := A₀.ordered
  let T := Target.toRelStructure
  have hSupport : Nonempty (OldACarrierEdge A T) := by
    obtain ⟨a, _, _⟩ := hTwo
    exact ⟨actualEdge a⟩
  have hEdge : Nonempty (Embedding A T) := by
    obtain ⟨a, _, _⟩ := hTwo
    exact ⟨a⟩
  have hCoverage := irreduciblesExtendTo_of_aGenerated_girthThree
    A T hGenerated hSupport hGirth
  obtain ⟨o, hMono⟩ := exists_cutoffTwo_partiteAuxiliaryOrder A₀ Target hTarget
  letI : LinearOrder VB := o
  obtain ⟨P, hP, J, hJ, Large, g, hLarge, _, hLargeGirth, _, hLargeForest, _, hLargeArrow⟩ :=
    cutoffThreeCoveredPartiteLocalRamsey A₀ Target hTarget hGirth hCoverage hGenerated.1
      hEdge hMono Set.univ (fun _ _ _ _ _ => Set.mem_univ _) κ
  letI : Finite P := hP
  let family : Set (Embedding T Large.toRelStructure) :=
    Set.range (fun j => (g j).toEmbedding)
  have hLargeLinear : ALinear A Large.toRelStructure :=
    aLinear_of_girthGT_two A Large.toRelStructure (girthGT_mono hLargeGirth (by decide))
  have hFamilyStrong (b : Embedding T Large.toRelStructure) (hb : b ∈ family) :
      AStrong A Large.toRelStructure (copyCarrier b) := by
    obtain ⟨j, rfl⟩ := hb
    exact aStrong_of_finiteMixedForestThrough A (g j).toEmbedding _ 2 (by decide) hLargeForest
      (Or.inl ⟨j, rfl⟩) (fun a => Or.inr ⟨a, rfl⟩)
  have hFamilyParts (b : Embedding T Large.toRelStructure) (hb : b ∈ family) (x : VB) :
      Large.part (b x) = Target.part x := by
    obtain ⟨j, rfl⟩ := hb
    exact (g j).map_part x
  have hBaseArrow (χ : Embedding A Large.toRelStructure → κ) :
      ∃ b : Embedding T Large.toRelStructure, b ∈ family ∧
        ∀ a b' : Embedding A T, χ (b.comp a) = χ (b.comp b') := by
    obtain ⟨j, hj⟩ := hLargeArrow χ
    exact ⟨(g j).toEmbedding, ⟨j, rfl⟩, hj⟩
  letI : Nonempty family := by
    obtain ⟨b, hb, _⟩ := hBaseArrow (fun _ => Classical.choice (inferInstance : Nonempty κ))
    exact ⟨⟨b, hb⟩⟩
  let targetTrain := EdgeTrainLevels.heightOne (OldACarrierEdge A T)
  let allowed : Fin 2 → Set UA := fun _ => Set.univ
  have hTargetParameters :
      targetTrain.AdjacentParameters (fun p => p.1) (fun ν => Target.part ⁻¹' allowed ν) := by
    apply (targetTrain.adjacentParameters_heightOne_iff _ _).mpr
    intro p q hNe x hIn
    exact Set.mem_univ _
  have ht : Admissible [3] := ⟨by simp, by simp, by simp⟩
  have hSupportCovers (x : VB) : ∃ p : OldACarrierEdge A T, x ∈ p.1 := by
    obtain ⟨a, ha⟩ := hGenerated.1 x
    exact ⟨actualEdge a, ha⟩
  obtain ⟨stage, _, hArrow⟩ := constructFromInitial_of_nontrivialSteps
    A₀ T Large.toRelStructure family [3] ht targetTrain (fun ν => Large.part ⁻¹' allowed ν)
    hSupport hSupportCovers hGirth
    (targetParameters_of_partiteFamily_preimage A Target Large
      family hFamilyParts (t := [3]) targetTrain allowed hTargetParameters)
    (by intro j hj; have hLt : j.val < 1 := j.isLt; omega)
    κ hBaseArrow (fun _ _ => True) trivial (fun _ _ _ _ _ => trivial)
    (by
      intro e _remaining old hPair _
      obtain ⟨next, hStep⟩ := old.coveredBaseThree_pictureStep
        A₀ hLargeLinear hFamilyStrong hTwo e hPair κ
      exact ⟨next, trivial, hStep⟩)
  let I := {b : DesignatedCopy T Large.toRelStructure stage.system family // b ∈ stage.selected}
  let C := stage.system.coarsenVia Large stage.isPartite
  let f := selectedPartiteGluingFamily_of_largeBase
    Target Large stage.system stage.isPartite family hFamilyParts stage.selected
  obtain ⟨hPartiteC, hCoverageC, _, hForestC⟩ :=
    stage.coarsenedSelected_fineWitnessInputs A Target Large
      hLarge hCoverage hFamilyParts 3 (by decide)
  have hGirthC : GirthGT (supportCopies A C.toRelStructure) 3 := by
    apply girthGT_of_finiteMixedForestThrough _ _ 3 hForestC
    rintro _ ⟨a, rfl⟩
    exact Or.inr ⟨a, rfl⟩
  refine ⟨stage.Vertex, I, inferInstance, C, f, hPartiteC,
    hCoverageC, hGirthC, fun i => stage.strong i.1 i.2, hForestC, ?_⟩
  intro χ
  obtain ⟨b, hb, hMono'⟩ := hArrow χ
  exact ⟨⟨b, hb⟩, hMono'⟩

/-- Retain just the support edges lying in designated target copies.
The exact vertex set is the union of their carriers. A mixed family in the
result was already tested in the full picture, with identical support pieces. -/
theorem cutoffThree_coveredSupportWitness
    (A₀ : RelStructure L UA) [LinearOrder UA] [Finite UA] [Nonempty UA]
    (Target : StructuralRamsey.Partite.System L.withOrder UA VB) [Finite VB]
    (hTarget : Target.IsPartiteOver A₀.ordered)
    (hGenerated : AGenerated A₀.ordered Target.toRelStructure)
    (hTwo : ∃ a b : Embedding A₀.ordered Target.toRelStructure, ¬ SameCopy a b)
    (hGirth : GirthGT (supportCopies A₀.ordered Target.toRelStructure) 3)
    (κ : Type w) [Fintype κ] [Nonempty κ] :
    let E := supportCopies A₀.ordered Target.toRelStructure
    ∃ (W : Type v) (_ : Finite W) (vertices : Set W)
      (K : Set (Set W)) (part : W → UA)
      (family : Set (StrongSupportEmbedding E K)),
      EdgeTransversal K part ∧
      StrongSupportCoversEdges E K family ∧
      GirthGT K 3 ∧
      (∀ x, x ∈ vertices ↔ ∃ f ∈ family, x ∈ Set.range f) ∧
      (∀ e ∈ K, e ⊆ vertices) ∧
      (∀ f ∈ family, ∀ x, part (f x) = Target.part x) ∧
      FiniteMixedForestThrough (fun P =>
        (∃ f ∈ family, P = f.supportPiece) ∨
        (∃ e ∈ K, P = HypergraphPiece.oneEdge e)) 3 ∧
      StrongSupportEdgeArrow E family κ := by
  classical
  let A := A₀.ordered
  let E := supportCopies A Target.toRelStructure
  obtain ⟨W, I, hW, C, f, hPartite, _, hCoreGirth, hStrong, hMixed, hArrow⟩ :=
    cutoffThree_partiteForestWitness A₀ Target hTarget hGenerated hTwo hGirth κ
  let oldK := supportCopies A C.toRelStructure
  let g (i : I) := strongASupportEmbedding A (f i).toEmbedding (hStrong i)
  let oldFamily : Set (StrongSupportEmbedding E oldK) := Set.range g
  let K := coveredLocalEdges E oldFamily
  let family := coveredLocalFamily E oldFamily
  let vertices := {x : W | ∃ f ∈ family, x ∈ Set.range f}
  have hOldArrow : StrongSupportEdgeArrow E oldFamily κ := by
    intro χ
    let originalColour (a : Embedding A C.toRelStructure) : κ :=
      χ ⟨copyCarrier a, ⟨a, rfl⟩⟩
    obtain ⟨i, hi⟩ := hArrow originalColour
    obtain ⟨a, _, _⟩ := hTwo
    refine ⟨g i, ⟨i, rfl⟩, originalColour ((f i).toEmbedding.comp a), ?_⟩
    rintro _ ⟨b, rfl⟩
    change χ ⟨(f i).toEmbedding '' copyCarrier b, _⟩ =
      originalColour ((f i).toEmbedding.comp a)
    have hMap := copyCarrier_comp_eq_image (f i).toEmbedding b
    calc
      _ = originalColour ((f i).toEmbedding.comp b) := by
        apply congrArg χ
        exact Subtype.ext hMap.symm
      _ = _ := hi b a
  letI : Inhabited κ := ⟨Classical.choice (inferInstance : Nonempty κ)⟩
  refine ⟨W, hW, vertices, K, C.part, family, ?_,
    coveredLocalFamily_covers E oldFamily, girthGT_coveredLocalEdges E oldFamily 3 hCoreGirth,
    fun _ => Iff.rfl, ?_, ?_, ?_, strongSupportEdgeArrow_covered E oldFamily κ hOldArrow⟩
  · intro e he u
    obtain ⟨a, rfl⟩ := coveredLocalEdges_subset E oldFamily he
    have hParts := relationalA_embedding_preserves_parts_of_rigid A C
      (RelStructure.ordered_hereditarilyIrreducible A₀).irreducible hPartite
      (orderedA_self_embedding_is_id A₀) a
    refine ⟨a u, ⟨⟨u, rfl⟩, hParts u⟩, ?_⟩
    rintro _ ⟨⟨p, rfl⟩, hEq⟩
    exact congrArg a ((hParts p).symm.trans hEq)
  · intro e he x hx
    obtain ⟨f', hf, _, _, rfl⟩ := he
    obtain ⟨y, _, rfl⟩ := hx
    exact ⟨f'.restrictCovered E oldFamily hf, ⟨⟨f', hf⟩, rfl⟩, ⟨y, rfl⟩⟩
  · rintro _ ⟨f', rfl⟩ x
    obtain ⟨i, hi⟩ := f'.2
    change C.part (f'.1 x) = Target.part x
    rw [← hi]
    exact (f i).map_part x
  · apply FiniteMixedForestThrough.of_tested_subset _ _ 3 ?_ hMixed
    intro piece hPiece
    rcases hPiece with ⟨_, ⟨f', rfl⟩, hEq⟩ | ⟨e, he, rfl⟩
    · obtain ⟨i, hi⟩ := f'.2
      apply Or.inl
      refine ⟨i, ?_⟩
      rw [hEq, StrongSupportEmbedding.restrictCovered_supportPiece, ← hi]
      exact strongASupportEmbedding_piece A (f i).toEmbedding (hStrong i)
    · obtain ⟨a, ha⟩ := coveredLocalEdges_subset E oldFamily he
      exact Or.inr ⟨a, congrArg HypergraphPiece.oneEdge ha⟩

#print axioms StructuralRamsey.Girth.TrainRecursiveWitness.cutoffThree_partiteForestWitness
#print axioms StructuralRamsey.Girth.TrainRecursiveWitness.cutoffThree_coveredSupportWitness

end StructuralRamsey.Girth.TrainRecursiveWitness
