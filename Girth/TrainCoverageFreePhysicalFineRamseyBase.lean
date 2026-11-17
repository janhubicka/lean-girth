import Girth.ForestRecursiveOutputGirth
import Girth.TrainPhysicalEdgeToEmbeddingArrow
import Girth.TrainPhysicalPartiteForestBaseTwo

set_option autoImplicit false
set_option Elab.async false

namespace StructuralRamsey.Girth.TrainRecursiveWitness.CoverageFree.Physical

open StructuralRamsey.RelStructure
open StructuralRamsey.Partite (System)

universe u v w
variable {L : RelLanguage.{u}} {UA X : Type v}

private theorem exists_finePartiteRamseyBase_withProjection_of_spanningTuple
    (A₀ : RelStructure L UA) [LinearOrder UA] [Finite UA]
    (Target : System L.withOrder UA X) [Finite X]
    (hFine : ∀ (a : Embedding A₀.ordered Target.toRelStructure) (x : UA),
      Target.part (a x) = x)
    (hSupport : ∀ x : X, ∃ a : Embedding A₀.ordered Target.toRelStructure,
      x ∈ copyCarrier a)
    (hTwo : ∃ a b : Embedding A₀.ordered Target.toRelStructure, ¬ SameCopy a b)
    (hGirth : GirthGT (supportCopies A₀.ordered Target.toRelStructure) 2)
    (hSpan : ∃ (r : L.Symbol) (z : Fin (L.arity r) → UA),
      A₀.rel r z ∧ Function.Surjective z)
    (κ : Type w) [Fintype κ] [Nonempty κ] :
    ∃ (P : Type v) (_ : Finite P) (D : System L.withOrder UA P)
        (family : Set (Embedding Target.toRelStructure D.toRelStructure)),
      (∀ (a : Embedding A₀.ordered D.toRelStructure) (x : UA), D.part (a x) = x) ∧
      ALinear A₀.ordered D.toRelStructure ∧
      (∀ x : P, ∃ edge : OldACarrierEdge A₀.ordered D.toRelStructure, x ∈ edge.1) ∧
      (∀ b ∈ family, ∀ x : X, D.part (b x) = Target.part x) ∧
      (∀ b ∈ family, AStrong A₀.ordered D.toRelStructure (copyCarrier b)) ∧
      (∀ χ : Embedding A₀.ordered D.toRelStructure → κ,
        ∃ b ∈ family, ∀ a a' : Embedding A₀.ordered Target.toRelStructure,
          χ (b.comp a) = χ (b.comp a')) ∧
      (Target.toRelStructure.IsHomomorphism A₀.ordered Target.part →
        D.toRelStructure.IsHomomorphism A₀.ordered D.part) := by
  let A := A₀.ordered
  let sourceTrain := EdgeTrainLevels.heightOne (OldACarrierEdge A Target.toRelStructure)
  let allowed : Fin 2 → Set UA := fun _ => Set.univ
  have hParameters : sourceTrain.AdjacentParameters (fun edge => edge.1)
      (fun ν => Target.part ⁻¹' allowed ν) := by
    apply (sourceTrain.adjacentParameters_heightOne_iff _ _).mpr
    intro a b hNe x hx
    exact Set.mem_univ (Target.part x)
  obtain ⟨active, _, _⟩ := hTwo
  obtain ⟨W, hProjection⟩ := finePartiteFtWitness_baseTwo_of_spanningTuple_withProjection
    A₀ Target sourceTrain allowed active hSpan hFine
    (aLinear_of_girthGT_two A Target.toRelStructure hGirth) hSupport hParameters κ
  let f (i : W.Index) : Embedding Target.toRelStructure W.core.toRelStructure :=
    (W.selected i).toEmbedding
  let tested := RelationalMixedSupportTest A f
  have hForest : FiniteMixedForestThrough tested 2 := W.mixedForest
  have hAmbient (a : Embedding A W.core.toRelStructure) :
      tested (HypergraphPiece.oneEdge (copyCarrier a)) :=
    Or.inr ⟨a, rfl⟩
  have hBaseGirth : GirthGT (supportCopies A W.core.toRelStructure) 2 := by
    apply girthGT_of_finiteMixedForestThrough _ tested 2 hForest
    rintro _ ⟨a, rfl⟩
    exact hAmbient a
  refine ⟨W.Vertex, W.finiteVertex, W.core, Set.range f, W.fineEdges,
    aLinear_of_girthGT_two A W.core.toRelStructure hBaseGirth, W.supportCovers,
    ?_, ?_, ?_, hProjection⟩
  · rintro _ ⟨i, rfl⟩ x
    exact (W.selected i).map_part x
  · rintro _ ⟨i, rfl⟩
    exact aStrong_of_finiteMixedForestThrough A (f i) tested 2 (by decide) hForest
      (Or.inl ⟨i, rfl⟩) hAmbient
  · intro χ
    obtain ⟨i, hi⟩ := ordered_embeddingArrow_of_physicalEdgeArrow (A₀ := A₀)
      f W.physicalArrow χ
    exact ⟨f i, ⟨i, rfl⟩, hi⟩

/-- Build the finite fine-partite Ramsey base for the higher-cutoff
picture pass from the height-one forest witness, with every part allowed. -/
theorem exists_finePartiteRamseyBase_of_spanningTuple
    (A₀ : RelStructure L UA) [LinearOrder UA] [Finite UA]
    (Target : System L.withOrder UA X) [Finite X]
    (hFine : ∀ (a : Embedding A₀.ordered Target.toRelStructure) (x : UA),
      Target.part (a x) = x)
    (hSupport : ∀ x : X, ∃ a : Embedding A₀.ordered Target.toRelStructure,
      x ∈ copyCarrier a)
    (hTwo : ∃ a b : Embedding A₀.ordered Target.toRelStructure, ¬ SameCopy a b)
    (hGirth : GirthGT (supportCopies A₀.ordered Target.toRelStructure) 2)
    (hSpan : ∃ (r : L.Symbol) (z : Fin (L.arity r) → UA),
      A₀.rel r z ∧ Function.Surjective z)
    (κ : Type w) [Fintype κ] [Nonempty κ] :
    ∃ (P : Type v) (_ : Finite P) (D : System L.withOrder UA P)
        (family : Set (Embedding Target.toRelStructure D.toRelStructure)),
      (∀ (a : Embedding A₀.ordered D.toRelStructure) (x : UA), D.part (a x) = x) ∧
      ALinear A₀.ordered D.toRelStructure ∧
      (∀ x : P, ∃ edge : OldACarrierEdge A₀.ordered D.toRelStructure, x ∈ edge.1) ∧
      (∀ b ∈ family, ∀ x : X, D.part (b x) = Target.part x) ∧
      (∀ b ∈ family, AStrong A₀.ordered D.toRelStructure (copyCarrier b)) ∧
      (∀ χ : Embedding A₀.ordered D.toRelStructure → κ,
        ∃ b ∈ family, ∀ a a' : Embedding A₀.ordered Target.toRelStructure,
          χ (b.comp a) = χ (b.comp a')) := by
  obtain ⟨P, hP, D, family, hBaseFine, hLinear, hBaseSupport, hFamilyParts,
    hStrong, hArrow, _⟩ := exists_finePartiteRamseyBase_withProjection_of_spanningTuple
    A₀ Target hFine hSupport hTwo hGirth hSpan κ
  exact ⟨P, hP, D, family, hBaseFine, hLinear, hBaseSupport, hFamilyParts, hStrong, hArrow⟩

/-- A fine target whose parts project to the edge type has a Ramsey base
whose parts project to the same type, retaining the actual selected maps. -/
theorem exists_projectingFinePartiteRamseyBase_of_spanningTuple
    (A₀ : RelStructure L UA) [LinearOrder UA] [Finite UA]
    (Target : System L.withOrder UA X) [Finite X]
    (hTarget : Target.toRelStructure.IsHomomorphism A₀.ordered Target.part)
    (hFine : ∀ (a : Embedding A₀.ordered Target.toRelStructure) (x : UA),
      Target.part (a x) = x)
    (hSupport : ∀ x : X, ∃ a : Embedding A₀.ordered Target.toRelStructure,
      x ∈ copyCarrier a)
    (hTwo : ∃ a b : Embedding A₀.ordered Target.toRelStructure, ¬ SameCopy a b)
    (hGirth : GirthGT (supportCopies A₀.ordered Target.toRelStructure) 2)
    (hSpan : ∃ (r : L.Symbol) (z : Fin (L.arity r) → UA),
      A₀.rel r z ∧ Function.Surjective z)
    (κ : Type w) [Fintype κ] [Nonempty κ] :
    ∃ (P : Type v) (_ : Finite P) (D : System L.withOrder UA P)
        (family : Set (Embedding Target.toRelStructure D.toRelStructure)),
      (∀ (a : Embedding A₀.ordered D.toRelStructure) (x : UA), D.part (a x) = x) ∧
      ALinear A₀.ordered D.toRelStructure ∧
      (∀ x : P, ∃ edge : OldACarrierEdge A₀.ordered D.toRelStructure, x ∈ edge.1) ∧
      (∀ b ∈ family, ∀ x : X, D.part (b x) = Target.part x) ∧
      (∀ b ∈ family, AStrong A₀.ordered D.toRelStructure (copyCarrier b)) ∧
      (∀ χ : Embedding A₀.ordered D.toRelStructure → κ,
        ∃ b ∈ family, ∀ a a' : Embedding A₀.ordered Target.toRelStructure,
          χ (b.comp a) = χ (b.comp a')) ∧
      D.toRelStructure.IsHomomorphism A₀.ordered D.part := by
  obtain ⟨P, hP, D, family, hBaseFine, hLinear, hBaseSupport, hFamilyParts,
    hStrong, hArrow, hProjection⟩ := exists_finePartiteRamseyBase_withProjection_of_spanningTuple
    A₀ Target hFine hSupport hTwo hGirth hSpan κ
  exact ⟨P, hP, D, family, hBaseFine, hLinear, hBaseSupport, hFamilyParts,
    hStrong, hArrow, hProjection hTarget⟩

end StructuralRamsey.Girth.TrainRecursiveWitness.CoverageFree.Physical
