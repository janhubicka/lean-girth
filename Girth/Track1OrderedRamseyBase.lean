import Girth.Track1FreshOrderRamsey
import Girth.Track1AuxiliaryOrder
import Girth.Track1TriangleFreeEHNClass
import Girth.TrainRecursiveCoveredClosureRamsey
import Girth.TrainRecursiveCutoffTwoLocalRamsey

set_option autoImplicit false
set_option Elab.async false

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v w
variable {L : RelLanguage.{u}} {U V : Type v}

/-- Use only order-preserving choices from the fresh EHN order.
They still form a Ramsey family. The resulting partite base is linear,
and each selected target copy is strong. -/
theorem cutoffThree_orderedRamseyBase
    (A₀ : RelStructure L U) [LinearOrder U] [Finite U]
    (Target : StructuralRamsey.Partite.System L.withOrder U V)
    [LinearOrder V] [Finite V]
    (hTarget : Target.IsPartiteOver A₀.ordered)
    (hGirth : GirthGT (supportCopies A₀.ordered Target.toRelStructure) 3)
    (hCoverage : IrreduciblesExtendTo A₀.ordered Target.toRelStructure)
    (hSupport : ∀ x : V,
      ∃ a : Embedding A₀.ordered Target.toRelStructure, x ∈ copyCarrier a)
    (hEdge : Nonempty (Embedding A₀.ordered Target.toRelStructure))
    (hMono : ∀ a : Embedding A₀.ordered Target.toRelStructure, StrictMono a)
    (κ : Type w) [Fintype κ] [Nonempty κ] :
    ∃ (W : Type v) (_ : Finite W) (I : Type v) (o : LinearOrder W)
      (Core : StructuralRamsey.Partite.System L.withOrder U W)
      (f : I → StructuralRamsey.Partite.Embedding Target Core),
      Core.IsPartiteOver A₀.ordered ∧ ALinear A₀.ordered Core.toRelStructure ∧
      (∀ i, AStrong A₀.ordered Core.toRelStructure (copyCarrier (f i).toEmbedding)) ∧
      (∀ i (x y : V), x < y → @LT.lt W o.toLT (f i x) (f i y)) ∧
      (∀ χ : Embedding A₀.ordered Core.toRelStructure → κ,
        ∃ i, ∀ a b : Embedding A₀.ordered Target.toRelStructure,
          χ ((f i).toEmbedding.comp a) = χ ((f i).toEmbedding.comp b)) := by
  classical
  let A := A₀.ordered
  let B := Target.toRelStructure
  have hA : A.Irreducible := (RelStructure.ordered_hereditarilyIrreducible A₀).irreducible
  have hRigid (a : Embedding A A) : a = Embedding.id A := by
    apply Embedding.ext
    intro u
    exact congrFun (StrictMono.eq_id (RelStructure.Embedding.strictMono a)) u
  have hTargetCoverage : NonsingletonIrreduciblesExtendTo A B := by
    intro S hS _
    obtain ⟨a, hCover⟩ := hCoverage S hS
    refine ⟨a, ?_⟩
    intro x hx
    obtain ⟨u, hu⟩ := hCover ⟨x, hx⟩
    exact ⟨u, hu.symm⟩
  have hLinear : ALinear A B :=
    aLinear_of_girthGT_two A B (girthGT_mono hGirth (by decide))
  let K : StructuralRamsey.Structure.StructureClass.{u,v} (L := closureLanguage L.withOrder) :=
    fun C => ElementaryCAThreeClass A C ∧ CoveredElementaryCAClass A C
  have hK : StructuralRamsey.Structure.FreeAmalgamationClass K := by
    let h₁ := ElementaryCAThreeClass_freeAmalgamationClass A hA
    let h₂ := CoveredElementaryCAClass_freeAmalgamationClass A hA
    constructor
    · intro _ _ _ _ h e
      exact ⟨h₁.hereditary h.1 e, h₂.hereditary h.2 e⟩
    · intro _ _ _ _ _ _ _ _ _ _ _ _ hLeft hRight hFree
      exact ⟨h₁.free hLeft.1 hRight.1 hFree, h₂.free hLeft.2 hRight.2 hFree⟩
  have hB : K (targetClosureExpansion A B) :=
    ⟨targetClosure_mem_ElementaryCAThreeClass hLinear hGirth,
      targetClosure_mem_ElementaryCAClass hLinear, hTargetCoverage⟩
  obtain ⟨Y, hY, oY, closedCore, hClass, hRamsey⟩ :=
    freshOrderedClosedTargetRamseyFamily_of_mem A B hK hB hLinear hMono κ
  letI : Finite Y := hY
  letI : LinearOrder Y := oY
  let D := closureRelReduct closedCore
  let I := {b : StructuralRamsey.Structure.Embedding (targetClosureExpansion A B) closedCore //
    StrictMono b}
  have hCoreArrow : ∀ χ : Embedding A D → κ, ∃ i : I,
      ∀ a b : Embedding A B,
        χ ((targetEmbeddingRel i.1).comp a) = χ ((targetEmbeddingRel i.1).comp b) := by
    intro χ
    obtain ⟨b, hb, hMono⟩ := hRamsey χ
    exact ⟨⟨b, fun x y h => hb x y h⟩, hMono⟩
  haveI : Nonempty I := by
    obtain ⟨i, _⟩ := hCoreArrow (fun _ => Classical.choice (inferInstance : Nonempty κ))
    exact ⟨i⟩
  let C : CutoffTwoLiftData A B D I :=
    ⟨fun i => targetEmbeddingRel i.1, Target.part, Set.univ, cutoffTwoOwner hSupport⟩
  have hPart : C.part = Target.part := rfl
  have hPartOnA (a : Embedding A B) (u : U) : C.part (a u) = u := by
    obtain ⟨b, hb⟩ := hTarget.after_irreducible_embedding hA a
    rw [hRigid b] at hb
    exact (hb u).symm
  have hOwner (a : Embedding A B) (u : U) (hu : u ∉ C.allowed) : C.owner (a u) = a :=
    False.elim (hu (Set.mem_univ _))
  have hStrong (i : I) : AStrong A D (copyCarrier (C.original i)) :=
    targetEmbedding_range_aStrong hClass.1.1.2 i.1
  let core := C.system Target hPart
  let f := C.partiteLift Target hPart
  have hLifted := C.all_core_edges_lifted Target hPart hPartOnA hOwner
    hA hRigid hStrong hClass.2.2 hSupport inferInstance hEdge
  obtain ⟨o, hOrder⟩ := C.exists_auxiliaryOrder_of_original (fun i => i.2)
  refine ⟨C.Vertex, inferInstance, I, o, core, f,
    C.system_isPartiteOver Target hPart hTarget hA hRigid hOwner
      hStrong hClass.2.2 hSupport inferInstance hEdge,
    C.core_aLinear Target hPart hPartOnA hOwner hLifted hRigid
      (aLinear_of_girthGT_two A D (girthGT_mono hClass.1.2 (by decide))),
    C.selected_core_aStrong Target hPart hPartOnA hOwner hLifted hStrong, ?_, ?_⟩
  · exact hOrder
  · exact C.core_selected_arrow Target hPart hPartOnA hOwner κ hCoreArrow

#print axioms StructuralRamsey.Girth.cutoffThree_orderedRamseyBase

end StructuralRamsey.Girth
