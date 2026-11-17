import Girth.Track1CoveredTriangleFreeRamsey
import Girth.Track1TriangleFreeCoreGeometry
import Girth.TrainRecursiveCutoffTwoLocalRamsey

set_option autoImplicit false
set_option Elab.async false

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v w

variable {L : RelLanguage.{u}} {U V : Type v}

/-- A covered triangle-free local witness for the actual partite step. -/
theorem cutoffThreeCoveredPartiteLocalRamsey
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
    (allowed : Set U)
    (hContacts : ∀ a b : Embedding A₀.ordered Target.toRelStructure, ¬ SameCopy a b →
      ∀ x ∈ copyCarrier a ∩ copyCarrier b, Target.part x ∈ allowed)
    (κ : Type w) [Fintype κ] [Nonempty κ] :
    ∃ (W : Type v) (_ : Finite W) (I : Type v) (_ : Finite I)
      (Core : StructuralRamsey.Partite.System L.withOrder U W)
      (f : I → StructuralRamsey.Partite.Embedding Target Core),
      Core.IsPartiteOver A₀.ordered ∧
      IrreduciblesExtendTo A₀.ordered Core.toRelStructure ∧
      GirthGT (supportCopies A₀.ordered Core.toRelStructure) 3 ∧
      Function.Injective (fun i => bSupportPiece A₀.ordered (f i).toEmbedding) ∧
      FiniteMixedForestThrough
        (RelationalMixedSupportTest A₀.ordered (fun i => (f i).toEmbedding)) 2 ∧
      (∀ a b : Embedding A₀.ordered Core.toRelStructure, ¬ SameCopy a b →
        ∀ x ∈ copyCarrier a ∩ copyCarrier b, Core.part x ∈ allowed) ∧
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
  have hTargetNonsingleton : NonsingletonIrreduciblesExtendTo A B := by
    intro S hS _
    obtain ⟨a, hCover⟩ := hCoverage S hS
    refine ⟨a, ?_⟩
    intro x hx
    obtain ⟨u, hu⟩ := hCover ⟨x, hx⟩
    exact ⟨u, hu.symm⟩
  have hLinear : ALinear A B :=
    aLinear_of_girthGT_two A B (girthGT_mono hGirth (by decide))
  obtain ⟨Y, hY, D, I, hI, original, hOldGirth, hClass, hDistinct,
    hStrong, hControlled, hRamsey⟩ :=
    coveredTriangleFreeRamsey_physicalSelectedFamily
      A B hA hLinear hGirth hTargetNonsingleton hMono κ
  letI : Finite Y := hY
  letI : Finite I := hI
  have hNonempty : Nonempty I := by
    obtain ⟨i, _⟩ := hRamsey (fun _ => Classical.choice (inferInstance : Nonempty κ))
    exact ⟨i⟩
  let C : CutoffTwoLiftData A B D I :=
    ⟨original, Target.part, allowed, cutoffTwoOwner hSupport⟩
  have hPart : C.part = Target.part := rfl
  have hPartOnA (a : Embedding A B) (u : U) : C.part (a u) = u := by
    obtain ⟨b, hb⟩ := hTarget.after_irreducible_embedding hA a
    rw [hRigid b] at hb
    exact (hb u).symm
  have hOwner (a : Embedding A B) (u : U) (hu : u ∉ C.allowed) : C.owner (a u) = a :=
    cutoffTwoOwner_eq_of_forbidden Target.part allowed hSupport
      (fun a b h => ordered_embedding_eq_of_sameCopy a b h) hContacts a u
      (by rw [← hPart, hPartOnA]; exact hu)
  let core := C.system Target hPart
  let f := C.partiteLift Target hPart
  have hLifted := C.all_core_edges_lifted Target hPart hPartOnA hOwner
    hA hRigid hStrong hClass hSupport hNonempty hEdge
  have hFullCoverage : IrreduciblesExtendTo A core.toRelStructure := by
    intro S hS
    obtain ⟨i, a, hCover⟩ := selectedRelationalLiftUnion_all_irreducibles_covered
      C.original C.lift C.project C.project_lift hStrong hClass
      (C.lift_compatible hPartOnA hOwner) C.lift_covers hSupport hNonempty hEdge S hS
    refine ⟨(f i).toEmbedding.comp a, fun z => ?_⟩
    obtain ⟨u, hu⟩ := hCover z.2
    exact ⟨u, hu.symm⟩
  refine ⟨C.Vertex, inferInstance, I, inferInstance, core, f,
    C.system_isPartiteOver Target hPart hTarget hA hRigid hOwner
      hStrong hClass hSupport hNonempty hEdge,
    hFullCoverage, ?_, C.lifted_support_injective Target hPart hDistinct, ?_, ?_, ?_⟩
  · exact C.core_girthGT_three Target hPart hPartOnA hOwner hLifted
      (fun a b h => ordered_embedding_eq_of_sameCopy a b h) hOldGirth
  · apply mixedForestThrough_two_of_strong_controlledFamily A _
    · exact C.core_aLinear Target hPart hPartOnA hOwner hLifted hRigid
        (aLinear_of_girthGT_two A D (girthGT_mono hOldGirth (by decide)))
    · exact C.selected_core_aStrong Target hPart hPartOnA hOwner hLifted hStrong
    · exact C.lifted_controlledIntersection Target hPart hPartOnA hOwner hControlled
  · intro a b hNe x hx
    exact C.core_contacts_allowed Target hPart hPartOnA hOwner hLifted
      hRigid a b hNe hx
  · exact C.core_selected_arrow Target hPart hPartOnA hOwner κ hRamsey

#print axioms StructuralRamsey.Girth.cutoffThreeCoveredPartiteLocalRamsey

end StructuralRamsey.Girth
