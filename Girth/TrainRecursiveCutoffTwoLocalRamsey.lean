import Girth.TrainRecursiveCoveredClosureRamsey
import Girth.TrainRecursiveCutoffTwoCoreGeometry
import Mathlib.Order.Prod.Lex.Basic

set_option autoImplicit false
set_option Elab.async false

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v w

variable {L : RelLanguage.{u}} {U V : Type v}

/-- Order the part blocks by the source order and break ties arbitrarily
inside a block. Then every A-embedding is strictly monotone. -/
theorem exists_cutoffTwo_partiteAuxiliaryOrder
    (A₀ : RelStructure L U) [LinearOrder U] [Finite U]
    (Target : StructuralRamsey.Partite.System L.withOrder U V) [Finite V]
    (hTarget : Target.IsPartiteOver A₀.ordered) :
    ∃ o : LinearOrder V, letI := o
      ∀ a : Embedding A₀.ordered Target.toRelStructure, StrictMono a := by
  classical
  letI : Fintype V := Fintype.ofFinite V
  let index := Fintype.equivFin V
  let key (x : V) : U ×ₗ Fin (Fintype.card V) := toLex (Target.part x, index x)
  have hKey : Function.Injective key := by
    intro x y hxy
    exact index.injective (congrArg (fun z => (ofLex z).2) hxy)
  refine ⟨LinearOrder.lift' key hKey, ?_⟩
  intro a x y hxy
  obtain ⟨b, hb⟩ := hTarget.after_irreducible_embedding
    (RelStructure.ordered_hereditarilyIrreducible A₀).irreducible a
  have hId (u : U) : b u = u :=
    congrFun (StrictMono.eq_id (RelStructure.Embedding.strictMono b)) u
  change key (a x) < key (a y)
  apply Prod.Lex.toLex_lt_toLex.mpr
  left
  change Target.part (a x) < Target.part (a y)
  rw [← hb x, ← hb y, hId x, hId y]
  exact hxy

/-- An actual covered local witness for the height-one, cutoff-two step.
The relational order on the partite target is kept throughout the lift.
The auxiliary linear order is used in the EHN call. The same literal
selected partite lifts give the Ramsey arrow, strongness and coverage. -/
theorem cutoffTwoCoveredPartiteLocalRamsey
    (A₀ : RelStructure L U) [LinearOrder U] [Finite U]
    (Target : StructuralRamsey.Partite.System L.withOrder U V)
    [LinearOrder V] [Finite V]
    (hTarget : Target.IsPartiteOver A₀.ordered)
    (hLinear : ALinear A₀.ordered Target.toRelStructure)
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
      ALinear A₀.ordered Core.toRelStructure ∧
      IrreduciblesExtendTo A₀.ordered Core.toRelStructure ∧
      (∀ i, AStrong A₀.ordered Core.toRelStructure (copyCarrier (f i).toEmbedding)) ∧
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
  obtain ⟨Y, hY, _, D, hClass, hRamsey⟩ :=
    coveredClosedTargetRamseyFamily_of_monotone_embeddings
      A B hA hLinear hTargetNonsingleton hMono κ
  letI : Finite Y := hY
  let I := StructuralRamsey.Structure.Embedding (targetClosureExpansion A B) D
  letI : Finite I := inferInstance
  have hNonempty : Nonempty I := by
    obtain ⟨i, _⟩ := hRamsey (fun _ => Classical.choice (inferInstance : Nonempty κ))
    exact ⟨i⟩
  let C : CutoffTwoLiftData A B (closureRelReduct D) I :=
    ⟨targetEmbeddingRel, Target.part, allowed, cutoffTwoOwner hSupport⟩
  have hPart : C.part = Target.part := rfl
  have hPartOnA (a : Embedding A B) (u : U) : C.part (a u) = u := by
    obtain ⟨b, hb⟩ := hTarget.after_irreducible_embedding hA a
    rw [hRigid b] at hb
    exact (hb u).symm
  have hOwner (a : Embedding A B) (u : U) (hu : u ∉ C.allowed) : C.owner (a u) = a :=
    cutoffTwoOwner_eq_of_forbidden Target.part allowed hSupport
      (fun a b h => ordered_embedding_eq_of_sameCopy a b h) hContacts a u
      (by rw [← hPart, hPartOnA]; exact hu)
  have hStrong (i : I) : AStrong A (closureRelReduct D) (copyCarrier (C.original i)) :=
    targetEmbedding_range_aStrong hClass.1.2 i
  let core := C.system Target hPart
  let f := C.partiteLift Target hPart
  have hLifted := C.all_core_edges_lifted Target hPart hPartOnA hOwner
    hA hRigid hStrong hClass.2 hSupport hNonempty hEdge
  have hFullCoverage : IrreduciblesExtendTo A core.toRelStructure := by
    intro S hS
    obtain ⟨i, a, hCover⟩ := selectedRelationalLiftUnion_all_irreducibles_covered
      C.original C.lift C.project C.project_lift hStrong hClass.2
      (C.lift_compatible hPartOnA hOwner) C.lift_covers hSupport hNonempty hEdge S hS
    refine ⟨(f i).toEmbedding.comp a, fun z => ?_⟩
    obtain ⟨u, hu⟩ := hCover z.2
    exact ⟨u, hu.symm⟩
  refine ⟨C.Vertex, inferInstance, I, inferInstance, core, f,
    C.system_isPartiteOver Target hPart hTarget hA hRigid hOwner
      hStrong hClass.2 hSupport hNonempty hEdge,
    C.core_aLinear Target hPart hPartOnA hOwner hLifted hRigid hClass.1.1,
    hFullCoverage,
    C.selected_core_aStrong Target hPart hPartOnA hOwner hLifted hStrong, ?_, ?_⟩
  · intro a b hNe x hx
    exact C.core_contacts_allowed Target hPart hPartOnA hOwner hLifted
      hRigid a b hNe hx
  · exact C.core_selected_arrow Target hPart hPartOnA hOwner κ hRamsey

end StructuralRamsey.Girth
