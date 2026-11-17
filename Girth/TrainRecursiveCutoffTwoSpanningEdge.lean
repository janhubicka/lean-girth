import Girth.ALinearRamsey
import Girth.TrainRecursiveCutoffTwoCoreGeometry

set_option autoImplicit false
set_option Elab.async false

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v w

variable {L : RelLanguage.{u}} {U V W I : Type v}
variable {A : RelStructure L U} {D : RelStructure L W}

/-- A true tuple spanning the entire source forces a copy in the selected
lifted union to lie in the selected lift that supplied that tuple. -/
theorem CutoffTwoLiftData.all_core_edges_lifted_of_spanningTuple
    (Target : StructuralRamsey.Partite.System L U V)
    (C : CutoffTwoLiftData A Target.toRelStructure D I)
    (hPart : C.part = Target.part)
    (hSpan : ∃ (R : L.Symbol) (z : Fin (L.arity R) → U),
        A.rel R z ∧ Function.Surjective z)
    (e : Embedding A (C.system Target hPart).toRelStructure) :
    ∃ (i : I) (a : Embedding A Target.toRelStructure),
      e = (C.liftedEmbedding Target hPart i).comp a := by
  classical
  obtain ⟨R, z, hz, hSurj⟩ := hSpan
  have he := (e.map_rel_iff R z).mpr hz
  change ∃ (i : I) (s : Fin (L.arity R) → V),
    Target.rel R s ∧ (C.lift i : V → C.Vertex) ∘ s = e ∘ z at he
  obtain ⟨i, s, _hs, hEq⟩ := he
  let f := C.liftedEmbedding Target hPart i
  have hFactor (x : U) : ∃ y : V, e x = f y := by
    obtain ⟨k, rfl⟩ := hSurj x
    exact ⟨s k, (congrFun hEq k).symm⟩
  let a := e.factorThroughRange f hFactor
  exact ⟨i, a, Embedding.ext (fun x => Classical.choose_spec (hFactor x))⟩

/-- A covered and strong local Ramsey witness for actual physical edges
at cutoff two. Every ambient physical source copy is supported in a selected
lift, by its whole-edge relation. No order-irreducible triangle needs to
extend to an edge, and only the actual source copies must preserve parts. -/
theorem cutoffTwoProjectedPartiteLocalRamsey
    (A₀ : RelStructure L U) [LinearOrder U] [Finite U]
    (Target : StructuralRamsey.Partite.System L.withOrder U V)
    [LinearOrder V] [Finite V]
    (hSpan : ∃ (R : L.Symbol) (z : Fin (L.arity R) → U),
        A₀.rel R z ∧ Function.Surjective z)
    (hPartOnA : ∀ (a : Embedding A₀.ordered Target.toRelStructure) (u : U),
      Target.part (a u) = u)
    (hLinear : ALinear A₀.ordered Target.toRelStructure)
    (hSupport : ∀ x : V,
      ∃ a : Embedding A₀.ordered Target.toRelStructure, x ∈ copyCarrier a)
    (hMono : ∀ a : Embedding A₀.ordered Target.toRelStructure, StrictMono a)
    (allowed : Set U)
    (hContacts : ∀ a b : Embedding A₀.ordered Target.toRelStructure, ¬ SameCopy a b →
      ∀ x ∈ copyCarrier a ∩ copyCarrier b, Target.part x ∈ allowed)
    (κ : Type w) [Fintype κ] [Nonempty κ] :
    ∃ (W : Type v) (_ : Finite W) (I : Type v) (_ : Finite I)
      (Core : StructuralRamsey.Partite.System L.withOrder U W)
      (f : I → StructuralRamsey.Partite.Embedding Target Core),
      (∀ (a : Embedding A₀.ordered Core.toRelStructure) (u : U), Core.part (a u) = u) ∧
      ALinear A₀.ordered Core.toRelStructure ∧
      (∀ x : W, ∃ a : Embedding A₀.ordered Core.toRelStructure, x ∈ copyCarrier a) ∧
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
    exact congrFun (StrictMono.eq_id (Embedding.strictMono a)) u
  obtain ⟨Y, hY, _, D, hClass, hRamsey⟩ :=
    closedTargetRamseyFamily_of_monotone_embeddings A B hA hLinear hMono κ
  letI : Finite Y := hY
  let I := Structure.Embedding (targetClosureExpansion A B) D
  let C : CutoffTwoLiftData A B (closureRelReduct D) I :=
    ⟨targetEmbeddingRel, Target.part, allowed, cutoffTwoOwner hSupport⟩
  have hPart : C.part = Target.part := rfl
  have hOwner (a : Embedding A B) (u : U) (hu : u ∉ C.allowed) : C.owner (a u) = a :=
    cutoffTwoOwner_eq_of_forbidden Target.part allowed hSupport
      (fun a b h => ordered_embedding_eq_of_sameCopy a b h) hContacts a u
      (by rw [hPartOnA]; exact hu)
  obtain ⟨R, z, hRel, hSurj⟩ := hSpan
  have hLifted := C.all_core_edges_lifted_of_spanningTuple Target hPart
    ⟨Sum.inl R, z, hRel, hSurj⟩
  have hStrong (i : I) : AStrong A (closureRelReduct D) (copyCarrier (C.original i)) :=
    targetEmbedding_range_aStrong hClass.2 i
  let core := C.system Target hPart
  let f := C.partiteLift Target hPart
  refine ⟨C.Vertex, inferInstance, I, inferInstance, core, f, ?_,
    C.core_aLinear Target hPart hPartOnA hOwner hLifted hRigid hClass.1, ?_,
    C.selected_core_aStrong Target hPart hPartOnA hOwner hLifted hStrong, ?_,
    C.core_selected_arrow Target hPart hPartOnA hOwner κ hRamsey⟩
  · intro a u
    obtain ⟨i, b, rfl⟩ := hLifted a
    exact (C.vertexPart_lift i (b u)).trans (hPartOnA b u)
  · intro x
    obtain ⟨i, y, rfl⟩ := C.lift_covers x
    obtain ⟨a, u, rfl⟩ := hSupport y
    exact ⟨(f i).toEmbedding.comp a, u, rfl⟩
  · intro a b hNe x hx
    exact C.core_contacts_allowed Target hPart hPartOnA hOwner hLifted hRigid a b hNe hx

end StructuralRamsey.Girth
