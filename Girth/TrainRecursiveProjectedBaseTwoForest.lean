import Girth.Track1PhysicalSelectedRepresentatives
import Girth.Track1TriangleFreeCoreGeometry
import Girth.TrainRecursiveCutoffTwoSpanningEdge
import Mathlib.Order.Prod.Lex.Basic

set_option autoImplicit false
set_option Elab.async false

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v w

variable {L : RelLanguage.{u}} {U V : Type v}

/-- The base-two forest witness uses the projections of the actual source
edges. Its selected copies have distinct complete supports, and its mixed
forest bound includes every ambient edge. The spanning relation ensures that
each such ambient edge belongs to a selected lift. If the target's parts
project all relation tuples to the edge type, the same is true of the core. -/
theorem cutoffTwoProjectedPartiteForestRamsey_withProjection
    (A₀ : RelStructure L U) [LinearOrder U] [Finite U]
    (Target : StructuralRamsey.Partite.System L.withOrder U V)
    [Finite V]
    (hSpan : ∃ (R : L.Symbol) (z : Fin (L.arity R) → U),
      A₀.rel R z ∧ Function.Surjective z)
    (hPartOnA : ∀ (a : Embedding A₀.ordered Target.toRelStructure) (u : U),
      Target.part (a u) = u)
    (hLinear : ALinear A₀.ordered Target.toRelStructure)
    (hSupport : ∀ x : V,
      ∃ a : Embedding A₀.ordered Target.toRelStructure, x ∈ copyCarrier a)
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
      (∀ a : Embedding A₀.ordered Core.toRelStructure,
        ∃ (i : I) (b : Embedding A₀.ordered Target.toRelStructure),
          a = (f i).toEmbedding.comp b) ∧
      Function.Injective (fun i => bSupportPiece A₀.ordered (f i).toEmbedding) ∧
      (∀ i, AStrong A₀.ordered Core.toRelStructure (copyCarrier (f i).toEmbedding)) ∧
      FiniteMixedForestThrough
        (RelationalMixedSupportTest A₀.ordered (fun i => (f i).toEmbedding)) 2 ∧
      (∀ a b : Embedding A₀.ordered Core.toRelStructure, ¬ SameCopy a b →
        ∀ x ∈ copyCarrier a ∩ copyCarrier b, Core.part x ∈ allowed) ∧
      (∀ χ : Embedding A₀.ordered Core.toRelStructure → κ,
        ∃ i, ∀ a b : Embedding A₀.ordered Target.toRelStructure,
          χ ((f i).toEmbedding.comp a) = χ ((f i).toEmbedding.comp b)) ∧
      (Target.toRelStructure.IsHomomorphism A₀.ordered Target.part →
        Core.toRelStructure.IsHomomorphism A₀.ordered Core.part) := by
  classical
  let A := A₀.ordered
  let B := Target.toRelStructure
  letI : Fintype V := Fintype.ofFinite V
  let index := Fintype.equivFin V
  let key (x : V) : U ×ₗ Fin (Fintype.card V) := toLex (Target.part x, index x)
  have hKey : Function.Injective key := by
    intro x y hxy
    exact index.injective (congrArg (fun z => (ofLex z).2) hxy)
  letI : LinearOrder V := LinearOrder.lift' key hKey
  have hMono (a : Embedding A B) : StrictMono a := by
    intro x y hxy
    change key (a x) < key (a y)
    apply Prod.Lex.toLex_lt_toLex.mpr
    left
    change Target.part (a x) < Target.part (a y)
    rw [hPartOnA a x, hPartOnA a y]
    exact hxy
  have hA : A.Irreducible := (RelStructure.ordered_hereditarilyIrreducible A₀).irreducible
  have hRigid (a : Embedding A A) : a = Embedding.id A := by
    apply Embedding.ext
    intro u
    exact congrFun (StrictMono.eq_id (Embedding.strictMono a)) u
  obtain ⟨Y, hY, _, D, hClass, hRamsey⟩ :=
    closedTargetRamseyFamily_of_monotone_embeddings A B hA hLinear hMono κ
  letI : Finite Y := hY
  let family : Set (Embedding B (closureRelReduct D)) := Set.range (fun b :
    Structure.Embedding (targetClosureExpansion A B) D => targetEmbeddingRel b)
  let I := Track1PhysicalBCarrier family
  letI : Finite I := Finite.of_injective Subtype.val Subtype.val_injective
  let C : CutoffTwoLiftData A B (closureRelReduct D) I :=
    ⟨track1_physicalRepresentative family, Target.part, allowed, cutoffTwoOwner hSupport⟩
  have hPart : C.part = Target.part := rfl
  have hOwner (a : Embedding A B) (u : U) (hu : u ∉ C.allowed) : C.owner (a u) = a :=
    cutoffTwoOwner_eq_of_forbidden Target.part allowed hSupport
      (fun a b h => ordered_embedding_eq_of_sameCopy a b h) hContacts a u
      (by rw [hPartOnA]; exact hu)
  obtain ⟨R, z, hRel, hSurj⟩ := hSpan
  have hLifted := C.all_core_edges_lifted_of_spanningTuple Target hPart
    ⟨Sum.inl R, z, hRel, hSurj⟩
  have hDistinct : Function.Injective (fun i : I => copyCarrier (C.original i)) := by
    intro i j hEq
    by_contra hNe
    exact track1_physicalRepresentative_distinct family hNe hEq
  have hStrong (i : I) : AStrong A (closureRelReduct D) (copyCarrier (C.original i)) := by
    obtain ⟨b, hb⟩ := (track1_physicalRepresentative_spec family i).1
    change targetEmbeddingRel b = C.original i at hb
    rw [← hb]
    exact targetEmbedding_range_aStrong hClass.2 b
  have hControlled (i j : I) (hNe : i ≠ j) :
      (copyCarrier (C.original i) ∩ copyCarrier (C.original j)).Subsingleton ∨
      ∃ a : Embedding A (closureRelReduct D),
        copyCarrier (C.original i) ∩ copyCarrier (C.original j) = copyCarrier a := by
    obtain ⟨b, hb⟩ := (track1_physicalRepresentative_spec family i).1
    obtain ⟨c, hc⟩ := (track1_physicalRepresentative_spec family j).1
    change targetEmbeddingRel b = C.original i at hb
    change targetEmbeddingRel c = C.original j at hc
    rw [← hb, ← hc]
    apply targetEmbeddings_controlledIntersection hLinear b c
    rw [hb, hc]
    exact fun hEq => hNe (hDistinct hEq)
  have hOldArrow : ∀ χ : Embedding A (closureRelReduct D) → κ,
      ∃ i : I, ∀ a b : Embedding A B,
        χ ((C.original i).comp a) = χ ((C.original i).comp b) := by
    apply track1_physicalRepresentative_arrow A family
    intro χ
    obtain ⟨b, hb⟩ := hRamsey χ
    exact ⟨targetEmbeddingRel b, ⟨b, rfl⟩, hb⟩
  let core := C.system Target hPart
  let f := C.partiteLift Target hPart
  have hCoreLinear := C.core_aLinear Target hPart hPartOnA hOwner hLifted hRigid hClass.1
  have hCoreStrong := C.selected_core_aStrong Target hPart hPartOnA hOwner hLifted hStrong
  refine ⟨C.Vertex, inferInstance, I, inferInstance, core, f, ?_, hCoreLinear, ?_,
    hLifted, C.lifted_support_injective Target hPart hDistinct, hCoreStrong, ?_, ?_,
    C.core_selected_arrow Target hPart hPartOnA hOwner κ hOldArrow, ?_⟩
  · intro a u
    obtain ⟨i, b, rfl⟩ := hLifted a
    exact (C.vertexPart_lift i (b u)).trans (hPartOnA b u)
  · intro x
    obtain ⟨i, y, rfl⟩ := C.lift_covers x
    obtain ⟨a, u, rfl⟩ := hSupport y
    exact ⟨(f i).toEmbedding.comp a, u, rfl⟩
  · exact mixedForestThrough_two_of_strong_controlledFamily A _ hCoreLinear hCoreStrong
      (C.lifted_controlledIntersection Target hPart hPartOnA hOwner hControlled)
  · intro a b hNe x hx
    exact C.core_contacts_allowed Target hPart hPartOnA hOwner hLifted hRigid a b hNe hx
  · exact C.system_isHomomorphism Target hPart

/-- The cutoff-two forest witness with its original edge, intersection,
and colouring assertions. -/
theorem cutoffTwoProjectedPartiteForestRamsey
    (A₀ : RelStructure L U) [LinearOrder U] [Finite U]
    (Target : StructuralRamsey.Partite.System L.withOrder U V)
    [Finite V]
    (hSpan : ∃ (R : L.Symbol) (z : Fin (L.arity R) → U),
      A₀.rel R z ∧ Function.Surjective z)
    (hPartOnA : ∀ (a : Embedding A₀.ordered Target.toRelStructure) (u : U),
      Target.part (a u) = u)
    (hLinear : ALinear A₀.ordered Target.toRelStructure)
    (hSupport : ∀ x : V,
      ∃ a : Embedding A₀.ordered Target.toRelStructure, x ∈ copyCarrier a)
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
      (∀ a : Embedding A₀.ordered Core.toRelStructure,
        ∃ (i : I) (b : Embedding A₀.ordered Target.toRelStructure),
          a = (f i).toEmbedding.comp b) ∧
      Function.Injective (fun i => bSupportPiece A₀.ordered (f i).toEmbedding) ∧
      (∀ i, AStrong A₀.ordered Core.toRelStructure (copyCarrier (f i).toEmbedding)) ∧
      FiniteMixedForestThrough
        (RelationalMixedSupportTest A₀.ordered (fun i => (f i).toEmbedding)) 2 ∧
      (∀ a b : Embedding A₀.ordered Core.toRelStructure, ¬ SameCopy a b →
        ∀ x ∈ copyCarrier a ∩ copyCarrier b, Core.part x ∈ allowed) ∧
      (∀ χ : Embedding A₀.ordered Core.toRelStructure → κ,
        ∃ i, ∀ a b : Embedding A₀.ordered Target.toRelStructure,
          χ ((f i).toEmbedding.comp a) = χ ((f i).toEmbedding.comp b)) := by
  obtain ⟨W, hW, I, hI, Core, f, hFine, hCoreLinear, hCoreCover, hEdgeCover,
    hDistinct, hStrong, hForest, hCoreContacts, hArrow, _⟩ :=
    cutoffTwoProjectedPartiteForestRamsey_withProjection
      A₀ Target hSpan hPartOnA hLinear hSupport allowed hContacts κ
  exact ⟨W, hW, I, hI, Core, f, hFine, hCoreLinear, hCoreCover, hEdgeCover,
    hDistinct, hStrong, hForest, hCoreContacts, hArrow⟩

end StructuralRamsey.Girth

#print axioms StructuralRamsey.Girth.cutoffTwoProjectedPartiteForestRamsey
