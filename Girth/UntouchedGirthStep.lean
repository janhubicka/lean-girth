import Girth.MappedOwnerLocalForest
import Girth.StandardActiveFactor
import Girth.UntouchedOwnerBoundary

/-! # Girth of an untouched subsystem after an active picture step

Each A-edge of an untouched beta-fibre has a standard-copy owner.  A constant
owner puts the entire cycle in that standard copy's old beta-active subsystem.
At an owner change, the connector belongs to the local core in the unique
fine part common to alpha and beta, and to both gluing-copy carriers.  The
mapped-forest owner dichotomy excludes the resulting short Berge cycle.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {UA P X Y I : Type v}

/-- Conditional untouched-subsystem girth preservation for one standard
attachment, with the bounded local-forest and projected-edge hypotheses used by
the circulation manuscript. -/
theorem no_short_untouched_projected_cycle
    (A : RelStructure L UA)
    (C : StructuralRamsey.Partite.System L P X)
    (S : Set X)
    (E : StructuralRamsey.Partite.System L P Y)
    (f : I → StructuralRamsey.Partite.Embedding (C.induce S) E)
    (α β : UA ↪ P)
    (hA : A.Irreducible)
    (hCoreSupport : ∀ y : Y, E.part y ∈ Set.range α)
    (hInter : (Set.range α ∩ Set.range β).Subsingleton)
    (u v : UA) (huv : u ≠ v)
    [Nonempty I]
    (F : I → HypergraphPiece Y)
    (g : ℕ)
    (hLocalForest : LocalForestThrough F g)
    (hCarrier : ∀ i : I,
      (F i).carrier = copyCarrier ((f i).toEmbedding))
    (p : P)
    (hFineUniq : ∀ w : P,
      w ∈ Set.range α ∩ Set.range β → w = p)
    (hPart : EdgesMeetPartAtMostOne F {y | E.part y = p})
    (hOldBeta :
      GirthGT
        (supportCopies A
          (C.induce (activeCarrier A C β)).toRelStructure) g)
    (c : BergeCycle (supportCopies A
      (StructuralRamsey.Partite.Attachment.attach C S E f).toRelStructure))
    (hLen : c.length ≤ g)
    (hProjected : ∀ j : Fin c.length,
      ∃ a : StructuralRamsey.Partite.ProjectedEmbedding A
        (StructuralRamsey.Partite.Attachment.attach C S E f) β,
        c.edge j = copyCarrier a.val) :
    False := by
  classical
  let copies : Fin c.length →
      StructuralRamsey.Partite.ProjectedEmbedding A
        (StructuralRamsey.Partite.Attachment.attach C S E f) β :=
    fun j => Classical.choose (hProjected j)
  have hCopies (j : Fin c.length) :
      c.edge j = copyCarrier (copies j).val :=
    Classical.choose_spec (hProjected j)
  let owner : Fin c.length → I :=
    fun j => untouchedOwner
      A C S E f α β hA hCoreSupport hInter u v huv (copies j)
  let oldβ : RelStructure L (activeCarrier A C β) :=
    (C.induce (activeCarrier A C β)).toRelStructure
  let whole :=
    (StructuralRamsey.Partite.Attachment.attach C S E f).toRelStructure
  let standard : I → RelStructure.Embedding oldβ whole :=
    fun i => (standardActiveEmbedding A C S E f β i).toEmbedding
  let core :=
    (StructuralRamsey.Partite.Attachment.coreEmbedding
      C S E f).toEmbedding.toFunctionEmbedding
  have hEdgeOwner :
      ∀ j, c.edge j ⊆ copyCarrier (standard (owner j)) := by
    intro j
    have hOwnerSub :=
      untouchedOwner_spec
        A C S E f α β hA hCoreSupport hInter u v huv (copies j)
    have hSub :
        copyCarrier (copies j).val ⊆
          copyCarrier
            (StructuralRamsey.Partite.Attachment.copyEmbedding
              C S E f (owner j)).toEmbedding := by
      simpa [owner] using hOwnerSub
    have hFactor :=
      projectedCopy_subset_standardActive
        A C S E f β (owner j) (copies j) hSub
    rw [hCopies j]
    exact hFactor
  have hBoundary :
      ∀ j, owner j ≠ owner (cyclicSucc j) →
        c.vertex j ∈
          core '' ((F (owner j)).restrictCarrier
            {y | E.part y = p}).carrier ∧
        c.vertex j ∈
          core '' ((F (owner (cyclicSucc j))).restrictCarrier
            {y | E.part y = p}).carrier := by
    intro j hNe
    have hLeft : c.vertex j ∈ copyCarrier (copies j).val := by
      rw [← hCopies j]
      exact c.left_mem j
    have hRight :
        c.vertex j ∈ copyCarrier (copies (cyclicSucc j)).val := by
      rw [← hCopies (cyclicSucc j)]
      exact c.right_mem j
    have hOwnerNe :
        untouchedOwner A C S E f α β hA hCoreSupport
            hInter u v huv (copies j) ≠
          untouchedOwner A C S E f α β hA hCoreSupport
            hInter u v huv (copies (cyclicSucc j)) := by
      simpa [owner] using hNe
    obtain ⟨y, hCore, hyL, hyR⟩ :=
      untouchedOwner_change_shared_point
        A C S E f α β hA hCoreSupport hInter
        u v huv (copies j) (copies (cyclicSucc j))
        (c.vertex j) hLeft hRight hOwnerNe
    rcases hLeft with ⟨x, hx⟩
    have hYPart : E.part y = β x := by
      calc
        E.part y =
            (StructuralRamsey.Partite.Attachment.attach C S E f).part
              ((StructuralRamsey.Partite.Attachment.coreEmbedding
                C S E f) y) :=
          ((StructuralRamsey.Partite.Attachment.coreEmbedding
            C S E f).map_part y).symm
        _ =
            (StructuralRamsey.Partite.Attachment.attach C S E f).part
              (c.vertex j) := congrArg
                (StructuralRamsey.Partite.Attachment.attach
                  C S E f).part hCore
        _ =
            (StructuralRamsey.Partite.Attachment.attach C S E f).part
              ((copies j).val x) := congrArg
                (StructuralRamsey.Partite.Attachment.attach
                  C S E f).part hx.symm
        _ = β x := (copies j).property x
    have hFine : E.part y = p :=
      hFineUniq (E.part y)
        ⟨hCoreSupport y, ⟨x, hYPart.symm⟩⟩
    have hyFL : y ∈ (F (owner j)).carrier := by
      rw [hCarrier (owner j)]
      simpa [owner] using hyL
    have hyFR :
        y ∈ (F (owner (cyclicSucc j))).carrier := by
      rw [hCarrier (owner (cyclicSucc j))]
      simpa [owner] using hyR
    constructor
    · refine ⟨y, ⟨hyFL, hFine⟩, ?_⟩
      exact hCore
    · refine ⟨y, ⟨hyFR, hFine⟩, ?_⟩
      exact hCore
  exact no_short_support_cycle_of_mapped_bounded_forest
    A oldβ whole standard F
    {y | E.part y = p} core g hLocalForest hPart
    hOldBeta c hLen owner hEdgeOwner hBoundary

end StructuralRamsey.Girth
