import Girth.TrainFirstRefinementAppend
import Girth.TrainFirstRefinementTransport
import Girth.TrainUntouchedChildGirth

set_option Elab.async false
set_option autoImplicit false

/-!
# Actual refinement preservation on an untouched active fibre

The complete active physical support is reindexed by standard/old-edge
pairs.  The old refinement is copied within each standard, the actual
output first relation is appended, and every positive output train level
is retained.  All parent fibres, their standard-owner injections, the
inherited and fresh permitted-part bounds, and labelled child girth are
constructed.  The result is returned to the actual physical support.

The core must be supported over the processed base copy; ambient
partiteness alone does not give this.  The fresh permitted part also uses
the output bottom-to-first edge parameter, already supplied by a complete
output stage.  The local indexed forest is needed only through the
refinement cutoff.  No completed output refinement or owner injection is
assumed.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}} {UA P X Y I : Type v}

section Untouched

variable (A₀ : RelStructure L UA) [LinearOrder UA] [Finite UA]
local notation "A" => A₀.ordered
variable (D : RelStructure L.withOrder P)
variable (C : StructuralRamsey.Partite.System L.withOrder P X)
variable (α β : Embedding A₀.ordered D)
variable (E : StructuralRamsey.Partite.System L.withOrder P Y)
variable (f : I → StructuralRamsey.Partite.Embedding
  (C.induce (activeCarrier A₀.ordered C α.toFunctionEmbedding)) E)

local notation "S" => activeCarrier A C α.toFunctionEmbedding
local notation "Out" => StructuralRamsey.Partite.Attachment.attach C S E f
local notation "Std" => StructuralRamsey.Partite.Attachment.copyEmbedding C S E f
local notation "OldActive" =>
  SharedOldACarrierEdge A C.toRelStructure (activeCarrier A C β.toFunctionEmbedding)
local notation "NewActive" =>
  SharedOldACarrierEdge A₀.ordered
    (StructuralRamsey.Partite.System.toRelStructure
      (StructuralRamsey.Partite.Attachment.attach C S E f))
    (activeCarrier A₀.ordered (StructuralRamsey.Partite.Attachment.attach C S E f)
      β.toFunctionEmbedding)

variable {m : ℕ}
variable (T : EdgeTrainLevels (OldACarrierEdge A₀.ordered C.toRelStructure) m)
variable (U : EdgeTrainLevels (OldACarrierEdge A₀.ordered E.toRelStructure) m)
variable (hShared : ∀ _i : I, Nonempty (SharedOldACarrierEdge A₀.ordered
  C.toRelStructure (activeCarrier A₀.ordered C α.toFunctionEmbedding)))

local notation "Train" => generatedActualASupportTrain A
  (RelStructure.HereditarilyIrreducible.irreducible
    (RelStructure.ordered_hereditarilyIrreducible A₀))
  C.toRelStructure S E.toRelStructure
  (fun i => StructuralRamsey.Partite.Embedding.toEmbedding (f i)) T U hShared
local notation "OldTrain" => T.restrict
  (sharedOldACarrierInclusion A C.toRelStructure (activeCarrier A C β.toFunctionEmbedding))
local notation "NewTrain" => EdgeTrainLevels.restrict Train
  (sharedOldACarrierInclusion A (StructuralRamsey.Partite.System.toRelStructure Out)
    (activeCarrier A (Out) β.toFunctionEmbedding))

/-- Append the actual output first relation above the copied old
refinement, on the complete untouched physical support.  The indexed
local forest provides the fresh labelled child-girth bound. -/
noncomputable def untouchedActiveFirstWagonRefinement
    (hPartite : C.IsPartiteOver D) (hEPartite : E.IsPartiteOver D)
    (hBaseLinear : ALinear A D) (hDifferent : α ≠ β)
    (hCoreSupport : ∀ y : Y, E.part y ∈ copyCarrier α)
    (hRel : ∀ (μ : Fin (m + 1)) (i : I)
      (a b : SharedOldACarrierEdge A C.toRelStructure S),
      T.rel μ a.1 b.1 ↔ U.rel μ
        (sharedOldACarrierCoreEmbedding A C.toRelStructure S E.toRelStructure
          (fun j => (f j).toEmbedding) i a)
        (sharedOldACarrierCoreEmbedding A C.toRelStructure S E.toRelStructure
          (fun j => (f j).toEmbedding) i b))
    (hm : 0 < m) (allowed : Fin (m + 1) → Set P)
    (hParameters : (Train).AdjacentParameters (fun edge => edge.1)
      (fun μ => (Out).part ⁻¹' allowed μ))
    (g : ℕ)
    (hLocal : LocalForestThrough (fun i => bSupportPiece A (f i).toEmbedding) g)
    (R : FirstWagonRefinement (OldTrain) hm (fun e => e.1.1) C.part
      (allowed ⟨1, Nat.succ_lt_succ hm⟩) g) :
    FirstWagonRefinement (NewTrain) hm (fun e => e.1.1) (Out).part
      (allowed ⟨1, Nat.succ_lt_succ hm⟩) g := by
  classical
  let eqv : (I × OldActive) ≃ NewActive :=
    untouchedActiveEdgeEquiv A₀ D C α β E f hPartite hEPartite hDifferent hCoreSupport
  let V := (NewTrain).restrict eqv.toEmbedding
  let std : I → X → StructuralRamsey.Partite.Attachment.Vertex S (W := Y) (I := I) :=
    fun i x => Std i x
  have hStandard : ∀ (i : I) (a b : OldActive),
      V.rel ⟨1, Nat.succ_lt_succ hm⟩ (i, a) (i, b) ↔
        (OldTrain).rel ⟨1, Nat.succ_lt_succ hm⟩ a b := by
    intro i a b
    exact standardActiveEdge_train_iff A C S E f β.toFunctionEmbedding
      (RelStructure.ordered_hereditarilyIrreducible A₀).irreducible
      T U hRel hShared ⟨1, Nat.succ_lt_succ hm⟩ i a b
  have hContained (i : I) (a : OldActive) :
      std i '' a.1.1 ⊆
        copyCarrier (standardActiveEmbedding A C S E f β.toFunctionEmbedding i).toEmbedding := by
    rintro z ⟨x, hx, rfl⟩
    exact ⟨⟨x, a.2 hx⟩, rfl⟩
  have hCommon := standardActiveCarriers_inter_single_part
    A₀ D C α β E f hBaseLinear hDifferent
  let Rproduct := FirstRefinementAppend.append
    (OldTrain) hm (fun e : OldActive => e.1.1) C.part
    (allowed ⟨1, Nat.succ_lt_succ hm⟩) g R V hStandard
    std (fun i => (Std i).toEmbedding.injective) (Out).part
    (fun i x => (Std i).map_part x)
    (copyCarrier α ∩ copyCarrier β) hCommon.1
    (by
      intro i j hij a b z ha hb
      exact hCommon.2 i j hij ⟨hContained i a ha, hContained j b hb⟩)
    (by
      intro a b hab hFirst z hz
      have hEdges : (eqv a).1 ≠ (eqv b).1 := by
        intro h
        exact hab (eqv.injective (Subtype.ext h))
      exact (Train).firstEdgeIntersection_of_adjacent hm (fun edge => edge.1)
        (fun μ => (Out).part ⁻¹' allowed μ) hParameters
        (eqv a).1 (eqv b).1 hEdges hFirst hz)
    (by
      intro J carrier owner hOwner hCarrier
      apply untouchedSubcarriers_labelledGirth_of_localForest
        A₀ D C α β E f hBaseLinear hDifferent carrier ⟨owner, hOwner⟩ ?_ g hLocal
      intro j z hz
      obtain ⟨a, ha⟩ := hCarrier j hz
      exact hContained (owner j) a ha)
  exact FirstWagonRefinement.transport hm Rproduct eqv (NewTrain)
    (fun e => e.1.1) (fun _ => rfl) (fun _ _ _ => Iff.rfl)

/-- The finite mixed-forest invariant supplies the preceding construction
when its physical gluing pieces are injectively indexed. -/
noncomputable def untouchedActiveFirstWagonRefinement_of_finiteMixed
    (hPartite : C.IsPartiteOver D) (hEPartite : E.IsPartiteOver D)
    (hBaseLinear : ALinear A D) (hDifferent : α ≠ β)
    (hCoreSupport : ∀ y : Y, E.part y ∈ copyCarrier α)
    (hRel : ∀ (μ : Fin (m + 1)) (i : I)
      (a b : SharedOldACarrierEdge A C.toRelStructure S),
      T.rel μ a.1 b.1 ↔ U.rel μ
        (sharedOldACarrierCoreEmbedding A C.toRelStructure S E.toRelStructure
          (fun j => (f j).toEmbedding) i a)
        (sharedOldACarrierCoreEmbedding A C.toRelStructure S E.toRelStructure
          (fun j => (f j).toEmbedding) i b))
    (hm : 0 < m) (allowed : Fin (m + 1) → Set P)
    (hParameters : (Train).AdjacentParameters (fun edge => edge.1)
      (fun μ => (Out).part ⁻¹' allowed μ))
    (g : ℕ)
    (hInjective : Function.Injective (fun i => bSupportPiece A (f i).toEmbedding))
    (hMixed : FiniteMixedForestThrough
      (RelationalMixedSupportTest A (fun i => (f i).toEmbedding)) g)
    (R : FirstWagonRefinement (OldTrain) hm (fun e => e.1.1) C.part
      (allowed ⟨1, Nat.succ_lt_succ hm⟩) g) :
    FirstWagonRefinement (NewTrain) hm (fun e => e.1.1) (Out).part
      (allowed ⟨1, Nat.succ_lt_succ hm⟩) g :=
  untouchedActiveFirstWagonRefinement A₀ D C α β E f T U hShared
    hPartite hEPartite hBaseLinear hDifferent hCoreSupport hRel hm allowed hParameters g
    (FiniteMixedForestThrough.toLocalForestThrough _ hInjective
      (RelationalMixedSupportTest A (fun i => (f i).toEmbedding)) g
      (fun i => Or.inl ⟨i, rfl⟩) hMixed) R

end Untouched
end StructuralRamsey.Girth
