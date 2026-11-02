import Girth.TrainRecursiveActivePartite
import Girth.TrainRecursiveRefinementParameters

set_option autoImplicit false
set_option Elab.async false

/-!
# Exact train data from the recursive fine witness

The refinement on an active fibre uses shared old physical A-edge labels.
The recursive local target uses the physical A-edges of the induced active
structure.  These are the same edges after applying the subtype inclusion.
We make that correspondence explicit, including its image under every
prescribed local embedding.

The ordinary fine target-restriction clause therefore supplies exact
shared-edge compatibility after forgetting the inserted cuts.  This keeps
all prescribed indices and proves preservation and reflection at every
coarse cut.  Coarse parameters of a relabelled A-partite core are separately
derived from fine parameters by pulling back the allowed-part containments
and applying the first-common-ancestor theorem.

No coarse compatibility, coarse parameter record, local girth bound or
completed attachment bound is assumed here.
-/

namespace StructuralRamsey.Girth.TrainRecursiveWitness

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}} {UA P X Y I : Type v}

/-- Every physical A-edge of the induced source gives its literal old
carrier, together with the fact that the whole edge is shared. -/
def inducedACarrierToShared
    (A : RelStructure L UA) (B : RelStructure L X) (S : Set X) :
    OldACarrierEdge A (B.induce S) ↪ SharedOldACarrierEdge A B S where
  toFun edge := ⟨⟨Subtype.val '' edge.1, by
    obtain ⟨a, ha⟩ := edge.2
    refine ⟨(B.inclusion S).comp a, ?_⟩
    rw [ha]
    exact (copyCarrier_comp_eq_image (B.inclusion S) a).symm⟩, by
      rintro x ⟨y, _hy, rfl⟩
      exact y.2⟩
  inj' := by
    intro edge edge' h
    apply Subtype.ext
    exact supportCarrier_image_eq_of_injective Subtype.val Subtype.val_injective
      (congrArg (fun p : SharedOldACarrierEdge A B S => p.1.1) h)

/-- The carrier map agrees exactly with composition of genuine
A-embeddings with the induced-substructure inclusion. -/
theorem inducedACarrierToShared_actualEdge
    (A : RelStructure L UA) (B : RelStructure L X) (S : Set X)
    (a : Embedding A (B.induce S)) :
    (inducedACarrierToShared A B S (actualEdge a)).1 =
      actualEdge ((B.inclusion S).comp a) := by
  apply Subtype.ext
  exact (copyCarrier_comp_eq_image (B.inclusion S) a).symm

/-- Every shared old edge is represented by a genuine A-embedding in
the exact induced source.  No carrier coverage or rigidity is needed. -/
theorem sharedOldACarrier_exists_inducedActualEdge
    (A : RelStructure L UA) (B : RelStructure L X) (S : Set X)
    (p : SharedOldACarrierEdge A B S) :
    ∃ a : Embedding A (B.induce S),
      inducedACarrierToShared A B S (actualEdge a) = p := by
  obtain ⟨a, ha⟩ := p.1.2
  let aS : Embedding A (B.induce S) := {
    toFun := fun x => ⟨a x, p.2 (by rw [ha]; exact ⟨x, rfl⟩)⟩
    injective := by
      intro x y h
      exact a.injective (congrArg Subtype.val h)
    map_rel_iff := fun _ _ => a.map_rel_iff _ _
  }
  refine ⟨aS, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  change Subtype.val '' copyCarrier aS = p.1.1
  rw [ha]
  exact (copyCarrier_comp_eq_image (B.inclusion S) aS).symm

/-- No physical edge is lost by changing from induced-source labels to
shared-old labels. -/
theorem inducedACarrierToShared_surjective
    (A : RelStructure L UA) (B : RelStructure L X) (S : Set X) :
    Function.Surjective (inducedACarrierToShared A B S) := by
  intro p
  obtain ⟨a, ha⟩ := sharedOldACarrier_exists_inducedActualEdge A B S p
  exact ⟨actualEdge a, ha⟩

/-- The canonical shared-to-core map is the actual physical carrier of
the composed prescribed A-copy.  This removes the classical carrier
choice from the local witness's train-restriction calculation. -/
theorem sharedCore_inducedActualEdge
    (A : RelStructure L UA) (B : RelStructure L X) (S : Set X)
    (D : RelStructure L Y) (f : I → Embedding (B.induce S) D)
    (i : I) (a : Embedding A (B.induce S)) :
    sharedOldACarrierCoreEmbedding A B S D f i
        (inducedACarrierToShared A B S (actualEdge a)) =
      actualEdge ((f i).comp a) := by
  let core := RelStructure.Attachment.coreEmbedding B S D f
  let std := RelStructure.Attachment.copyEmbedding B S D f i
  let old := (B.inclusion S).comp a
  have hMaps : std.comp old = core.comp ((f i).comp a) := by
    apply Embedding.ext
    intro x
    exact RelStructure.Attachment.copy_extends B S D f i (a x)
  have hOld : (inducedACarrierToShared A B S (actualEdge a)).1.1 =
      copyCarrier old :=
    congrArg Subtype.val (inducedACarrierToShared_actualEdge A B S a)
  apply Subtype.ext
  apply supportCarrier_image_eq_of_injective core core.injective
  calc
    _ = (fun x : X => std x) ''
        (inducedACarrierToShared A B S (actualEdge a)).1.1 :=
      (sharedOldACarrierCoreMap_image A B S D f i
        (inducedACarrierToShared A B S (actualEdge a))).symm
    _ = (fun x : X => std x) '' copyCarrier old := by rw [hOld]
    _ = copyCarrier (std.comp old) := (copyCarrier_comp_eq_image std old).symm
    _ = copyCarrier (core.comp ((f i).comp a)) := congrArg copyCarrier hMaps
    _ = (fun y : Y => core y) '' copyCarrier ((f i).comp a) :=
      copyCarrier_comp_eq_image core ((f i).comp a)

/-- Ordinary target restriction on all genuine A-embeddings gives
preservation and reflection on all shared physical labels.  The local
target train is the given shared train pulled back to the induced source.
-/
theorem sharedCore_train_iff_of_prescribedRestriction
    (A : RelStructure L UA) (B : RelStructure L X) (S : Set X)
    (D : RelStructure L Y) (f : I → Embedding (B.induce S) D)
    {h : ℕ} (source : EdgeTrainLevels (SharedOldACarrierEdge A B S) h)
    (coreTrain : EdgeTrainLevels (OldACarrierEdge A D) h)
    (hRestriction : ∀ (ν : Fin (h + 1)) (i : I)
      (a b : Embedding A (B.induce S)),
      coreTrain.rel ν (actualEdge ((f i).comp a)) (actualEdge ((f i).comp b)) ↔
        (source.restrict (inducedACarrierToShared A B S)).rel ν
          (actualEdge a) (actualEdge b))
    (ν : Fin (h + 1)) (i : I) (p q : SharedOldACarrierEdge A B S) :
    source.rel ν p q ↔ coreTrain.rel ν
      (sharedOldACarrierCoreEmbedding A B S D f i p)
      (sharedOldACarrierCoreEmbedding A B S D f i q) := by
  obtain ⟨a, rfl⟩ := sharedOldACarrier_exists_inducedActualEdge A B S p
  obtain ⟨b, rfl⟩ := sharedOldACarrier_exists_inducedActualEdge A B S q
  rw [sharedCore_inducedActualEdge, sharedCore_inducedActualEdge]
  exact (hRestriction ν i a b).symm

/-- A lower-rank witness's exact fine target restriction descends to
every coarse shared-edge relation.  The source is an actual refinement
of the old restricted train; the output is the forgotten fine core train.
The equality cut and top cut are included in the conclusion. -/
theorem coarseSharedTrain_iff_of_finePrescribedRestriction
    (A : RelStructure L UA) (B : RelStructure L X) (S : Set X)
    (D : RelStructure L Y) (f : I → Embedding (B.induce S) D)
    {m : ℕ} (oldTrain : EdgeTrainLevels (OldACarrierEdge A B) m)
    (hm : 0 < m)
    {edge : SharedOldACarrierEdge A B S → Set X} {part : X → P}
    {firstAllowed : Set P} {g : ℕ}
    (R : FirstWagonRefinement
      (oldTrain.restrict (sharedOldACarrierInclusion A B S))
      hm edge part firstAllowed g)
    (fineTrain : EdgeTrainLevels (OldACarrierEdge A D) (m + R.extraCuts))
    (hRestriction : ∀ (ν : Fin (m + R.extraCuts + 1)) (i : I)
      (a b : Embedding A (B.induce S)),
      fineTrain.rel ν (actualEdge ((f i).comp a)) (actualEdge ((f i).comp b)) ↔
        (R.train.restrict (inducedACarrierToShared A B S)).rel ν
          (actualEdge a) (actualEdge b))
    (μ : Fin (m + 1)) (i : I) (p q : SharedOldACarrierEdge A B S) :
    oldTrain.rel μ p.1 q.1 ↔ (fineTrain.forgetFirstCuts hm).rel μ
      (sharedOldACarrierCoreEmbedding A B S D f i p)
      (sharedOldACarrierCoreEmbedding A B S D f i q) := by
  exact (R.forget_rel_iff μ p q).symm.trans
    (sharedCore_train_iff_of_prescribedRestriction A B S D f
      R.train fineTrain hRestriction
      (EdgeTrainLevels.firstForgetIndex m R.extraCuts μ) i p q)

/-- Fine allowed sets in the recursive A-parts give the actual coarse
parameters after relabelling by the processed base embedding.  The first
coarse parameter uses every positive fine cut through `d + 1`; the other
parameters use their exact retained fine cuts. -/
theorem relabelledCore_forgetFirstCuts_adjacentParameters
    (A : RelStructure L UA) (α : UA ↪ P)
    (E : StructuralRamsey.Partite.System L UA Y)
    {m d : ℕ}
    (fineTrain : EdgeTrainLevels (OldACarrierEdge A E.toRelStructure) (m + d))
    (hm : 0 < m) (fineAllowed : Fin (m + d + 1) → Set UA)
    (allowed : Fin (m + 1) → Set P)
    (hFine : fineTrain.AdjacentParameters (fun edge => edge.1)
      (fun ν => E.part ⁻¹' fineAllowed ν))
    (hFirst : ∀ ρ : Fin (m + d + 1), 0 < ρ.val → ρ.val ≤ d + 1 →
      fineAllowed ρ ⊆ α ⁻¹' allowed ⟨1, Nat.succ_lt_succ hm⟩)
    (hRetained : ∀ ν : Fin (m + 1), 0 < ν.val →
      fineAllowed (EdgeTrainLevels.firstForgetIndex m d ν) ⊆ α ⁻¹' allowed ν) :
    (fineTrain.forgetFirstCuts hm).AdjacentParameters (fun edge => edge.1)
      (fun ν => (E.relabel α).part ⁻¹' allowed ν) := by
  apply fineTrain.forgetFirstCuts_adjacentParameters hm (fun edge => edge.1)
    (fun ν => E.part ⁻¹' fineAllowed ν)
    (fun ν => (E.relabel α).part ⁻¹' allowed ν) hFine
  · intro ρ hPos hLe y hy
    exact hFirst ρ hPos hLe hy
  · intro ν hPos y hy
    exact hRetained ν hPos hy

end StructuralRamsey.Girth.TrainRecursiveWitness
