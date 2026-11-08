import Girth.TrainActualTwoCycleMixedNoMinimality
import Girth.TrainCyclicCutIndexAtSourceTwo
import Girth.TrainActualCutIndexedBigCycle
import Mathlib.Tactic

set_option autoImplicit false
set_option Elab.async false

/-!
# Actual n=2 mixed connectors are lower cut connectors

The original source is NOT a witness cycle. We instead take the
existing geometric cut-indexed witness of the original source.
When n=2 and there are exactly two geometric owner changes, both
cut indices are literally 0 and 1 (not a silently assumed rotation).

The verified connector transport maps the two witness contacts to
the two ACTUAL original output contacts. In a mixed source this
forces the output vertex to have a genuine core-vertex preimage
and the output wagon to have a genuine core-wagon preimage.
The physical original-B mixed supreme theorem can therefore be
applied without assuming those preimages.

No output girth, source-label/owner identification, or appendix.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure
universe u v
section ActualN2MixedCutRealization

variable {L : RelLanguage.{u}} {UA VB P X Y I : Type v}
variable (A : RelStructure L UA) (hA : A.Irreducible)
variable (B : RelStructure L VB) (D : RelStructure L P)
variable (C : StructuralRamsey.Partite.System L P X)
variable (family : Set (Embedding B D))
variable (selected : Set (DesignatedCopy B D C family))
variable (e : Embedding A D) (R : RelStructure L Y)
variable (f : I → Embedding
  (C.toRelStructure.induce (activeCarrier A C e.toFunctionEmbedding)) R)
variable {m : ℕ}
variable (T : EdgeTrainLevels (OldACarrierEdge A C.toRelStructure) m)
variable (U : EdgeTrainLevels (OldACarrierEdge A R) m)
variable (hShared : ∀ _i : I, Nonempty
  (SharedOldACarrierEdge A C.toRelStructure
    (activeCarrier A C e.toFunctionEmbedding)))
variable (hRel : ∀ (ν : Fin (m + 1)) (j : I)
  (p q : SharedOldACarrierEdge A C.toRelStructure
    (activeCarrier A C e.toFunctionEmbedding)),
  T.rel ν p.1 q.1 ↔
    U.rel ν (sharedOldACarrierCoreEmbedding A C.toRelStructure
      (activeCarrier A C e.toFunctionEmbedding) R f j p)
      (sharedOldACarrierCoreEmbedding A C.toRelStructure
        (activeCarrier A C e.toFunctionEmbedding) R f j q))
variable (μ : Fin (m + 1))

local notation "S" => activeCarrier A C e.toFunctionEmbedding
local notation "Vertex" =>
  RelStructure.Attachment.Vertex S (W := Y) (I := I)
local notation "Selected" =>
  {q : DesignatedCopy B D C family // q ∈ selected}
local notation "OldEdge" => OldACarrierEdge A C.toRelStructure
local notation "CoreEdge" => OldACarrierEdge A R
local notation "CoreEmb" => RelStructure.Attachment.coreEmbedding
  C.toRelStructure S R f
local notation "Train" => generatedActualASupportTrain
  A hA C.toRelStructure S R f T U hShared
local notation "CoreWagon" => generatedActualASupportTrain_coreWagonEmbedding
  A hA C.toRelStructure S R f T U
  (fun ν j p q h => (hRel ν j p q).mp h) hShared μ
local notation "Out" => attachedSelectedPictureOrderOneData
  A hA B D C family selected e R f T U hShared μ
local notation "Old" => selectedPictureOrderOneData
  A B D C family selected T μ
local notation "Wit" => sharedWitnessOrderOneData U μ
  (sharedOldACarrierCoreEmbedding A C.toRelStructure S R f)
  (Subtype.val : CoreEdge → Set Y)
local notation "GeomAllowed" => selectedOutputGeometricOwnerAllowed
  A hA B D C family selected e R f T U hShared μ

include hRel

/-- A mixed pair of ACTUAL source connectors comes from a genuine
lower witness vertex and wagon, with literal source indices intact. -/
theorem attachedSelectedPicture_two_cycle_mixed_cut_connector_realization
    (K : (Out).BigCycle 2)
    (owner : Fin 2 → I ⊕ CoreEdge)
    (hAllowed : ∀ j, GeomAllowed (K.label j) (owner j))
    (hTwo : cyclicOwnerChanges owner = 2)
    (hShape :
      (∃ (v : Vertex) (w : Quotient ((Train).wagonSetoid μ)),
        K.connector 0 = Sum.inl v ∧ K.connector 1 = Sum.inr w) ∨
      (∃ (v : Vertex) (w : Quotient ((Train).wagonSetoid μ)),
        K.connector 0 = Sum.inr w ∧ K.connector 1 = Sum.inl v)) :
    ∃ (x : Y) (p : Quotient (U.wagonSetoid μ)),
      (K.connector 0 = Sum.inl (CoreEmb x) ∧
        K.connector 1 = Sum.inr (CoreWagon p)) ∨
      (K.connector 0 = Sum.inr (CoreWagon p) ∧
        K.connector 1 = Sum.inl (CoreEmb x)) := by
  classical
  let j0 : Fin (cyclicOwnerChanges owner) := ⟨0, by omega⟩
  let j1 : Fin (cyclicOwnerChanges owner) := ⟨1, by omega⟩
  have hi0 : cyclicOwnerCutIndex owner j0 = (0 : Fin 2) := by
    apply Fin.ext
    simpa [j0] using
      (cyclicOwnerCutIndex_val_eq_of_source_two owner hTwo j0)
  have hi1 : cyclicOwnerCutIndex owner j1 = (1 : Fin 2) := by
    apply Fin.ext
    simpa [j1] using
      (cyclicOwnerCutIndex_val_eq_of_source_two owner hTwo j1)
  let Z := attachedSelectedPicture_geometric_cutBigCycle
    A hA B D C family selected e R f T U hShared hRel μ
    K owner hAllowed (by omega : 2 ≤ cyclicOwnerChanges owner)
  have hmap0 : Sum.map CoreEmb CoreWagon (Z.connector j0) =
      K.connector (0 : Fin 2) := by
    simpa only [hi0] using
      (attachedSelectedPicture_cutConnector_eq
        A hA B D C family selected e R f T U hShared hRel μ
        K owner hAllowed j0)
  have hmap1 : Sum.map CoreEmb CoreWagon (Z.connector j1) =
      K.connector (1 : Fin 2) := by
    simpa only [hi1] using
      (attachedSelectedPicture_cutConnector_eq
        A hA B D C family selected e R f T U hShared hRel μ
        K owner hAllowed j1)
  rcases hShape with ⟨v, w, h0, h1⟩ | ⟨v, w, h0, h1⟩
  · cases hc0 : Z.connector j0 with
    | inl x =>
        cases hc1 : Z.connector j1 with
        | inl y =>
            simp [hc1, h1] at hmap1
        | inr p =>
            refine ⟨x, p, Or.inl ⟨?_, ?_⟩⟩
            · simpa [hc0] using hmap0.symm
            · simpa [hc1] using hmap1.symm
    | inr p =>
        simp [hc0, h0] at hmap0
  · cases hc0 : Z.connector j0 with
    | inl x =>
        simp [hc0, h0] at hmap0
    | inr p =>
        cases hc1 : Z.connector j1 with
        | inl x =>
            refine ⟨x, p, Or.inr ⟨?_, ?_⟩⟩
            · simpa [hc0] using hmap0.symm
            · simpa [hc1] using hmap1.symm
        | inr q =>
            simp [hc1, h1] at hmap1

/-- Close the genuine selected B-labelled mixed source from its
ORIGINAL mixed sort, not from separately assumed core preimages. -/
theorem attachedSelectedPicture_two_cycle_mixed_shape_full_supreme
    [Finite UA]
    (hBaseStrong : ∀ q : Selected,
      AStrong A D (copyCarrier q.1.base))
    (hTwoEdges : ∀ q : Selected, ∃ r s : OldEdge,
      r ≠ s ∧ r.1 ⊆ copyCarrier q.1.embedding ∧
        s.1 ⊆ copyCarrier q.1.embedding)
    {qcut : ℕ} (hq : 1 ≤ qcut)
    (hOld : (Old).SupremeCycleBound qcut)
    (hWitness : (Wit).FullSystemGirthGT qcut)
    (K : (Out).BigCycle 2) (hAccept : K.Acceptable)
    (owner : Fin 2 → I ⊕ CoreEdge)
    (hAllowed : ∀ j, GeomAllowed (K.label j) (owner j))
    (hTwo : cyclicOwnerChanges owner = 2)
    (target : Fin 2) (i : I) (q : Selected)
    (hOriginal : K.label target = Sum.inl (i, q))
    (hShape :
      (∃ (v : Vertex) (w : Quotient ((Train).wagonSetoid μ)),
        K.connector 0 = Sum.inl v ∧ K.connector 1 = Sum.inr w) ∨
      (∃ (v : Vertex) (w : Quotient ((Train).wagonSetoid μ)),
        K.connector 0 = Sum.inr w ∧ K.connector 1 = Sum.inl v)) :
    K.HasSimultaneousSupreme := by
  obtain ⟨x, p, hMixed⟩ :=
    attachedSelectedPicture_two_cycle_mixed_cut_connector_realization
      A hA B D C family selected e R f T U hShared hRel μ
      K owner hAllowed hTwo hShape
  exact attachedSelectedPicture_two_cycle_mixed_full_supreme_of_two_edge_base
    A hA B D C family selected e R f T U hShared hRel μ
    hBaseStrong hTwoEdges hq hOld hWitness
    K hAccept owner hAllowed hTwo
    target i q hOriginal x p hMixed

end ActualN2MixedCutRealization
end StructuralRamsey.Girth
