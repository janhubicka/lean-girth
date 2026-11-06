import Girth.TrainRecursiveFineWitnessTransport
import Girth.TrainAllAdjacentParameterPreservation
import Girth.ActualActivePartitePresentation

set_option autoImplicit false
set_option Elab.async false

/-!
# Adjacent target parameters under honest active-support restriction

The genuine recursive source contains exactly the A-copies of an induced
active relational substructure, not a larger part fibre.  Restricting
the train first to shared physical old A-edges and then to the induced
source preserves sibling-intersection parameters.  The proof uses
injective maps on BOTH physical edge labels and vertices, and never
identifies labels which have equal carriers.

The target allowed parts are literal preimages of the OLD allowed
base-part sets along the processed A-base embedding.

This settles the ORIGINAL retained train's adjacent parameters on
the true active source.  Adjacent parameters at the newly inserted
refinement levels require the refinement's own parent intersection
certificates and are treated separately.
-/

namespace StructuralRamsey.Girth

universe v
variable {E F V W : Type v}

/-- An injective restriction of physical edge labels, together with an
injective transport of physical vertices and a pullback of permitted
vertex sets, preserves every adjacent sibling intersection bound.
The train's quotient wagon labels remain distinguishable. -/
theorem EdgeTrainLevels.adjacentParameters_restrict_of_vertexEmbedding
    {m : ℕ} (T : EdgeTrainLevels E m)
    (old : E → Set W) (keep : F ↪ E)
    (emb : V ↪ W) (new : F → Set V)
    (hMaps : ∀ (a : F) (x : V), x ∈ new a → emb x ∈ old (keep a))
    (oldAllowed : Fin (m + 1) → Set W)
    (newAllowed : Fin (m + 1) → Set V)
    (hAllow : ∀ (ν : Fin (m + 1)) (x : V),
      emb x ∈ oldAllowed ν → x ∈ newAllowed ν)
    (hOld : T.AdjacentParameters old oldAllowed) :
    (T.restrict keep).AdjacentParameters new newAllowed := by
  intro μ ν hμν hNext a b hne hParent x hx
  have hNeOld :
      T.wagonClassEmbedding keep μ a ≠
        T.wagonClassEmbedding keep μ b :=
    fun heq => hne ((T.wagonClassEmbedding keep μ).injective heq)
  have hParentOld :
      T.wagonParent μ ν hμν (T.wagonClassEmbedding keep μ a) =
        T.wagonParent μ ν hμν (T.wagonClassEmbedding keep μ b) := by
    induction a using Quotient.inductionOn with
    | h a =>
      induction b using Quotient.inductionOn with
      | h b =>
        have hAtParent :
            Quotient.mk ((T.restrict keep).wagonSetoid ν) a =
              Quotient.mk ((T.restrict keep).wagonSetoid ν) b := hParent
        have hRel : T.rel ν (keep a) (keep b) :=
          Quotient.exact hAtParent
        exact Quotient.sound hRel
  have hCarrier (c : Quotient ((T.restrict keep).wagonSetoid μ))
      (z : V) :
      z ∈ (T.restrict keep).wagonClassCarrier new μ c →
        emb z ∈ T.wagonClassCarrier old μ
          (T.wagonClassEmbedding keep μ c) := by
    induction c using Quotient.inductionOn with
    | h a =>
      change z ∈ (T.restrict keep).wagonCarrier new μ a →
        emb z ∈ T.wagonCarrier old μ (keep a)
      rintro ⟨b, hab, hzb⟩
      exact ⟨keep b, hab, hMaps b z hzb⟩
  exact hAllow ν x
    ((hOld μ ν hμν hNext) hNeOld hParentOld
      ⟨hCarrier a x hx.1, hCarrier b x hx.2⟩)

end StructuralRamsey.Girth

namespace StructuralRamsey.Girth.TrainRecursiveWitness

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}} {UA VB P : Type v}
variable {A : RelStructure L UA} {B : RelStructure L VB}
variable {D : RelStructure L P}
variable {family : Set (Embedding B D)} {t : List ℕ}
variable {targetTrain : EdgeTrainLevels (OldACarrierEdge A B) t.length}
variable {allowed : Fin (t.length + 1) → Set P}

/-- The OLD train's complete adjacent parameters hold on the genuinely
induced active A-support, with its own canonical A-parts.  No new
physical support is introduced, and all vertex/edge restriction maps
are genuine injections. -/
theorem ForestTailStage.trueActive_inducedAdjacentParameters
    (stage : ForestTailStage A B D family t targetTrain allowed)
    (e : Embedding A D) :
    ((stage.train.restrict
      (sharedOldACarrierInclusion A stage.system.toRelStructure
        (activeCarrier A stage.system e.toFunctionEmbedding))).restrict
      (inducedACarrierToShared A stage.system.toRelStructure
        (activeCarrier A stage.system e.toFunctionEmbedding))).AdjacentParameters
      (fun edge : OldACarrierEdge A
        (stage.system.toRelStructure.induce
          (activeCarrier A stage.system e.toFunctionEmbedding)) => edge.1)
      (fun ν =>
        (actualActiveSubsystemPartite A stage.system
          e.toFunctionEmbedding).part ⁻¹'
          (e.toFunctionEmbedding ⁻¹' allowed ν)) := by
  let S := activeCarrier A stage.system e.toFunctionEmbedding
  let α := e.toFunctionEmbedding
  let Tshared := stage.train.restrict
    (sharedOldACarrierInclusion A stage.system.toRelStructure S)
  let idVertex : stage.Vertex ↪ stage.Vertex :=
    ⟨id, fun _ _ h => h⟩
  let inclusion : S ↪ stage.Vertex :=
    ⟨Subtype.val, Subtype.val_injective⟩
  have hShared : Tshared.AdjacentParameters
      (fun edge : SharedOldACarrierEdge A stage.system.toRelStructure S => edge.1.1)
      (fun ν => stage.system.part ⁻¹' allowed ν) := by
    apply stage.train.adjacentParameters_restrict_of_vertexEmbedding
      (fun edge : OldACarrierEdge A stage.system.toRelStructure => edge.1)
      (sharedOldACarrierInclusion A stage.system.toRelStructure S)
      idVertex
      (fun edge : SharedOldACarrierEdge A stage.system.toRelStructure S => edge.1.1)
      (by intro a x hx; exact hx)
      (fun ν => stage.system.part ⁻¹' allowed ν)
      (fun ν => stage.system.part ⁻¹' allowed ν)
      (by intro ν x hx; exact hx)
      stage.parameters
  change (Tshared.restrict
      (inducedACarrierToShared A stage.system.toRelStructure S)).AdjacentParameters
      (fun edge : OldACarrierEdge A (stage.system.toRelStructure.induce S) =>
        edge.1)
      (fun ν =>
        (actualActiveSubsystemPartite A stage.system α).part ⁻¹'
          (α ⁻¹' allowed ν))
  apply Tshared.adjacentParameters_restrict_of_vertexEmbedding
    (fun edge : SharedOldACarrierEdge A stage.system.toRelStructure S => edge.1.1)
    (inducedACarrierToShared A stage.system.toRelStructure S)
    inclusion
    (fun edge : OldACarrierEdge A (stage.system.toRelStructure.induce S) =>
      edge.1)
    (by
      intro a x hx
      change x.val ∈ Subtype.val '' a.1
      exact ⟨x, hx, rfl⟩)
    (fun ν => stage.system.part ⁻¹' allowed ν)
    (fun ν => (actualActiveSubsystemPartite A stage.system α).part ⁻¹'
      (α ⁻¹' allowed ν))
    (by
      intro ν x hx
      change α (activeSourcePart A stage.system α x) ∈ allowed ν
      rw [activeSourcePart_spec A stage.system α x]
      exact hx)
    hShared

end StructuralRamsey.Girth.TrainRecursiveWitness
