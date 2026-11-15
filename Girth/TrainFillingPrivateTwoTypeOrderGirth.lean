import Girth.TrainFillingOrderStageCanonicalAllCutGirth
import Girth.TrainFillingTemplateConstruction

set_option Elab.async false

/-!
# Canonical OrderStage filling with DIFFERENT old and template edge types

CRITICAL CUTOFF-TWO DISTINCTION:

The lower RR_h witness has old edges of a large coloured type
Aold, whose vertices are the WHOLE ordered set V(X).
The inserted template hypergraph R on X has edges of the
ORIGINAL SMALL coloured type Asmall (denoted E_a in the paper).

These may have DIFFERENT edge cardinalities, different relation
languages and different linearity assertions.

The previous checked theorem
  OrderStage.canonicalFilledCut_fullSystemGirthGT
applied one SAME source A to both the old selected support
and the template R. That is a useful special case but does NOT
by itself justify the actual cutoff-two application.

Here we keep Aold and Asmall, as well as their relational
languages, INDEPENDENT. The old edge carriers are literally
the Aold support of the genuine selected lower OrderStage;
the generated template edges are the Asmall support of R.
The checked filling theorem needs only:
  - full old system girth from OrderStage.allCutGirth,
  - linearity of all physical old edges,
  - linearity of Asmall-support inside each new filled fibre,
  - full template support coverage, so the vertex carriers
    and the selected incidence records do not change.

No Aold embedding into R or Asmall embedding into the
lower selected N is postulated: those generally do not exist
for the genuine cutoff-two large/small types.

The conclusion is precisely the complete N[X] inherited
cut with all old designated parents, at EVERY old proper
cut including the old equality cut. Neither output girth
nor its intended consequence is an input hypothesis.

Source candidate, not a Lean kernel certificate until built.
-/

namespace StructuralRamsey.Girth.TrainRecursiveWitness

open StructuralRamsey.RelStructure

universe u0 u1 v

variable {Lold : RelLanguage.{u0}}
variable {Lsmall : RelLanguage.{u1}}
variable {Uold Usmall VB P X : Type v}

variable (Aold : RelStructure Lold Uold) [Nontrivial Uold]
variable (B : RelStructure Lold VB)
variable (D : RelStructure Lold P)
variable (family : Set (Embedding B D))
variable {t : List ℕ}
variable {targetTrain : EdgeTrainLevels (OldACarrierEdge Aold B) t.length}
variable {allowed : Fin (t.length + 1) → Set P}

/-- The original shorter OrderStage gives the EXACT filled
full-system-girth bound for arbitrary local template edge type
Asmall. Old and new relational languages and edge sizes are
independent, as required by direct cutoff two.

This theorem is an explicit two-type generalization of the
already checked one-type canonical filling theorem, proved
using the SAME generic fibre-linear filling transfer. -/
theorem OrderStage.canonicalFilledCut_fullSystemGirthGT_twoTypes
    (S : OrderStage Aold B D family t targetTrain allowed)
    (Asmall : RelStructure Lsmall Usmall) [Nontrivial Usmall]
    (R : RelStructure Lsmall X)
    (place : OldACarrierEdge Aold S.system.toRelStructure →
      (X ↪ S.Vertex))
    (hRange : ∀ f, Set.range (place f) = f.1)
    (hCovers : ∀ x : X, ∃ a : Embedding Asmall R,
      x ∈ copyCarrier a)
    (hSmallLinear : ALinear Asmall R)
    (j : Fin t.length) :
    let H : UniformFillingData S.Vertex X :=
      UniformFillingData.ofSupportCopies Asmall R
        (supportCopies Aold S.system.toRelStructure)
        place hRange
        (oldACarrier_edges_inter_subsingleton_of_aLinear
          Aold S.system.toRelStructure S.aLinear)
        hCovers
    (H.toTrainFilling.inheritedCutData S.train
      (fun i : {b : DesignatedCopy B D S.system family //
                 b ∈ S.selected} =>
        copyCarrier i.1.embedding)
      (fun i : {b : DesignatedCopy B D S.system family //
                 b ∈ S.selected} =>
        {e : H.OldEdge | e.1 ⊆ copyCarrier i.1.embedding})
      j.castSucc).FullSystemGirthGT (t.get j) := by
  let H : UniformFillingData S.Vertex X :=
    UniformFillingData.ofSupportCopies Asmall R
      (supportCopies Aold S.system.toRelStructure)
      place hRange
      (oldACarrier_edges_inter_subsingleton_of_aLinear
        Aold S.system.toRelStructure S.aLinear)
      hCovers
  apply H.toTrainFilling.inheritedCutData_fullSystemGirthGT_of_fibreLinearity
    S.train
    (fun i : {b : DesignatedCopy B D S.system family //
               b ∈ S.selected} =>
      copyCarrier i.1.embedding)
    (fun i : {b : DesignatedCopy B D S.system family //
               b ∈ S.selected} =>
      {e : H.OldEdge | e.1 ⊆ copyCarrier i.1.embedding})
    j.castSucc
  · change (selectedPictureOrderOneData Aold B D S.system family
      S.selected S.train j.castSucc).FullSystemGirthGT (t.get j)
    exact S.allCutGirth j
  · exact H.fibre_linear
      (oldACarrier_edges_inter_subsingleton_of_aLinear
        Asmall R hSmallLinear)

end StructuralRamsey.Girth.TrainRecursiveWitness
