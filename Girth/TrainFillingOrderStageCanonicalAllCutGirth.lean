import Girth.TrainFillingTemplateConstruction
import Girth.TrainRecursiveWitnessPass
import Girth.TrainSelectedPictureTwoStandard

set_option Elab.async false

/-!
# All proper filled system-girth cuts from the ACTUAL shorter OrderStage

The cutoff-two argument invokes the shorter ORDER/Ramsey assertion.
Its witness is an OrderStage, not merely a ForestTailStage. The
checked OrderStage.allCutGirth contains full simultaneous A2/A3
system girth at EVERY old proper cut, including equality zero.

For the canonical template filling, old edge carriers are literally
the complete A-support of that shorter stage. Hence its old
incidence record has the same physical support edges, selected
designated M-copies, parent quotient, vertex carriers and copy-edge
families as the genuine OrderStage.selectedPictureOrderOneData.

Apply the checked full-system-girth filling transfer at each cut
without first deriving a false forest-through-2q invariant. This
theorem changes neither the target girth hypotheses nor the old
allCutGirth index and introduces no top-cut girth requirement.

This generic real-filling theorem is independent of the
choice-tagged G0 representation; that separate integration remains
in Track C candidate PR #943. The selected G0 physical lift and
final Ramsey arrow are NOT proved by this statement alone.
-/

namespace StructuralRamsey.Girth.TrainRecursiveWitness

open StructuralRamsey.RelStructure

universe u v

variable {L : RelLanguage.{u}} {UA VB P X : Type v}
variable (A : RelStructure L UA) [Nontrivial UA]
variable (B : RelStructure L VB) (D : RelStructure L P)
variable (family : Set (Embedding B D))
variable {t : List ℕ}
variable {targetTrain : EdgeTrainLevels (OldACarrierEdge A B) t.length}
variable {allowed : Fin (t.length + 1) → Set P}

/-- The complete shortened ORDER witness supplies the old
full-system-girth input for every proper inherited cut, including
the first restored positive coordinate from old equality zero.
The only additional geometry is ordinary linearity of the local
template A-support and full coverage of its vertices. -/
theorem OrderStage.canonicalFilledCut_fullSystemGirthGT
    (S : OrderStage A B D family t targetTrain allowed)
    (R : RelStructure L X)
    (place : OldACarrierEdge A S.system.toRelStructure → (X ↪ S.Vertex))
    (hRange : ∀ f, Set.range (place f) = f.1)
    (hCovers : ∀ x : X, ∃ a : Embedding A R, x ∈ copyCarrier a)
    (hLocalLinear : ALinear A R)
    (j : Fin t.length) :
    let H := UniformFillingData.ofSupportCopies A R
      (supportCopies A S.system.toRelStructure) place hRange
      (oldACarrier_edges_inter_subsingleton_of_aLinear
        A S.system.toRelStructure S.aLinear)
      hCovers
    (H.toTrainFilling.inheritedCutData S.train
      (fun i : {b : DesignatedCopy B D S.system family // b ∈ S.selected} =>
        copyCarrier i.1.embedding)
      (fun i : {b : DesignatedCopy B D S.system family // b ∈ S.selected} =>
        {e : H.OldEdge | e.1 ⊆ copyCarrier i.1.embedding})
      j.castSucc).FullSystemGirthGT (t.get j) := by
  let H : UniformFillingData S.Vertex X :=
    UniformFillingData.ofSupportCopies A R
      (supportCopies A S.system.toRelStructure) place hRange
      (oldACarrier_edges_inter_subsingleton_of_aLinear
        A S.system.toRelStructure S.aLinear)
      hCovers
  apply H.toTrainFilling.inheritedCutData_fullSystemGirthGT_of_fibreLinearity
    S.train
    (fun i : {b : DesignatedCopy B D S.system family // b ∈ S.selected} =>
      copyCarrier i.1.embedding)
    (fun i : {b : DesignatedCopy B D S.system family // b ∈ S.selected} =>
      {e : H.OldEdge | e.1 ⊆ copyCarrier i.1.embedding})
    j.castSucc
  · change (selectedPictureOrderOneData A B D S.system family
        S.selected S.train j.castSucc).FullSystemGirthGT (t.get j)
    exact S.allCutGirth j
  · exact H.fibre_linear
      (oldACarrier_edges_inter_subsingleton_of_aLinear A R hLocalLinear)

end StructuralRamsey.Girth.TrainRecursiveWitness
