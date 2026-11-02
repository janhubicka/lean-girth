import Girth.TrainActiveGluingWitness
import Girth.TrainSelectedPictureTwoStandard
import Girth.TrainDesignatedReindexGirth
import Girth.TrainRecursiveWitnessPass

set_option autoImplicit false

/-!
# Exact selected-copy to gluing-index incidence comparison

The source and output partite systems may have DIFFERENT part types.
The comparison uses their literal relational induced target, complete
physical ambient edge family and exact quotient labels.  No equality
between old and new part maps is required.

The full-system girth certificates provided by a recursive selected
picture are indexed by its ACTUAL selected-copy labels.  The gluing
operator uses a separately prescribed family of embeddings.  To reuse
the former as certificates for the latter, a genuine equivalence of
designated labels and equality of their physical carriers are needed.

With those two data, the complete OrderOneData structures agree after
reindexing designated labels.  This includes the FULL set of physical
ambient A-edges, their parent quotient wagons, and every physical edge
contained in each designated carrier.  The simultaneous supreme-cycle
bound transports at the same cutoff: no extra linearity or cycle
hypothesis is assumed.

Constructing this equivalence for the actual fine recursive target and
its prescribed gluing family is a separate obligation; the theorem
does not pretend that coincident vertex carriers imply equal labels.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}} {UA VB P Q X Y I : Type v}
variable (A : RelStructure L UA) (B : RelStructure L VB)
variable (D : RelStructure L Q)
variable (Old : StructuralRamsey.Partite.System L P X)
variable (New : StructuralRamsey.Partite.System L Q Y)
variable (family : Set (Embedding B D))
variable (selected : Set (DesignatedCopy B D New family))
variable (α : UA → P)
variable (f : I → Embedding
  (Old.toRelStructure.induce (activeCarrier A Old α)) New.toRelStructure)
variable {m : ℕ}
variable (T : EdgeTrainLevels (OldACarrierEdge A New.toRelStructure) m)
variable (μ : Fin (m + 1))
variable (e : I ≃ {q : DesignatedCopy B D New family // q ∈ selected})

/-- After an actual bijective match of designated-copy labels, matching
physical carriers makes the ENTIRE local gluing incidence record equal to
the selected-picture incidence record, including membership of every
ambient support edge and the unchanged train quotient. -/
theorem activeGluingWitness_eq_reindexed_selectedPicture
    (hCarrier : ∀ i : I, copyCarrier (f i) =
      copyCarrier (e i).1.embedding) :
    activeGluingWitnessOrderOneData A Old α New.toRelStructure f T μ =
      (selectedPictureOrderOneData A B D New family selected T μ).reindexDesignated e := by
  have hCopy :
      (fun i : I => copyCarrier (f i)) =
        (fun i : I => copyCarrier (e i).1.embedding) := by
    funext i
    exact hCarrier i
  have hEdges :
      (fun i : I =>
        {a : OldACarrierEdge A New.toRelStructure | a.1 ⊆ copyCarrier (f i)}) =
      (fun i : I =>
        {a : OldACarrierEdge A New.toRelStructure | a.1 ⊆
          copyCarrier (e i).1.embedding}) := by
    funext i
    exact congrArg
      (fun s : Set Y => {a : OldACarrierEdge A New.toRelStructure | a.1 ⊆ s})
      (hCarrier i)
  unfold activeGluingWitnessOrderOneData selectedPictureOrderOneData
    OrderOneData.reindexDesignated
  simp only [hCopy, hEdges]

/-- An indexed full-system-girth certificate for one record is exactly
one for the other.  This is an iff, not a one-way approximation, and
transports global simultaneous supreme plans rather than only local
short/long pieces. -/
theorem activeGluingWitness_fullSystemGirth_iff_selectedPicture
    (hCarrier : ∀ i : I, copyCarrier (f i) =
      copyCarrier (e i).1.embedding) (q : ℕ) :
    (activeGluingWitnessOrderOneData A Old α New.toRelStructure f T μ).FullSystemGirthGT q ↔
      (selectedPictureOrderOneData A B D New family selected T μ).FullSystemGirthGT q := by
  rw [activeGluingWitness_eq_reindexed_selectedPicture
    A B D Old New family selected α f T μ e hCarrier]
  exact OrderOneData.reindexDesignated_fullSystemGirth_iff
    (selectedPictureOrderOneData A B D New family selected T μ) e q


section CanonicalSelectedIndices

local notation "Source" =>
  Old.toRelStructure.induce (activeCarrier A Old α)
variable (lowerFamily : Set (Embedding Source D))
variable (lowerSelected : Set (DesignatedCopy Source D New lowerFamily))
variable {n : ℕ} (U : EdgeTrainLevels (OldACarrierEdge A New.toRelStructure) n)
variable (ν : Fin (n + 1))

/-- If the gluing indices are literally the selected local target copies,
the local gluing record and the selected-picture record are the SAME
complete incidence data.  No chosen equivalence or image-based
identification of distinct selected labels is needed. -/
theorem activeGluingWitness_eq_selectedPicture_of_canonicalIndices :
    activeGluingWitnessOrderOneData A Old α New.toRelStructure
      (fun q : {q : DesignatedCopy Source D New lowerFamily //
          q ∈ lowerSelected} => q.1.embedding) U ν =
    selectedPictureOrderOneData A Source D New lowerFamily lowerSelected U ν := by
  rfl

/-- Therefore the actual lower-stage selected-copy system bound is
already precisely the indexed gluing bound whenever the canonical
selected labels themselves are used as the gluing index family. -/
theorem activeGluingWitness_fullSystemGirth_iff_canonicalIndices
    (q : ℕ) :
    (activeGluingWitnessOrderOneData A Old α New.toRelStructure
      (fun i : {i : DesignatedCopy Source D New lowerFamily //
          i ∈ lowerSelected} => i.1.embedding) U ν).FullSystemGirthGT q ↔
    (selectedPictureOrderOneData A Source D New lowerFamily lowerSelected
      U ν).FullSystemGirthGT q := by
  rfl

end CanonicalSelectedIndices

section CanonicalForestTailStage

local notation "Source" =>
  Old.toRelStructure.induce (activeCarrier A Old α)
variable (lowerFamily : Set (Embedding Source D))
variable {t : List ℕ}
variable {targetTrain : EdgeTrainLevels (OldACarrierEdge A Source) t.length}
variable {allowed : Fin (t.length + 1) → Set Q}

/-- If a lower recursive forest-tail stage is built with the exact
physical active induced target and its ACTUAL selected copies are used as
the gluing indices, its existing tail-girth certificate already applies
to the entire local gluing incidence record at the identical cutoff.
The matching of the stage's source type with this active induced target
is explicit in the statement; this does NOT produce the lower stage,
its prescribed Ramsey family or any arbitrary external gluing indices. -/
theorem TrainRecursiveWitness.ForestTailStage.gluingFullSystemGirth_of_canonicalSelected
    (S : TrainRecursiveWitness.ForestTailStage A Source D lowerFamily
      t targetTrain allowed)
    (j : Fin t.length) (hj : 0 < j.val) :
    (activeGluingWitnessOrderOneData A Old α S.system.toRelStructure
      (fun i : {i : DesignatedCopy Source D S.system lowerFamily //
        i ∈ S.selected} => i.1.embedding)
      S.train j.castSucc).FullSystemGirthGT (t.get j) := by
  change (selectedPictureOrderOneData A Source D S.system
    lowerFamily S.selected S.train j.castSucc).FullSystemGirthGT (t.get j)
  exact S.tailGirth j hj

end CanonicalForestTailStage

end StructuralRamsey.Girth
