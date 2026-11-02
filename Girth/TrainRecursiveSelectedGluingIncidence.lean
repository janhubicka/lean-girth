import Girth.TrainActiveGluingWitness
import Girth.TrainSelectedPictureTwoStandard
import Girth.TrainDesignatedReindexGirth

set_option autoImplicit false

/-!
# Exact selected-copy to gluing-index incidence comparison

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
variable {L : RelLanguage.{u}} {UA VB P X I : Type v}
variable (A : RelStructure L UA) (B : RelStructure L VB)
variable (D : RelStructure L P)
variable (C : StructuralRamsey.Partite.System L P X)
variable (family : Set (Embedding B D))
variable (selected : Set (DesignatedCopy B D C family))
variable (α : UA → P)
variable (f : I → Embedding
  (C.toRelStructure.induce (activeCarrier A C α)) C.toRelStructure)
variable {m : ℕ}
variable (T : EdgeTrainLevels (OldACarrierEdge A C.toRelStructure) m)
variable (μ : Fin (m + 1))
variable (e : I ≃ {q : DesignatedCopy B D C family // q ∈ selected})

/-- After an actual bijective match of designated-copy labels, matching
physical carriers makes the ENTIRE local gluing incidence record equal to
the selected-picture incidence record, including membership of every
ambient support edge and the unchanged train quotient. -/
theorem activeGluingWitness_eq_reindexed_selectedPicture
    (hCarrier : ∀ i : I, copyCarrier (f i) =
      copyCarrier (e i).1.embedding) :
    activeGluingWitnessOrderOneData A C α C.toRelStructure f T μ =
      (selectedPictureOrderOneData A B D C family selected T μ).reindexDesignated e := by
  have hCopy :
      (fun i : I => copyCarrier (f i)) =
        (fun i : I => copyCarrier (e i).1.embedding) := by
    funext i
    exact hCarrier i
  have hEdges :
      (fun i : I =>
        {a : OldACarrierEdge A C.toRelStructure | a.1 ⊆ copyCarrier (f i)}) =
      (fun i : I =>
        {a : OldACarrierEdge A C.toRelStructure | a.1 ⊆
          copyCarrier (e i).1.embedding}) := by
    funext i
    exact congrArg
      (fun s : Set X => {a : OldACarrierEdge A C.toRelStructure | a.1 ⊆ s})
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
    (activeGluingWitnessOrderOneData A C α C.toRelStructure f T μ).FullSystemGirthGT q ↔
      (selectedPictureOrderOneData A B D C family selected T μ).FullSystemGirthGT q := by
  rw [activeGluingWitness_eq_reindexed_selectedPicture
    A B D C family selected α f T μ e hCarrier]
  exact OrderOneData.reindexDesignated_fullSystemGirth_iff
    (selectedPictureOrderOneData A B D C family selected T μ) e q

end StructuralRamsey.Girth
