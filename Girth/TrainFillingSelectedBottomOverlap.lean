import Girth.TrainSelectedPictureTwoStandard
import Girth.TrainThreeLabelWagonProbe
import Girth.TrainFullGirthCopyStrongness

set_option autoImplicit false

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v

variable {L : RelLanguage.{u}} {A B Base Y : Type v}

/-- At the shortened equality cut, any distinct pair shared by two
selected parents belongs to an actual old edge contained in both parents.
This identifies the canonical template placement for the two vertices
when comparing overlapping fine target copies. -/
theorem selectedPictureBottom_commonEdge_of_sharedPair
    (source : RelStructure L A) (target : RelStructure L B)
    (D : RelStructure L Base) (N : StructuralRamsey.Partite.System L Base Y)
    (family : Set (Embedding target D))
    (selected : Set (DesignatedCopy target D N family))
    {m q : ℕ} (train : EdgeTrainLevels (OldACarrierEdge source N.toRelStructure) m)
    (hq : 2 ≤ q)
    (hFull : (selectedPictureOrderOneData source target D N family selected train 0).FullSystemGirthGT q)
    (i j : {b : DesignatedCopy target D N family // b ∈ selected})
    (hij : i ≠ j) (x y : Y) (hxy : x ≠ y)
    (hix : x ∈ copyCarrier i.1.embedding) (hiy : y ∈ copyCarrier i.1.embedding)
    (hjx : x ∈ copyCarrier j.1.embedding) (hjy : y ∈ copyCarrier j.1.embedding) :
    ∃ e : OldACarrierEdge source N.toRelStructure,
      x ∈ e.1 ∧ y ∈ e.1 ∧ e.1 ⊆ copyCarrier i.1.embedding ∧
        e.1 ⊆ copyCarrier j.1.embedding := by
  let O := selectedPictureOrderOneData source target D N family selected train 0
  have hLocal : O.LocalPieceSystemBound 2 := by
    intro n C hAccept hOrder
    exact O.localPieceSystemBound_of_supremeCycleBound q hFull.2
      n C hAccept (hOrder.trans (Nat.mul_le_mul_left 2 hq))
  obtain ⟨p, hx, hy⟩ := O.common_wagon_of_two_copy_vertex_pair hLocal
    i j x y hij hxy hix hiy hjx hjy
  obtain ⟨e, hep, he⟩ := hx
  obtain ⟨f, hfp, hf⟩ := hy
  have hParents : Quotient.mk (train.wagonSetoid 0) e =
      Quotient.mk (train.wagonSetoid 0) f := hep.trans hfp.symm
  have hef : e = f := (train.bottom e f).mp (Quotient.exact hParents)
  subst f
  exact ⟨e, he, hf,
    O.copy_edge_of_pair_of_fullSystemGirth q hq hFull i e x y hxy hix hiy he hf,
    O.copy_edge_of_pair_of_fullSystemGirth q hq hFull j e x y hxy hjx hjy he hf⟩

end StructuralRamsey.Girth
