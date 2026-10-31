import Girth.TrainSystemCutAllWagonWindow
import Girth.TrainSystemCutPhysicalPieces

/-!
# Full system-girth yields the labelled horizontal wagon-cut bound

This is the missing converse used by the circulation train recursion.
A hypothetical short labelled wagon-cycle is replaced by one of
globally minimal length. Pairwise wagon-carrier linearity rules out
length two. The checked chord-shortening theorem forces every wagon
contact to lie in an adjacent cyclic pair. Physical short/long
expansion then gives an acceptable edge-only BigCycle with the same
numerical order in the ORIGINAL system, contradicting FullSystemGirthGT.

No original designated copy is added or inferred from a temporary
wagon label. The all-ambient-edge family is retained. No appendix.
-/

namespace StructuralRamsey.Girth.OrderOneData

universe v
variable {V E I P : Type v} (D : OrderOneData V E I P)

/-- Full-system girth greater than q implies girth greater than q
of the FULL LABELLED wagon-carrier cut (including all wagon labels).
This proves the corresponding circulation manuscript corollary.
The original system is arbitrary; no finite-size or covering
hypothesis is needed. -/
theorem fullSystemGirth_implies_labelledWagonCutGirth
    (q : ℕ) (hFull : D.FullSystemGirthGT q) :
    LabelledGirthGT
      (fun p : P => {x : V | D.WagonVertex p x}) q := by
  by_contra hFail
  obtain ⟨C, hn, hBudget, hMin⟩ :=
    LabelledGirthGT.exists_minimal_three_of_failure
      (fun p : P => {x : V | D.WagonVertex p x})
      q hFull.1.2 hFail
  have hChordless :=
    C.contact_window_of_global_minimal
      (fun p : P => {x : V | D.WagonVertex p x})
      hMin hFull.1.2 hn
  exact D.false_of_chordless_wagon_cycle
    q hFull C hn hBudget hChordless

end StructuralRamsey.Girth.OrderOneData
