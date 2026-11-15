import Girth.TrainFillingPrivateActualWagonOwner
import Girth.LabelledWagonCutRestriction

set_option Elab.async false

/-!
# The ACTUAL first wagon quotient gives coverage and carrier linearity

For the original train T on full A-support edge labels:
  P := Quotient (T.wagonSetoid μ)
  owner(e) := [e]_μ
  F_p := T.wagonClassCarrier oldEdges μ p.
The existing wagon-class carrier API and our
TrainFillingPrivateActualWagonOwner prove that
every F_p vertex lies in an owned original edge.

A labelled wagon-cut Berge TWO-cycle exists exactly
when two distinct wagon labels share two distinct
vertices. The old first-tail wagon-girth >h1>=2
therefore implies the pairwise carrier linearity
used when each first wagon is contracted to one edge.
This is LABELLED girth: equal carrier sets with
different wagon labels are not silently collapsed.

Both source facts are packaged below for the actual
quotient cut. No arbitrary owner map, new cutoff
hypothesis, output M-linear condition or output
system-girth assumption is introduced.

Source candidate pending exact-head Lean elaboration.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v
variable {V I : Type v}

/-- Converse to the existing
labelledGirthGT_two_of_pairwiseSubsingleton:
a pair of different labels with two different common
vertices gives an actual labelled Berge two-cycle. -/
theorem pairwiseSubsingleton_of_labelledGirthGT_two
    (carrier : I → Set V)
    (h : LabelledGirthGT carrier 2) :
    ∀ p q : I, p ≠ q →
      (carrier p ∩ carrier q).Subsingleton := by
  intro p q hpq x hx y hy
  by_contra hxy
  let c : LabelledBergeCycle carrier := {
    length := 2
    hlength := by omega
    label := ![p, q]
    vertex := ![x, y]
    label_injective := by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all
    vertex_injective := by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all
    left_mem := by
      intro i
      fin_cases i
      · exact hx.1
      · exact hy.2
    right_mem := by
      intro i
      fin_cases i
      · simpa [cyclicSucc] using hx.2
      · simpa [cyclicSucc] using hy.1
  }
  exact h ⟨c, by simp [c]⟩

/-- The same statement at ANY actual labelled quotient
of an EdgeTrainLevels, with no cardinality assumption on
individual wagons and no quotient collapse of duplicates. -/
theorem EdgeTrainLevels.wagonClassCarrier_linear_of_labelledGirthGT_two
    {E : Type v} {m : ℕ}
    (T : EdgeTrainLevels E m)
    (edges : E → Set V) (μ : Fin (m + 1))
    (hGirth : LabelledGirthGT
      (T.wagonClassCarrier edges μ) 2) :
    ∀ p q : Quotient (T.wagonSetoid μ),
      p ≠ q →
        (T.wagonClassCarrier edges μ p ∩
          T.wagonClassCarrier edges μ q).Subsingleton :=
  pairwiseSubsingleton_of_labelledGirthGT_two
    (T.wagonClassCarrier edges μ) hGirth

/-- Extract the true local first-wagon source EHN data
from the original A-support edge train and its actual
labelled horizontal-cut girth bound. The first output
is exactly old-carrier linearity and the second output
is pointwise A-edge coverage inside each induced wagon.

Neither output requires a separate first-wagon owner
map or a new hypothesis about the shortened train M. -/
theorem EdgeTrainLevels.actualWagon_EHN_source
    {L : RelLanguage.{u}} {UA : Type v}
    (A : RelStructure L UA) (D : RelStructure L V)
    {m : ℕ}
    (T : EdgeTrainLevels
      {e : Set V // e ∈ supportCopies A D} m)
    (μ : Fin (m + 1))
    (hGirth : LabelledGirthGT
      (T.wagonClassCarrier
        (fun e : {e : Set V // e ∈ supportCopies A D} => e.1) μ) 2) :
    let carrier := T.wagonClassCarrier
      (fun e : {e : Set V // e ∈ supportCopies A D} => e.1) μ
    (∀ p q : Quotient (T.wagonSetoid μ),
      p ≠ q → (carrier p ∩ carrier q).Subsingleton) ∧
    (∀ p (x : {v : V // v ∈ carrier p}),
      ∃ a : Embedding A (D.induce (carrier p)),
        x ∈ copyCarrier a) := by
  constructor
  · exact T.wagonClassCarrier_linear_of_labelledGirthGT_two
      (fun e : {e : Set V // e ∈ supportCopies A D} => e.1)
      μ hGirth
  · exact T.inducedWagon_Acovered A D μ

end StructuralRamsey.Girth
