import Girth.TrainPhysicalLongSourceDesignated
import Girth.TrainActualCycleDesignatedRank
import Girth.TrainActualLongResultLabelWord

/-!
# Actual physical long insertion strictly reduces designated occurrence count

A genuine PhysicalLongGeometry replacement automatically acts on an
ORIGINALLY designated occurrence (not merely one geometrically owned
by a standard). The checked literal one-long resultWord bookkeeping
replaces that single designated label by TWO physical edge labels and
retains all other source labels in the exact same order.

Combine the actual source-designation theorem, the one-double Fin
word split, the literal label projection and the actual BigCycle
counting lemma. The result is a fully literal, target-INDEPENDENT
decrease of designated occurrence count for every globally legal
one-long inserted BigCycle, even if its length is n+1 and its
receiving standard is not a cyclic neighbour.

This does not construct the output BigCycle, assign new geometric
owners or show that its minimum cuts cannot increase. Those are
separate Path A obligations. Circulation only; no appendix.
-/

namespace StructuralRamsey.Girth.OrderOneData

universe v
variable {V E I P : Type v} (D : OrderOneData V E I P)

/-- A genuine physical-only long insertion with an ACTUAL literal
output BigCycle reduces the number of genuine designated labels by
EXACTLY ONE. Neither the original designated label's identity nor
the reduced supreme target standard is assumed. -/
theorem BigCycle.oneFreshPhysicalLong_designatedCount_drop
    {n m : ℕ} (K : D.BigCycle n) (H : D.BigCycle m)
    (j : Fin n) (first : E) (wagon : P) (second : E)
    (hPhysical : K.PhysicalLongGeometry D j first wagon second)
    (hWord : List.ofFn (fun k : Fin m =>
      (H.label k, H.connector k)) =
      K.resultWord D (K.onlyLongPieces D j first wagon second)) :
    H.designatedOccurrenceCount D + 1 =
      K.designatedOccurrenceCount D := by
  obtain ⟨source, hDesignated⟩ :=
    K.source_designated_of_physicalLongGeometry
      D j first wagon second hPhysical
  obtain ⟨before, after, hOld, hNew⟩ :=
    oneDoubleWord_exists_common_split K.label j
      (Sum.inr first) (Sum.inr second)
  have hOldLabels :
      List.ofFn K.label = before ++ Sum.inl source :: after := by
    simpa only [hDesignated] using hOld
  have hOutWord :
      List.ofFn H.label =
        oneDoubleWord K.label j (Sum.inr first) (Sum.inr second) := by
    calc
      List.ofFn H.label =
          (List.ofFn (fun k : Fin m =>
            (H.label k, H.connector k))).map Prod.fst := by
              simp [List.map_ofFn] <;> (funext k; rfl)
      _ = (K.resultWord D
          (K.onlyLongPieces D j first wagon second)).map Prod.fst :=
            congrArg (List.map Prod.fst) hWord
      _ = oneDoubleWord K.label j
          (Sum.inr first) (Sum.inr second) :=
            K.onlyLong_resultWord_label_projection
              D j first wagon second
  have hNewLabels :
      List.ofFn H.label =
        before ++ Sum.inr first :: Sum.inr second :: after :=
    hOutWord.trans hNew
  exact K.designatedCount_drop_of_long_literal
    D H before after source first second hOldLabels hNewLabels

end StructuralRamsey.Girth.OrderOneData
