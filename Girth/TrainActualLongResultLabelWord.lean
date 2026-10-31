import Girth.TrainOneDoubleWordSplit
import Girth.TrainOneFreshLongComplete

/-!
# The actual one-long BigCycle replacement has exact doubled label word

The physically constructed resultWord of BigCycle.onlyLongPieces
keeps all source labels except one selected source position. At that
position its label PROJECTION is exactly two physical-edge labels.

This connects the already-checked arbitrary physical replacement
syntax to the pure Fin-indexed common-prefix/suffix splitting lemma.
No output BigCycle, acceptability, geometry, or chosen supreme label
is assumed here. Those are used in the next actual designated-rank
integration. Circulation only, no appendix.
-/

namespace StructuralRamsey.Girth.OrderOneData

universe v
variable {V E I P : Type v} (D : OrderOneData V E I P)

/-- The list of labels of the one-long physical replacement result
is literally the source list with just one doubled edge block. -/
theorem BigCycle.onlyLong_resultWord_label_projection
    {n : ℕ} (K : D.BigCycle n)
    (j : Fin n) (first : E) (wagon : P) (second : E) :
    (K.resultWord D (K.onlyLongPieces D j first wagon second)).map Prod.fst =
      oneDoubleWord K.label j (Sum.inr first) (Sum.inr second) := by
  simp only [BigCycle.resultWord, oneDoubleWord,
    List.map_flatten, List.map_ofFn]
  have hBlocks :
      (fun k : Fin n =>
        (K.pieceWord D k
          (K.onlyLongPieces D j first wagon second k)).map Prod.fst) =
      (fun k : Fin n =>
        if k = j then [Sum.inr first, Sum.inr second]
        else [K.label k]) := by
    funext k
    by_cases hk : k = j
    · subst k
      simp [BigCycle.pieceWord, BigCycle.onlyLongPieces]
    · simp [BigCycle.pieceWord, BigCycle.onlyLongPieces, hk]
  exact congrArg List.flatten (congrArg List.ofFn hBlocks)

end StructuralRamsey.Girth.OrderOneData
