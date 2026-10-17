import Girth.TrainCheckedCycleWord
import Mathlib.Tactic

/-!
# Circulation: a literal three-occurrence big-cycle constructor

A length-two strict supreme plan can have one retained designated
occurrence and one genuine long piece. Its literal output then has
three entries. Rather than reasoning with a second cyclic indexing
scheme, the following general constructor checks a three-entry
word directly and produces the manuscript's real BigCycle.

Only six pairwise inequalities and six label-connector incidences
are needed. There is no output acceptability premise and no appendix
input. The length-two strict-plan application is a separate step.
-/

namespace StructuralRamsey.Girth.OrderOneData

universe v
variable {V E I P : Type v} (D : OrderOneData V E I P)

/-- Form a genuine ordered three-occurrence big cycle from the
three labels, three distinct connectors and both incidences at each
connector, including the last-to-first boundary. -/
theorem threeWordBigCycle
    (a b c : I ⊕ E) (u v w : V ⊕ P)
    (hab : a ≠ b) (hbc : b ≠ c) (hca : c ≠ a)
    (huv : u ≠ v) (hvw : v ≠ w) (hwu : w ≠ u)
    (hau : D.Incident a u) (hbv : D.Incident b v)
    (hcw : D.Incident c w)
    (hbu : D.Incident b u) (hcv : D.Incident c v)
    (haw : D.Incident a w) :
    ∃ B : D.BigCycle 3,
      List.ofFn (fun i : Fin 3 => (B.label i, B.connector i)) =
        [(a, u), (b, v), (c, w)] := by
  let word : List ((I ⊕ E) × (V ⊕ P)) :=
    [(a, u), (b, v), (c, w)]
  have hCheck : D.CyclicWordChecks word := by
    refine ⟨by decide, ?_, ?_, ?_, ?_⟩
    · intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all [word]
    · intro i
      fin_cases i
      · simpa [word, cyclicSucc] using hab
      · simpa [word, cyclicSucc] using hbc
      · simpa [word, cyclicSucc] using hca
    · intro i
      fin_cases i
      · simpa [word] using hau
      · simpa [word] using hbv
      · simpa [word] using hcw
    · intro i
      fin_cases i
      · simpa [word, cyclicSucc] using hbu
      · simpa [word, cyclicSucc] using hcv
      · simpa [word, cyclicSucc] using haw
  refine ⟨BigCycle.ofCheckedWord D word hCheck, ?_⟩
  simpa [word] using BigCycle.ofCheckedWord_word D word hCheck

end StructuralRamsey.Girth.OrderOneData
