import Girth.TrainSystemCutCycleRotation

/-!
# Transport a chordless contact window through cyclic reindexing

If a rotated labelled Berge cycle admits the manuscript's exact A3
window for a fixed real wagon p, then so does the original cycle.
The witness pair of positions is transported by the cyclic index
equivalence. Both connectors, all wagon labels, and the chosen
physical carrier remain unchanged.

This is a proof-state transport theorem, not a girth or chordless
assumption and not the final shortest-cycle argument.
-/

namespace StructuralRamsey.Girth

universe v
variable {V I : Type v}

/-- Recover the original labelled cycle's A3 window from one rotated
window, including exact successor identities at the cyclic wrap. -/
theorem LabelledBergeCycle.contact_window_of_rotate
    {carrier : I → Set V} (C : LabelledBergeCycle carrier)
    (s : Fin C.length) (p : I)
    (h :
      ∃ i : Fin (C.rotate s).length,
        ∀ j : Fin (C.rotate s).length,
          (C.rotate s).vertex j ∈ carrier p →
            j = i ∨ j = cyclicSucc i) :
    ∃ i : Fin C.length, ∀ j : Fin C.length,
        C.vertex j ∈ carrier p → j = i ∨ j = cyclicSucc i := by
  obtain ⟨i, hi⟩ := h
  let iC : Fin C.length := (finCycle s) i
  refine ⟨iC, ?_⟩
  intro j hj
  let jR : Fin C.length := (finCycle s).symm j
  have hMap : (finCycle s) jR = j :=
    Equiv.apply_symm_apply (finCycle s) j
  have hjR : (C.rotate s).vertex jR ∈ carrier p := by
    change C.vertex ((finCycle s) jR) ∈ carrier p
    rw [hMap]
    exact hj
  rcases hi jR hjR with heq | heq
  · left
    change j = (finCycle s) i
    calc
      j = (finCycle s) jR := hMap.symm
      _ = (finCycle s) i := congrArg (finCycle s) heq
  · right
    change j = cyclicSucc ((finCycle s) i)
    calc
      j = (finCycle s) jR := hMap.symm
      _ = (finCycle s) (cyclicSucc i) :=
        congrArg (finCycle s) heq
      _ = cyclicSucc ((finCycle s) i) :=
        RawCyclicIncidenceData.finCycle_cyclicSucc s i

end StructuralRamsey.Girth
