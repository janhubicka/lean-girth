import Girth.IncidenceCompression
import Girth.LabelledWagonCutRestriction
import Mathlib.Tactic

/-!
# Rotation of labelled Berge cycles

The minimum-cycle chord-shortening proof must move an arbitrary
pair of connector positions to the beginning of the cyclic word.
This is an EXACT reindexing of both physical vertex connectors
and tagged wagon labels; their injectivity, incidence, and length
are preserved without quotienting equal carriers.

This module deliberately proves only the cyclic reindexing, not a
girth bound or the combinatorial shortcut.
-/

namespace StructuralRamsey.Girth

universe v
variable {V I : Type v}

/-- Rotate a labelled Berge cycle by a genuine cyclic equivalence. -/
def LabelledBergeCycle.rotate
    {carrier : I → Set V} (C : LabelledBergeCycle carrier)
    (s : Fin C.length) : LabelledBergeCycle carrier where
  length := C.length
  hlength := C.hlength
  label i := C.label ((finCycle s) i)
  vertex i := C.vertex ((finCycle s) i)
  label_injective := by
    intro i j h
    exact (finCycle s).injective (C.label_injective h)
  vertex_injective := by
    intro i j h
    exact (finCycle s).injective (C.vertex_injective h)
  left_mem := fun i => C.left_mem ((finCycle s) i)
  right_mem := by
    intro i
    change C.vertex ((finCycle s) i) ∈
      carrier (C.label ((finCycle s) (cyclicSucc i)))
    rw [RawCyclicIncidenceData.finCycle_cyclicSucc]
    exact C.right_mem ((finCycle s) i)

/-- Rotation preserves the exact count of distinct labelled wagons. -/
@[simp] theorem LabelledBergeCycle.rotate_length
    {carrier : I → Set V} (C : LabelledBergeCycle carrier)
    (s : Fin C.length) : (C.rotate s).length = C.length := rfl

/-- Rotation sends the chosen source connector to index zero. -/
theorem LabelledBergeCycle.rotate_vertex_zero
    {carrier : I → Set V} (C : LabelledBergeCycle carrier)
    (s : Fin C.length) :
    (C.rotate s).vertex
        (⟨0, by have h := C.hlength; omega⟩ : Fin C.length) =
      C.vertex s := by
  change C.vertex ((finCycle s) (⟨0, by have h := C.hlength; omega⟩ : Fin C.length)) =
    C.vertex s
  congr 1
  rw [finCycle_apply]
  apply Fin.ext
  rw [Fin.val_add]
  simpa using (Nat.mod_eq_of_lt s.isLt)

/-- The same rotation sends the chosen original wagon label to zero. -/
theorem LabelledBergeCycle.rotate_label_zero
    {carrier : I → Set V} (C : LabelledBergeCycle carrier)
    (s : Fin C.length) :
    (C.rotate s).label
        (⟨0, by have h := C.hlength; omega⟩ : Fin C.length) =
      C.label s := by
  change C.label ((finCycle s) (⟨0, by have h := C.hlength; omega⟩ : Fin C.length)) =
    C.label s
  congr 1
  rw [finCycle_apply]
  apply Fin.ext
  rw [Fin.val_add]
  simpa using (Nat.mod_eq_of_lt s.isLt)

/-- A globally minimal labelled cycle remains globally minimal
under rotation, since its length is literally unchanged. -/
theorem LabelledBergeCycle.rotate_minimal
    {carrier : I → Set V} (C : LabelledBergeCycle carrier)
    (hMin : ∀ B : LabelledBergeCycle carrier, C.length ≤ B.length)
    (s : Fin C.length) :
    ∀ B : LabelledBergeCycle carrier, (C.rotate s).length ≤ B.length :=
  hMin

end StructuralRamsey.Girth
