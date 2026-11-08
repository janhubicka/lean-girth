import Girth.TrainSimultaneousSupreme
import Mathlib.Tactic

set_option autoImplicit false
set_option Elab.async false

/-!
# Path A: two physical order-one bridges give two genuine ShortValid pieces

A two-occurrence witness cycle with one vertex connector x and one
wagon connector w has its two boundary connectors in either cyclic
orientation. For each actual label a, the existing order-one bridge
data supplies its OWN physical edge e_a in wagon w through x.

For each possible designated target, that bridge edge is a literal
ShortValid replacement at the OTHER occurrence. Different targets
are allowed to have different physical edges: no artificial common
edge assumption is needed.

The second theorem states this directly for any cut-index length
known to be exactly two, retaining its original index type.
Neither result assumes the labels are designated; that is a separate
source-level condition when applying the old standard supreme bound.
No physical source expansion, appendix, or manuscript edit.
-/

namespace StructuralRamsey.Girth.OrderOneData

universe v
variable {V E I P : Type v} (D : OrderOneData V E I P)

/-- At a genuine mixed two-occurrence word, the physical bridge
of the chosen target is ShortValid at the other occurrence. -/
theorem BigCycle.two_mixed_bridges_shortValid_at_each_cut
    (Z : D.BigCycle 2) (x : V) (w : P)
    (hMixed :
      (Z.connector 0 = Sum.inl x ∧
       Z.connector 1 = Sum.inr w) ∨
      (Z.connector 0 = Sum.inr w ∧
       Z.connector 1 = Sum.inl x))
    (hBridges : ∀ target : Fin 2, D.Bridge (Z.label target) x w) :
    ∀ cut : Fin 2, ∃ e : E,
      Z.ShortValid D (trainCyclicPred cut) cut e := by
  intro cut
  obtain ⟨e, hOwned, hParent, hVertex⟩ :=
    hBridges (trainCyclicPred cut)
  have hV : D.Incident (.inr e) (.inl x) := by
    simpa [Incident, carrier] using hVertex
  have hW : D.Incident (.inr e) (.inr w) := by
    change D.Meets (.inr e) w
    exact ⟨e, rfl, hParent⟩
  have hEveryInc : ∀ t : Fin 2,
      D.Incident (.inr e) (Z.connector t) := by
    intro t
    fin_cases t
    · change D.Incident (.inr e) (Z.connector (0 : Fin 2))
      rcases hMixed with h | h
      · rw [h.1]
        exact hV
      · rw [h.1]
        exact hW
    · change D.Incident (.inr e) (Z.connector (1 : Fin 2))
      rcases hMixed with h | h
      · rw [h.2]
        exact hW
      · rw [h.2]
        exact hV
  exact ⟨e, hOwned, hEveryInc (trainCyclicPred cut), hEveryInc cut⟩

/-- Same bridge-to-short theorem with an actual arbitrary Fin c
cut-index type for which c=2. This is the literal input to the
two-cut original-source singleton transfer. -/
theorem BigCycle.two_mixed_bridges_shortValid_at_each_cut_of_two
    {c : ℕ} (hc : c = 2)
    (Z : D.BigCycle c) (x : V) (w : P)
    (hMixed :
      (Z.connector ⟨0, by omega⟩ = Sum.inl x ∧
       Z.connector ⟨1, by omega⟩ = Sum.inr w) ∨
      (Z.connector ⟨0, by omega⟩ = Sum.inr w ∧
       Z.connector ⟨1, by omega⟩ = Sum.inl x))
    (hBridges : ∀ target : Fin c,
      D.Bridge (Z.label target) x w) :
    ∀ cut : Fin c, ∃ e : E,
      Z.ShortValid D (trainCyclicPred cut) cut e := by
  subst c
  exact BigCycle.two_mixed_bridges_shortValid_at_each_cut
    D Z x w hMixed hBridges

end StructuralRamsey.Girth.OrderOneData
