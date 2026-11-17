import Girth.TrainFillingFineRelationalCore

set_option autoImplicit false

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure
open StructuralRamsey.Partite (System)

universe u v
variable {K : RelLanguage.{u}} {A X Y I : Type v} [LinearOrder A]

/-- Restore sparse fine comparisons on the marked copies. For two
different copies, the marked overlap condition either rules out the
two endpoints or puts them in one common physical edge. The genuine
original edge comparison then reflects into the other copy. -/
theorem markedOrder_agrees_of_pairwise_physical_overlap
    (A₀ : RelStructure K A) (Target : System K.withOrder A X)
    (edges : Set (Set Y)) (part : Y → A) (lift : I → X ↪ Y)
    (hPart : ∀ i x, part (lift i x) = Target.part x)
    (hForward : PartiteOrderCompatible Target)
    (hFine : ∀ (a : Embedding A₀.ordered Target.toRelStructure) u,
      Target.part (a u) = u)
    (hStrong : ∀ i e, e ∈ edges → ∀ x y : X, x ≠ y → lift i x ∈ e → lift i y ∈ e →
      ∃ a : Embedding A₀.ordered Target.toRelStructure, e = lift i '' copyCarrier a)
    (hOverlap : ∀ i j, i ≠ j →
      (Set.range (lift i) ∩ Set.range (lift j)).Subsingleton ∨
        ∃ e ∈ edges, Set.range (lift i) ∩ Set.range (lift j) = e)
    (i j : I) (z w : Fin 2 → X) (hEq : lift i ∘ z = lift j ∘ w)
    (hw : Target.rel (.inr ()) w) : Target.rel (.inr ()) z := by
  classical
  by_cases hSame : i = j
  · subst j
    have hz : z = w := funext (fun k => (lift i).injective (congrFun hEq k))
    exact hz.symm ▸ hw
  have hPoint (k : Fin 2) : lift i (z k) = lift j (w k) := congrFun hEq k
  have hOrder : Target.part (z 0) < Target.part (z 1) := by
    rw [← hPart i (z 0), ← hPart i (z 1), hPoint 0, hPoint 1,
      hPart j (w 0), hPart j (w 1)]
    exact hForward w hw
  have hNe : z 0 ≠ z 1 := fun h => (ne_of_lt hOrder) (congrArg Target.part h)
  have hIn (k : Fin 2) : lift i (z k) ∈ Set.range (lift i) ∩ Set.range (lift j) :=
    ⟨⟨z k, rfl⟩, ⟨w k, (congrFun hEq k).symm⟩⟩
  rcases hOverlap i j hSame with hOne | ⟨e, he, hEdge⟩
  · exact (hNe ((lift i).injective (hOne (hIn 0) (hIn 1)))).elim
  · obtain ⟨a, ha⟩ := hStrong i e he (z 0) (z 1) hNe
      (hEdge ▸ hIn 0) (hEdge ▸ hIn 1)
    have hInSource (k : Fin 2) : z k ∈ copyCarrier a := by
      have hk : lift i (z k) ∈ lift i '' copyCarrier a := (hEdge.trans ha) ▸ hIn k
      obtain ⟨x, hx, heq⟩ := hk
      exact ((lift i).injective heq) ▸ hx
    choose u hu using hInSource
    have huOrder : u 0 < u 1 := by
      rw [← hFine a (u 0), ← hFine a (u 1), hu 0, hu 1]
      exact hOrder
    exact (funext hu : a ∘ u = z) ▸ ((a.map_rel_iff (.inr ()) u).mpr huOrder)

end StructuralRamsey.Girth
