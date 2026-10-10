import Girth.Berge

/-!
# Labelled wagon-cut girth under restriction and shrinking carriers

The manuscript's horizontal cuts are LABELLED hypergraph families:
different wagons remain different labels even when their carriers
happen to coincide. Ordinary GirthGT on a SET of vertex sets is
insufficient, since that representation collapses repeated carriers.

For a witness obtained by deleting uncovered support edges, surviving
wagon labels inject into the original labels and every surviving
wagon carrier is a subset of its old carrier. The elementary labelled
Berge-cycle transport below proves that this operation cannot create
new short cycles. It is the exact girth kernel required for covered
witness normalization of recursive train witnesses.
-/

namespace StructuralRamsey.Girth

universe v
variable {W I J : Type v}

/-- A Berge cycle in a family indexed by occurrence labels,
not merely by its set of distinct vertex carriers. -/
structure LabelledBergeCycle (carriers : I → Set W) where
  length : ℕ
  hlength : 2 ≤ length
  label : Fin length → I
  vertex : Fin length → W
  label_injective : Function.Injective label
  vertex_injective : Function.Injective vertex
  left_mem : ∀ i, vertex i ∈ carriers (label i)
  right_mem : ∀ i, vertex i ∈ carriers (label (cyclicSucc i))

/-- Girth bound in a labelled wagon cut. Duplicated carriers still
carry distinct labels and may yield length-two cycles. -/
def LabelledGirthGT (carriers : I → Set W) (g : ℕ) : Prop :=
  ¬ ∃ c : LabelledBergeCycle carriers, c.length ≤ g

/-- Restrict to injected surviving wagon labels and shrink every
surviving carrier. No new labelled Berge cycle can appear. -/
theorem labelledGirthGT_of_injective_shrinking
    (old : I → Set W) (reduced : J → Set W)
    (label : J → I) (hLabel : Function.Injective label)
    (hShrink : ∀ j : J, reduced j ⊆ old (label j))
    (g : ℕ) (hOld : LabelledGirthGT old g) :
    LabelledGirthGT reduced g := by
  rintro ⟨c, hBound⟩
  let lifted : LabelledBergeCycle old := {
    length := c.length
    hlength := c.hlength
    label := fun i => label (c.label i)
    vertex := c.vertex
    label_injective := by
      intro i j hij
      exact c.label_injective (hLabel hij)
    vertex_injective := c.vertex_injective
    left_mem := by
      intro i
      exact hShrink (c.label i) (c.left_mem i)
    right_mem := by
      intro i
      exact hShrink (c.label (cyclicSucc i)) (c.right_mem i)
  }
  exact hOld ⟨lifted, hBound⟩

/-- In particular, shrinking carriers without relabelling cannot
decrease labelled girth. -/
theorem labelledGirthGT_of_carrier_shrinking
    (old reduced : I → Set W)
    (hShrink : ∀ i, reduced i ⊆ old i)
    (g : ℕ) (hOld : LabelledGirthGT old g) :
    LabelledGirthGT reduced g :=
  labelledGirthGT_of_injective_shrinking
    old reduced id Function.injective_id hShrink g hOld

/-- Restricting the set of wagon labels alone cannot decrease
labelled girth; all duplicate carrier labels remain explicit. -/
theorem labelledGirthGT_of_injective_reindex
    (old : I → Set W) (label : J → I)
    (hLabel : Function.Injective label)
    (g : ℕ) (hOld : LabelledGirthGT old g) :
    LabelledGirthGT (fun j : J => old (label j)) g :=
  labelledGirthGT_of_injective_shrinking
    old (fun j : J => old (label j)) label hLabel
    (fun _ => Set.Subset.rfl) g hOld

end StructuralRamsey.Girth
