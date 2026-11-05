import Girth.TrainColouredOwnerSelectedStrong

set_option Elab.async false

/-!
# Exact selected split-edge sets and physical colour transfer

The owner-incidence construction retains every old physical edge with
a distinct split physical carrier. Its complete new edge type is exactly
the range of the splitEdge map, not an arbitrary selection of labelled
occurrences.

For a selected source copy, old strongness and two vertices on every old
edge imply that the split physical edges wholly contained in its lifted
vertex range are PRECISELY the split images of its selected old physical
edges. The proof uses the already checked selected_strong_of_old and
literal lift_source_edge identity; no output inducedness premise.

Consequently a colouring of all actual split physical edges pulls back
to a colouring of all old physical edges. Any old Ramsey selection on a
specified family of physical source edges is monochromatic after lift.
This is the EDGE-COLOUR calculation, not a proof that lifted vertices
form an induced ordered relational copy. That final selected-arrow
transport and prescribed A1 application remain separate.
-/

namespace StructuralRamsey.Girth

universe v w

namespace ColouredEdgeOwnerSplit

variable {V I : Type v} (H : ColouredEdgeOwnerSplit V I)

/-- Every new split physical edge is a split image of a genuine old
physical edge; no occurrence is discarded or counted twice. -/
def splitPhysicalEdges : Set (Set H.Vertex) := Set.range H.splitEdge
abbrev SplitPhysicalEdge := {e : Set H.Vertex // e ∈ H.splitPhysicalEdges}

def physicalSplitEdge (f : H.OldEdge) : H.SplitPhysicalEdge :=
  ⟨H.splitEdge f, ⟨f, rfl⟩⟩

@[simp] theorem physicalSplitEdge_carrier (f : H.OldEdge) :
    (H.physicalSplitEdge f).1 = H.splitEdge f := rfl

theorem physicalSplitEdge_injective : Function.Injective H.physicalSplitEdge := by
  intro f g h
  exact H.splitEdge_injective (congrArg Subtype.val h)

theorem physicalSplitEdge_surjective : Function.Surjective H.physicalSplitEdge := by
  intro e
  obtain ⟨f, hf⟩ := e.2
  refine ⟨f, ?_⟩
  apply Subtype.ext
  exact hf

noncomputable def physicalSplitEdgeEquiv : H.OldEdge ≃ H.SplitPhysicalEdge :=
  Equiv.ofBijective H.physicalSplitEdge
    ⟨H.physicalSplitEdge_injective, H.physicalSplitEdge_surjective⟩

/-- The colour-word transfer along the actual physical edge equivalence.
The old selected family may depend on the colouring; no preselected
copy, old colour or output Ramsey arrow is assumed. -/
theorem selectedColourTransfer
    {W Choice : Type v} {κ : Type w}
    (selected : Choice → ColouredOwnerSelectedCopy (W := W) H)
    (hOldArrow : ∀ χ : H.OldEdge → κ,
      ∃ c : Choice, ∀ a b : (selected c).SourceEdge,
        χ ((selected c).physicalEdge a) =
          χ ((selected c).physicalEdge b))
    (χ : H.SplitPhysicalEdge → κ) :
    ∃ c : Choice, ∀ a b : (selected c).SourceEdge,
      χ (H.physicalSplitEdge ((selected c).physicalEdge a)) =
        χ (H.physicalSplitEdge ((selected c).physicalEdge b)) := by
  obtain ⟨c, hc⟩ := hOldArrow (fun f => χ (H.physicalSplitEdge f))
  exact ⟨c, hc⟩

end ColouredEdgeOwnerSplit

namespace ColouredOwnerSelectedCopy

variable {V I W : Type v} {H : ColouredEdgeOwnerSplit V I}
variable (S : ColouredOwnerSelectedCopy (W := W) H)

/-- The physical new edge under its old owner has exactly the carrier
of the ACTUAL lifted source edge. -/
theorem physicalSplitEdge_source_carrier (a : S.SourceEdge) :
    (H.physicalSplitEdge (S.physicalEdge a)).1 =
      S.lift '' a.1 :=
  (S.lift_source_edge a).symm

/-- No additional split physical edge can lie wholly inside a selected
lifted copy: an old edge with two distinct original endpoints has two
distinct split endpoints, so old strongness forces its selection. -/
theorem splitEdge_subset_lift_iff_selected
    (hPair : ∀ f : H.OldEdge,
      ∃ x y : V, x ≠ y ∧ x ∈ f.1 ∧ y ∈ f.1)
    (hOldStrong : ∀ (f : H.OldEdge) (x y : V),
      x ≠ y → x ∈ f.1 → y ∈ f.1 →
      x ∈ Set.range S.embedding → y ∈ Set.range S.embedding →
      ∃ a : S.SourceEdge, S.physicalEdge a = f)
    (f : H.OldEdge) :
    H.splitEdge f ⊆ Set.range S.lift ↔
      f ∈ Set.range S.physicalEdge := by
  constructor
  · intro hInside
    obtain ⟨x, y, hxy, hx, hy⟩ := hPair f
    have hz : H.place f x ∈ H.splitEdge f := ⟨x, hx, rfl⟩
    have hw : H.place f y ∈ H.splitEdge f := ⟨y, hy, rfl⟩
    have hDistinct : H.place f x ≠ H.place f y := by
      intro h
      exact hxy (H.place_injective f h)
    obtain ⟨a, ha⟩ := S.selected_strong_of_old hOldStrong f
      (H.place f x) (H.place f y) hDistinct
      hz hw (hInside hz) (hInside hw)
    exact ⟨a, ha⟩
  · rintro ⟨a, rfl⟩
    exact S.split_selected_edge_subset_copy a

/-- Exact equality of actual selected split-edge sets, using only OLD
strongness, the nontrivial old physical-edge hypothesis, and the
existing literal source-edge lift. No ambient edges are pruned. -/
theorem selectedSplitPhysicalEdges_exact
    (hPair : ∀ f : H.OldEdge,
      ∃ x y : V, x ≠ y ∧ x ∈ f.1 ∧ y ∈ f.1)
    (hOldStrong : ∀ (f : H.OldEdge) (x y : V),
      x ≠ y → x ∈ f.1 → y ∈ f.1 →
      x ∈ Set.range S.embedding → y ∈ Set.range S.embedding →
      ∃ a : S.SourceEdge, S.physicalEdge a = f) :
    Set.range (fun a : S.SourceEdge =>
      H.physicalSplitEdge (S.physicalEdge a)) =
        {e : H.SplitPhysicalEdge | e.1 ⊆ Set.range S.lift} := by
  ext e
  obtain ⟨f, rfl⟩ := H.physicalSplitEdge_surjective e
  constructor
  · rintro ⟨a, ha⟩
    have hSelected : S.physicalEdge a = f :=
      H.physicalSplitEdge_injective ha
    exact (S.splitEdge_subset_lift_iff_selected hPair hOldStrong f).mpr
      ⟨a, hSelected⟩
  · intro hInside
    obtain ⟨a, ha⟩ :=
      (S.splitEdge_subset_lift_iff_selected hPair hOldStrong f).mp hInside
    exact ⟨a, congrArg H.physicalSplitEdge ha⟩

end ColouredOwnerSelectedCopy
end StructuralRamsey.Girth
