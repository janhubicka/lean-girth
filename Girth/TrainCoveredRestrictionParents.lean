import Girth.Berge

/-!
# Restricting a train's wagon hierarchy to covered edges

A train is a hierarchy of equivalence classes of ACTUAL edges.  For any
restriction to a subset of edges, its surviving wagon labels are the old
labels having a retained edge.  Parent maps are induced by the original
parent maps, all surviving carriers shrink, and the sibling-intersection
parameters are inherited.  Different labelled wagons are not identified
even if their surviving physical carriers become equal.

These elementary, noncircular facts address part of the manuscript's
covered-edge normalization.  They DO NOT assert preservation of the
stronger acceptable-cycle system-Girth property: its acceptability
conditions can depend on ambient edges deleted by the restriction.
-/

namespace StructuralRamsey.Girth

universe u v w
variable {E : Type u} {I J : Type v} {V : Type w}

/-- Labels that still have a member after restricting actual edges to S. -/
def UsedTrainLabels (cut : E → I) (S : Set E) : Type v :=
  {i : I // ∃ e : E, e ∈ S ∧ cut e = i}

/-- The induced parent map on nonempty restricted wagon classes. -/
def restrictedTrainParent
    (fine : E → I) (coarse : E → J) (parent : I → J)
    (hParent : ∀ e, coarse e = parent (fine e))
    (S : Set E) :
    UsedTrainLabels fine S → UsedTrainLabels coarse S := by
  intro i
  refine ⟨parent i.1, ?_⟩
  obtain ⟨e, heS, heFine⟩ := i.2
  exact ⟨e, heS, (hParent e).trans (congrArg parent heFine)⟩

/-- The restricted parent square commutes with inclusion of labels. -/
theorem restrictedTrainParent_val
    (fine : E → I) (coarse : E → J) (parent : I → J)
    (hParent : ∀ e, coarse e = parent (fine e))
    (S : Set E) (i : UsedTrainLabels fine S) :
    (restrictedTrainParent fine coarse parent hParent S i).val =
      parent i.val := rfl

/-- Every surviving coarse wagon has a surviving fine child. -/
theorem restrictedTrainParent_surjective
    (fine : E → I) (coarse : E → J) (parent : I → J)
    (hParent : ∀ e, coarse e = parent (fine e))
    (S : Set E) :
    Function.Surjective
      (restrictedTrainParent fine coarse parent hParent S) := by
  intro j
  obtain ⟨e, heS, heCoarse⟩ := j.2
  refine ⟨⟨fine e, ⟨e, heS, rfl⟩⟩, ?_⟩
  apply Subtype.ext
  change parent (fine e) = j.val
  exact (hParent e).symm.trans heCoarse

/-- The vertex carrier of a labelled wagon is the union of its edges. -/
def trainWagonCarrier
    (edgeVertices : E → Set V) (cut : E → I) (i : I) : Set V :=
  {x | ∃ e, cut e = i ∧ x ∈ edgeVertices e}

/-- A surviving wagon carries just the vertices of its retained edges. -/
def restrictedTrainWagonCarrier
    (edgeVertices : E → Set V) (cut : E → I)
    (S : Set E) (i : UsedTrainLabels cut S) : Set V :=
  {x | ∃ e, e ∈ S ∧ cut e = i.val ∧ x ∈ edgeVertices e}

/-- Restriction cannot enlarge a wagon carrier. -/
theorem restrictedTrainWagonCarrier_subset
    (edgeVertices : E → Set V) (cut : E → I)
    (S : Set E) (i : UsedTrainLabels cut S) :
    restrictedTrainWagonCarrier edgeVertices cut S i ⊆
      trainWagonCarrier edgeVertices cut i.val := by
  rintro x ⟨e, _heS, heLabel, hx⟩
  exact ⟨e, heLabel, hx⟩

/-- The allowed-part intersection parameter is inherited under
edge deletion, even if formerly different wagon carriers become equal.
This is formulated using labels, not extensional carrier sets. -/
theorem restrictedTrain_siblingIntersection
    (edgeVertices : E → Set V)
    (fine : E → I) (coarse : E → J) (parent : I → J)
    (hParent : ∀ e, coarse e = parent (fine e))
    (S : Set E) (allowed : Set V)
    (hOld :
      ∀ i j : I, i ≠ j → parent i = parent j →
        trainWagonCarrier edgeVertices fine i ∩
          trainWagonCarrier edgeVertices fine j ⊆ allowed)
    (i j : UsedTrainLabels fine S) (hDifferent : i ≠ j)
    (hSameParent :
      restrictedTrainParent fine coarse parent hParent S i =
        restrictedTrainParent fine coarse parent hParent S j) :
    restrictedTrainWagonCarrier edgeVertices fine S i ∩
      restrictedTrainWagonCarrier edgeVertices fine S j ⊆ allowed := by
  have hDifferentOld : i.val ≠ j.val := by
    intro heq
    exact hDifferent (Subtype.ext heq)
  have hSameOld : parent i.val = parent j.val := by
    have hh := congrArg (fun k : UsedTrainLabels coarse S => k.val) hSameParent
    exact hh
  intro x hx
  apply hOld i.val j.val hDifferentOld hSameOld
  exact ⟨
    restrictedTrainWagonCarrier_subset edgeVertices fine S i hx.1,
    restrictedTrainWagonCarrier_subset edgeVertices fine S j hx.2⟩

end StructuralRamsey.Girth
