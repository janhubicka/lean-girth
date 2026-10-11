import Girth.Berge

/-!
# Train parent-parameter intersection conditions survive support pruning

At each train level, distinct child wagons of the SAME parent may
intersect only in parts allowed by that level's parameter. The
allowed vertices can be represented as a Set W; later specialization
is to {x | part x ∈ Aμ}. If each surviving child wagon has an
injectively determined old child label, lies inside that old child,
and its parent is mapped to the old parent, the intersection
condition is automatically inherited.

This isolates the parent-map side of the noncircular covered-edge
normalization; it does not assume that the whole old wagon cut is
linear, and does not merge distinct wagon labels.
-/

namespace StructuralRamsey.Girth

universe v
variable {W I J I' J' : Type v}

/-- At one train level, distinct children of a common parent
intersect only at vertices of the permitted predicate union. -/
def TrainParentIntersectionBound
    (carrier : I → Set W) (parent : I → J)
    (allowed : Set W) : Prop :=
  ∀ ⦃i j : I⦄, i ≠ j → parent i = parent j →
    carrier i ∩ carrier j ⊆ allowed

/-- Injectively restricting surviving child wagons and shrinking
their carriers preserves the old parent-parameter intersection
condition, provided the new and old parent maps commute. -/
theorem trainParentIntersectionBound_restrict
    (oldCarrier : I → Set W) (oldParent : I → J)
    (newCarrier : I' → Set W) (newParent : I' → J')
    (allowed : Set W)
    (hOld : TrainParentIntersectionBound oldCarrier oldParent allowed)
    (child : I' ↪ I)
    (parent : J' → J)
    (hCommute : ∀ a : I',
      oldParent (child a) = parent (newParent a))
    (hShrink : ∀ a : I', newCarrier a ⊆ oldCarrier (child a)) :
    TrainParentIntersectionBound newCarrier newParent allowed := by
  intro a b hab hParent x hx
  have hChild : child a ≠ child b := by
    intro heq
    exact hab (child.injective heq)
  have hOldParent : oldParent (child a) = oldParent (child b) := by
    calc
      oldParent (child a) = parent (newParent a) := hCommute a
      _ = parent (newParent b) := congrArg parent hParent
      _ = oldParent (child b) := (hCommute b).symm
  exact hOld hChild hOldParent ⟨hShrink a hx.1, hShrink b hx.2⟩

/-- If allowedness comes from the union of prescribed vertex
predicates, the parameter itself need not be changed when edges
or wagons are removed. -/
theorem trainParentPartBound_restrict
    {P : Type v}
    (part : W → P) (allowedParts : Set P)
    (oldCarrier : I → Set W) (oldParent : I → J)
    (newCarrier : I' → Set W) (newParent : I' → J')
    (hOld :
      TrainParentIntersectionBound oldCarrier oldParent
        {x | part x ∈ allowedParts})
    (child : I' ↪ I) (parent : J' → J)
    (hCommute : ∀ a, oldParent (child a) = parent (newParent a))
    (hShrink : ∀ a, newCarrier a ⊆ oldCarrier (child a)) :
    TrainParentIntersectionBound newCarrier newParent
      {x | part x ∈ allowedParts} :=
  trainParentIntersectionBound_restrict
    oldCarrier oldParent newCarrier newParent
    {x | part x ∈ allowedParts} hOld
    child parent hCommute hShrink

end StructuralRamsey.Girth
