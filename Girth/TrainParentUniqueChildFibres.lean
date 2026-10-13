import Girth.TrainParameterRestriction

/-!
# Wagon parent parameters as unique incident child fibres

The manuscript's allowed-part parameter says that two distinct
child wagons of one parent may intersect only in allowed vertices.
Equivalently, for any vertex x outside the allowed set, at most ONE
child of any fixed parent may contain x.

This fibre-uniqueness form turns the output parameter proof into
a local ownership statement rather than a global pairwise
intersection calculation: it suffices to embed each forbidden
vertex/parent child-incidence fibre into a corresponding fibre of
an old standard picture or the witness core, which already has
at most one element.

The crucial missing geometric step is supplying those
fibre embeddings for cross-standard core vertices from actual
order-one witness bridges. We do NOT claim that step here.
-/

namespace StructuralRamsey.Girth

universe v
variable {W I J K O : Type v}

/-- All child wagon labels containing vertex x and belonging to
the SAME fixed parent p. -/
def WagonChildAtVertex
    (carrier : I → Set W) (parent : I → J)
    (x : W) (p : J) : Type v :=
  {i : I // parent i = p ∧ x ∈ carrier i}

/-- The allowed-part sibling intersection condition is exactly
UNIQUE CHILD OWNERSHIP at forbidden vertices. -/
theorem trainParentIntersectionBound_iff_uniqueChildFibres
    (carrier : I → Set W) (parent : I → J)
    (allowed : Set W) :
    TrainParentIntersectionBound carrier parent allowed ↔
      ∀ x : W, x ∉ allowed → ∀ p : J,
        Subsingleton (WagonChildAtVertex carrier parent x p) := by
  constructor
  · intro h x hx p
    constructor
    intro a b
    apply Subtype.ext
    by_contra hab
    have hParent : parent a.1 = parent b.1 :=
      a.2.1.trans b.2.1.symm
    have hxAllowed : x ∈ allowed :=
      h hab hParent ⟨a.2.2, b.2.2⟩
    exact hx hxAllowed
  · intro h a b hab hParent x hx
    by_contra hxForbidden
    let qa : WagonChildAtVertex carrier parent x (parent a) :=
      ⟨a, rfl, hx.1⟩
    let qb : WagonChildAtVertex carrier parent x (parent a) :=
      ⟨b, hParent.symm, hx.2⟩
    have heq : qa = qb := (h x hxForbidden (parent a)).allEq qa qb
    exact hab (congrArg Subtype.val heq)

/-- It is sufficient to embed each forbidden-vertex child
fibre of the NEW train into one old/core child fibre. This
is the exact LOCAL OWNER criterion needed from the geometric
picture-step witness bridge, not an extra Ramsey assumption. -/
theorem trainParentIntersectionBound_of_fibreEmbeddings
    (oldCarrier : O → Set W) (oldParent : O → K)
    (newCarrier : I → Set W) (newParent : I → J)
    (allowed : Set W)
    (hOld : TrainParentIntersectionBound oldCarrier oldParent allowed)
    (hOwner : ∀ x : W, x ∉ allowed → ∀ p : J,
      ∃ q : K,
        (WagonChildAtVertex newCarrier newParent x p) ↪
          (WagonChildAtVertex oldCarrier oldParent x q)) :
    TrainParentIntersectionBound newCarrier newParent allowed := by
  apply (trainParentIntersectionBound_iff_uniqueChildFibres
    newCarrier newParent allowed).mpr
  intro x hx p
  obtain ⟨q, e⟩ := hOwner x hx p
  have hSingle :
      Subsingleton (WagonChildAtVertex oldCarrier oldParent x q) :=
    (trainParentIntersectionBound_iff_uniqueChildFibres
      oldCarrier oldParent allowed).mp hOld x hx q
  constructor
  intro a b
  exact e.injective (Subsingleton.elim (e a) (e b))

end StructuralRamsey.Girth
