import Girth.ContactJoinTree
import Girth.ContactLevelZero

/-! The two components of the finite bottom mixed-forest property.
They are shared by the two directions of its relationship with
contact system girth. -/

namespace StructuralRamsey.Girth
universe v
variable {V E I : Type v}

namespace OrderOneData
variable (D : OrderOneData V E I E)

def ZeroPairwise : Prop :=
  ∀ a b : I ⊕ E, a ≠ b →
    (D.carrier a ∩ D.carrier b).Subsingleton ∨
      ∃ e, e ∈ D.edges a ∧ e ∈ D.edges b ∧
        D.carrier a ∩ D.carrier b = D.edgeCarrier e

/-- The actual finite-subfamily join-tree part of mixed forests. -/
def ZeroJoinTreesThrough (q : ℕ) : Prop :=
  ∀ s : Finset (I ⊕ E), s.Nonempty → s.card ≤ q →
    Nonempty (ContactJoinTree (fun a : {a // a ∈ s} => D.carrier a.val))

/-- The mixed-forest property through q (with global allowed
pair intersections, as is equivalent when q is at least two). -/
def ZeroMixedForestsThrough (q : ℕ) : Prop :=
  D.ZeroPairwise ∧ D.ZeroJoinTreesThrough q

end OrderOneData
end StructuralRamsey.Girth
