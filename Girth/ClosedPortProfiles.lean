import Girth.PortSideP4Geometry

/-!
# Finite closed-port profiles for ARBITRARY finite coloured graphs

The three P4 crossing patterns are a special case of a general
shape calculus: every induced or homomorphic graph occurrence in a
free graph amalgam over a midpoint-closed interface determines a
vertex-location map into three sorts (left-private, shared, right-
private). Adjacent graph vertices cannot be on opposite private
sides, and a two-edge path joining two distinct shared vertices
cannot have a private midpoint.

These elementary constraints define a finite profile alphabet for
EVERY finite coloured A. The number of possible profiles is at most
3^|A|, but the number of occurrences realizing a given profile
need not be bounded. The profile theorem does NOT by itself produce
a Ramsey expansion, synchronized replay, or a Ramsey arrow.
-/

namespace StructuralRamsey.Girth
namespace CoherentPort

universe v
variable {U W : Type v}

/-- The location profile of an occurrence is admissible if it respects
both free-attachment adjacency and midpoint-closure constraints. -/
def ClosedPortProfile
    (A : SimpleGraph U) (profile : U → PortSide) : Prop :=
  (∀ ⦃a b : U⦄, A.Adj a b →
    SideStepAllowed (profile a) (profile b)) ∧
  (∀ ⦃a b c : U⦄, a ≠ c →
    A.Adj a b → A.Adj b c →
      NoHiddenPrivateMidpoint (profile a) (profile b) (profile c))

/-- Any injective graph homomorphism into a free union over a
midpoint-closed interface has an admissible three-sort profile.
No inducedness or graph girth assumption is needed for this purely
geometric constraint. -/
theorem closedPortProfile_of_embedding
    {A : SimpleGraph U}
    {adj : W → W → Prop} {L R : Set W}
    (hCover : L ∪ R = Set.univ)
    (hNoCross : ∀ ⦃x y⦄, x ∈ L \ R → y ∈ R \ L → ¬ adj x y)
    (hSymm : ∀ ⦃x y⦄, adj x y → adj y x)
    (hPortClosed : MidpointClosed (adj := adj) (L ∩ R))
    (f : U ↪ W)
    (hAdj : ∀ ⦃a b : U⦄, A.Adj a b → adj (f a) (f b)) :
    ClosedPortProfile A (fun a => sideLocation L R (f a)) := by
  constructor
  · intro a b hab
    exact sideLocation_step_of_free_adj
      hCover hNoCross hSymm (hAdj hab)
  · intro a b c hac hab hbc
    have hfa : f a ≠ f c := by
      intro h
      exact hac (f.injective h)
    exact sideLocation_no_hidden_midpoint hSymm hPortClosed hfa
      (hAdj hab) (hAdj hbc)

/-- The space of potential closed-port shapes for a fixed finite
coloured graph is finite, regardless of host size or girth. The
actual geometric occurrence sets in those shapes can be arbitrarily
large and need separate Ramsey homogenization. -/
theorem finite_closedPortProfiles
    [Finite U] (A : SimpleGraph U) :
    Finite {p : U → PortSide // ClosedPortProfile A p} := by
  infer_instance

end CoherentPort
end StructuralRamsey.Girth
