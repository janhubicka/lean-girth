import Girth.ForestMarkedSupportTransport
import Girth.ForestObservableProfile

/-!
# Forest status factors through the finite observable B-copy profile

A q-tuple of B-copy vertex positions has a finite Boolean
vertex-equality/role profile, already formalized in ForestObservableProfile.
If the intrinsic labelled carriers and A-edge supports are fixed, equality
of that profile implies equality of the complete ForestOfCopies status.

This is the exact finite-colouring interface needed by the proposed
successor-tree proof. It does not show that every geometric q-tuple
admits a bounded free-history presentation, or that the colouring is
equivariant under arbitrary successor shape maps.
-/

namespace StructuralRamsey.Girth

/-- In the ordinary type-zero finite structural setting, the existing
observable profile determines full foresthood, including both allowed
pairwise A-edge/singleton intersections and arbitrary running-intersection
join trees. Every selected B-copy is represented by the same labelled
carrier positions and intrinsic support-edge pattern in both hosts. -/
theorem forestObservableProfile_determines_forest
    (q : ℕ)
    {VB Role W Z : Type}
    [DecidableEq W] [DecidableEq Z]
    (f : MarkedCopyVertex q VB → W)
    (g : MarkedCopyVertex q VB → Z)
    (role : MarkedCopyVertex q VB → Role)
    (hProfile :
      forestObservableProfile q f role =
        forestObservableProfile q g role)
    (F : Fin q → HypergraphPiece W)
    (G : Fin q → HypergraphPiece Z)
    (carriers : Fin q → Set (MarkedCopyVertex q VB))
    (atoms : Fin q → Set (Set (MarkedCopyVertex q VB)))
    (hPresent :
      SameMarkedSupportPresentation F G f g carriers atoms) :
    ForestOfCopies F ↔ ForestOfCopies G := by
  have hKernel : SameMarkedKernel f g :=
    sameMarkedKernel_of_observableProfile_eq q f g role hProfile
  exact markedFamily_forest_iff_of_supportPresentation
    F G f g hKernel carriers atoms hPresent

end StructuralRamsey.Girth
