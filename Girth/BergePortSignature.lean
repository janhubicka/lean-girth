import Girth.BergePath
import Mathlib.Data.Set.Card
import Mathlib.Tactic

/-!
# Finite Berge-path boundary signatures

A free gluing over an original-vertex interface S creates a mixed
Berge cycle exactly when the two local short-path signatures contain
a mixed weighted cycle below the girth threshold, PROVIDED:
  * the two edge-occurrence families are disjoint;
  * the old sides already have the desired Berge girth;
  * all cross-side edge intersections lie inside the shared port.

The full equivalence still needs two proofs: cutting a physical
Berge cycle into S-to-S excursions, and constructing a short
physical cycle from a mixed symbolic one via mod-two incidence chains.
This module defines the finite, intrinsic signature and its exact
mixed-cycle condition. The finite-size and singleton-port facts
below are fully mathematical theorems, not axioms.

Unlike the older ForestOfCopies interface, no assumption is made
that the coloured object is a single support edge.
-/

namespace StructuralRamsey.Girth
namespace BergePortSignature

universe v
variable {W : Type v}

/-- The port's intrinsic short-path alphabet: two ordered boundary
vertices and a Berge length strictly below g. The label of the
side (left/right) is carried by which signature set is used. -/
abbrev PortSymbol (S : Set W) (g : ℕ) : Type v :=
  S × (S × Fin g)

/-- A Berge excursion has all connector vertices strictly between
its endpoints outside the shared interface. Hyperedges may contain
other port vertices, but these are not chosen as connectors. -/
def PrivateExcursion
    {H : Set (Set W)} (S : Set W) (p : BergePath H) : Prop :=
  (∀ i : Fin (p.length + 1),
      i ≠ (0 : Fin (p.length + 1)) →
      i ≠ Fin.last p.length →
      p.vertex i ∉ S)

/-- The set of all actual *types* of private Berge excursions.
The signature deliberately forgets multiplicity and the actual
witness paths, retaining only endpoint types and Berge length. -/
def ShortSignature
    (H : Set (Set W)) (S : Set W) (g : ℕ) :
    Set (PortSymbol S g) :=
  { a |
    a.1 ≠ a.2.1 ∧
    ∃ p : BergePath H,
      p.length = a.2.2.val ∧
      p.vertex 0 = a.1.val ∧
      p.vertex (Fin.last p.length) = a.2.1.val ∧
      PrivateExcursion S p }

/-- For a finite port, there are only finitely many possible
endpoint/length signatures even if the ambient hypergraph
has infinitely many edges. -/
theorem finite_shortSignature
    {S : Set W} [Finite S]
    (H : Set (Set W)) (g : ℕ) :
    (ShortSignature H S g).Finite := by
  exact Set.toFinite _

/-- The signature alphabet is bounded solely by the port size
and the girth cutoff. This is independent of the sizes of the
two private pieces or of the number of physical path witnesses. -/
theorem ncard_shortSignature_le
    {S : Set W} [Fintype S]
    (H : Set (Set W)) (g : ℕ) :
    (ShortSignature H S g).ncard ≤
      Fintype.card S * Fintype.card S * g := by
  classical
  have h := Set.ncard_le_ncard
    (Set.subset_univ (ShortSignature H S g))
    (Set.finite_univ : (Set.univ : Set (PortSymbol S g)).Finite)
  simpa [PortSymbol, Fintype.card_prod, Nat.card_eq_fintype_card,
    mul_assoc] using h

/-- A singleton (or empty) port has no path signature between
distinct interface vertices. This is the boundary analogue
of the unrestricted singleton-gluing girth lemma. -/
theorem shortSignature_empty_of_subsingleton
    {H : Set (Set W)} {S : Set W} {g : ℕ}
    (hS : S.Subsingleton) :
    ShortSignature H S g = ∅ := by
  ext a
  constructor
  · intro h
    have hEq : a.1 = a.2.1 :=
      Subtype.ext (hS a.1.property a.2.1.property)
    exact (h.1 hEq).elim
  · intro h
    simp at h

/-- A symbolic short cycle on the port with at least one excursion
from each side. A two-edge cycle is permitted (the two paths have
different side labels), while all boundary vertices must be
distinct. Parallel same-side/length types are collapsed by
ShortSignature, consistently with its existence-only semantics. -/
structure MixedPortCycle
    {S : Set W} {g : ℕ}
    (left right : Set (PortSymbol S g)) where
  length : ℕ
  atLeastTwo : 2 ≤ length
  port : Fin length → S
  port_injective : Function.Injective port
  side : Fin length → Bool
  cost : Fin length → Fin g
  step :
    ∀ i : Fin length,
       ( (port i, (port (cyclicSucc i), cost i)) ∈
           (if side i then left else right) ) ∨
       ( (port (cyclicSucc i), (port i, cost i)) ∈
           (if side i then left else right) )
  mixed : ∃ i j : Fin length, side i ≠ side j
  totalCost_lt : (∑ i : Fin length, (cost i).val) < g

/-- The exact finite-state *test* for a one-step free union.
The theorem linking this condition to GirthGT is the next
proof obligation; it is not assumed anywhere in the verified
circulation code. -/
def NoShortMixedPortCycle
    {S : Set W} {g : ℕ}
    (left right : Set (PortSymbol S g)) : Prop :=
  ¬ Nonempty (MixedPortCycle left right)

/-- A disjoint pair of empty signatures has no mixed cycle. -/
theorem noShortMixed_of_empty
    {S : Set W} {g : ℕ} :
    NoShortMixedPortCycle
      (∅ : Set (PortSymbol S g)) ∅ := by
  intro ⟨c⟩
  obtain ⟨i, j, _⟩ := c.mixed
  have h := c.step i
  cases hs : c.side i <;> simp [hs] at h

end BergePortSignature
end StructuralRamsey.Girth
