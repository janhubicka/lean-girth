import Girth.CrossPortP4Birth

/-!
# Finite three-type catalogue of P4 births at a closed free port

For a simple graph freely glued along a midpoint-closed interface,
each vertex of an induced four-vertex path has one of three positions:
left-private (L), shared interface (S), or right-private (R).
Adjacent vertices cannot have positions L-R or R-L. Moreover a
simple path cannot contain S-L-S or S-R-S: the middle vertex would
be a common neighbour of distinct interface vertices, contradicting
closure of the interface.

An exhaustive proof on the three-element side type shows that every
path meeting BOTH private sides has one of THREE shapes, up to reversal:
LLSR, LSRR, LSSR. The result is a pure finite classification theorem,
separate from the geometric proof that a particular graph induces its
two hypotheses. See FreePortMidpointClosed and CrossPortP4Birth.
-/

namespace StructuralRamsey.Girth
namespace CoherentPort

/-- A vertex in a free union is on the left-only side, in the
interface, or on the right-only side. -/
inductive PortSide where
  | left
  | shared
  | right
  deriving DecidableEq, Repr

/-- Avoid elaborator dependence on generated enumList coercions. -/
instance : Fintype PortSide where
  elems := {.left, .shared, .right}
  complete := by
    intro x
    cases x <;> simp

/-- Free gluing forbids an edge directly between opposite private sides. -/
def SideStepAllowed : PortSide → PortSide → Prop
  | .left, .right => False
  | .right, .left => False
  | _, _ => True

/-- Midpoint closure excludes a two-edge path from the port to itself
whose intermediate vertex is private. The vertex endpoints of an
induced P4 are all distinct, so the two shared endpoints here are
different physical vertices. -/
def NoHiddenPrivateMidpoint (a b c : PortSide) : Prop :=
  a = .shared → c = .shared → b = .shared

/-- Both private sides occur in this four-position path. -/
def CrossesPrivateSides (a b c d : PortSide) : Prop :=
  (a = .left ∨ b = .left ∨ c = .left ∨ d = .left) ∧
  (a = .right ∨ b = .right ∨ c = .right ∨ d = .right)

/-- The three possible new P4 birth shapes, up to path reversal. -/
def IsCrossPortP4Birth (a b c d : PortSide) : Prop :=
  (a = .left ∧ b = .left ∧ c = .shared ∧ d = .right) ∨
  (a = .right ∧ b = .shared ∧ c = .left ∧ d = .left) ∨
  (a = .left ∧ b = .shared ∧ c = .right ∧ d = .right) ∨
  (a = .right ∧ b = .right ∧ c = .shared ∧ d = .left) ∨
  (a = .left ∧ b = .shared ∧ c = .shared ∧ d = .right) ∨
  (a = .right ∧ b = .shared ∧ c = .shared ∧ d = .left)

/-- All 3^4 side words are checked by the kernel; the hypotheses
exclude the direct left/right edges and hidden private midpoints.
There are six oriented possibilities, three up to reversal. -/
theorem only_three_cross_port_P4_types :
    ∀ a b c d : PortSide,
      CrossesPrivateSides a b c d →
      SideStepAllowed a b →
      SideStepAllowed b c →
      SideStepAllowed c d →
      NoHiddenPrivateMidpoint a b c →
      NoHiddenPrivateMidpoint b c d →
      IsCrossPortP4Birth a b c d := by
  intro a b c d hCross hAB hBC hCD hM1 hM2
  cases a <;> cases b <;> cases c <;> cases d <;>
    simp_all [CrossesPrivateSides, SideStepAllowed,
      NoHiddenPrivateMidpoint, IsCrossPortP4Birth]

end CoherentPort
end StructuralRamsey.Girth
