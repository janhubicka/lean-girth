import Girth.PortSideP4Geometry

/-!
# No newly mixed graph cycles of length three, four or five

A common midpoint-closed port imposes two constraints on the side
locations of any simple cycle:
  (1) consecutive vertices cannot be left-private/right-private;
  (2) a cyclic triple cannot be shared/private/shared, since its two
      shared endpoints are distinct and closure forbids a private
      common neighbour.

A finite exhaustive check on PortSide proves that no cyclic word of
length 3, 4, or 5 contains BOTH kinds of private vertices while
satisfying these constraints. A length-six word LLSRRS does satisfy
them. The geometric result is that free gluing over a closed port
cannot CREATE a cycle of length < 6; every shorter cycle lies wholly
in one old side.

These are pure finite-type propositions with a proof by decide;
the geometric transfer uses sideLocation_step_of_free_adj and
sideLocation_no_hidden_midpoint in PortSideP4Geometry. The latter
requires simple-cycle distinctness for the endpoints of each two-step
segment. Higher girth is not claimed.
-/

namespace StructuralRamsey.Girth
namespace CoherentPort

private def PrivateBoth3 (a b c : PortSide) : Prop :=
  (a = .left ∨ b = .left ∨ c = .left) ∧
  (a = .right ∨ b = .right ∨ c = .right)

private def Steps3 (a b c : PortSide) : Prop :=
  SideStepAllowed a b ∧ SideStepAllowed b c ∧ SideStepAllowed c a

private def PortTriples3 (a b c : PortSide) : Prop :=
  NoHiddenPrivateMidpoint a b c ∧
  NoHiddenPrivateMidpoint b c a ∧
  NoHiddenPrivateMidpoint c a b

/-- No crossing triangle is compatible with a closed free interface. -/
theorem no_cross_private_cycle_three :
    ∀ a b c : PortSide,
      PrivateBoth3 a b c →
      Steps3 a b c → PortTriples3 a b c → False := by
  decide

private def PrivateBoth4 (a b c d : PortSide) : Prop :=
  (a = .left ∨ b = .left ∨ c = .left ∨ d = .left) ∧
  (a = .right ∨ b = .right ∨ c = .right ∨ d = .right)

private def Steps4 (a b c d : PortSide) : Prop :=
  SideStepAllowed a b ∧ SideStepAllowed b c ∧
  SideStepAllowed c d ∧ SideStepAllowed d a

private def PortTriples4 (a b c d : PortSide) : Prop :=
  NoHiddenPrivateMidpoint a b c ∧
  NoHiddenPrivateMidpoint b c d ∧
  NoHiddenPrivateMidpoint c d a ∧
  NoHiddenPrivateMidpoint d a b

/-- No crossing four-cycle is compatible with a closed free interface. -/
theorem no_cross_private_cycle_four :
    ∀ a b c d : PortSide,
      PrivateBoth4 a b c d →
      Steps4 a b c d → PortTriples4 a b c d → False := by
  decide

private def PrivateBoth5 (a b c d e : PortSide) : Prop :=
  (a = .left ∨ b = .left ∨ c = .left ∨ d = .left ∨ e = .left) ∧
  (a = .right ∨ b = .right ∨ c = .right ∨ d = .right ∨ e = .right)

private def Steps5 (a b c d e : PortSide) : Prop :=
  SideStepAllowed a b ∧ SideStepAllowed b c ∧
  SideStepAllowed c d ∧ SideStepAllowed d e ∧
  SideStepAllowed e a

private def PortTriples5 (a b c d e : PortSide) : Prop :=
  NoHiddenPrivateMidpoint a b c ∧
  NoHiddenPrivateMidpoint b c d ∧
  NoHiddenPrivateMidpoint c d e ∧
  NoHiddenPrivateMidpoint d e a ∧
  NoHiddenPrivateMidpoint e a b

/-- No crossing five-cycle is compatible with a closed free interface. -/
theorem no_cross_private_cycle_five :
    ∀ a b c d e : PortSide,
      PrivateBoth5 a b c d e →
      Steps5 a b c d e → PortTriples5 a b c d e → False := by
  decide

/-- The length-six cyclic side word LLSRRS is combinatorially allowed:
this witnesses the sharpness of the <6 obstruction at the level of
side-position geometry (two length-three paths are realizations). -/
theorem six_cycle_location_pattern_allowed :
    SideStepAllowed .left .left ∧
    SideStepAllowed .left .shared ∧
    SideStepAllowed .shared .right ∧
    SideStepAllowed .right .right ∧
    SideStepAllowed .right .shared ∧
    SideStepAllowed .shared .left ∧
    NoHiddenPrivateMidpoint .left .left .shared ∧
    NoHiddenPrivateMidpoint .left .shared .right ∧
    NoHiddenPrivateMidpoint .shared .right .right ∧
    NoHiddenPrivateMidpoint .right .right .shared ∧
    NoHiddenPrivateMidpoint .right .shared .left ∧
    NoHiddenPrivateMidpoint .shared .left .left := by
  decide

end CoherentPort
end StructuralRamsey.Girth
