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

universe v

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
  intro a b c hCross hEdges hMidpoints
  cases a <;> cases b <;> cases c <;>
    simp_all [PrivateBoth3, Steps3, PortTriples3,
      SideStepAllowed, NoHiddenPrivateMidpoint]

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
  intro a b c d hCross hEdges hMidpoints
  cases a <;> cases b <;> cases c <;> cases d <;>
    simp_all [PrivateBoth4, Steps4, PortTriples4,
      SideStepAllowed, NoHiddenPrivateMidpoint]

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
  intro a b c d e hCross hEdges hMidpoints
  cases a <;> cases b <;> cases c <;> cases d <;> cases e <;>
    simp_all [PrivateBoth5, Steps5, PortTriples5,
      SideStepAllowed, NoHiddenPrivateMidpoint]

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
  simp [SideStepAllowed, NoHiddenPrivateMidpoint]

/-- Geometric impossibility of a triangle meeting both private sides.
Distinctness is stated at the two-step distances, as needed by the
midpoint-closed interface hypothesis. -/
theorem no_mixed_triangle_of_closed_port
    {W : Type v} {adj : W → W → Prop} {L R : Set W}
    (hCover : L ∪ R = Set.univ)
    (hNoCross : ∀ ⦃a b⦄, a ∈ L \ R → b ∈ R \ L → ¬ adj a b)
    (hSymm : ∀ ⦃a b⦄, adj a b → adj b a)
    (hPortClosed : MidpointClosed (adj := adj) (L ∩ R))
    {a b c : W} (hac : a ≠ c) (hba : b ≠ a) (hcb : c ≠ b)
    (hab : adj a b) (hbc : adj b c) (hca : adj c a)
    (hCross : PrivateBoth3 (sideLocation L R a)
      (sideLocation L R b) (sideLocation L R c)) : False := by
  exact no_cross_private_cycle_three _ _ _ hCross
    ⟨sideLocation_step_of_free_adj hCover hNoCross hSymm hab,
     sideLocation_step_of_free_adj hCover hNoCross hSymm hbc,
     sideLocation_step_of_free_adj hCover hNoCross hSymm hca⟩
    ⟨sideLocation_no_hidden_midpoint hSymm hPortClosed hac hab hbc,
     sideLocation_no_hidden_midpoint hSymm hPortClosed hba hbc hca,
     sideLocation_no_hidden_midpoint hSymm hPortClosed hcb hca hab⟩

/-- No simple four-cycle can meet both private sides of a free gluing
over a midpoint-closed interface. -/
theorem no_mixed_square_of_closed_port
    {W : Type v} {adj : W → W → Prop} {L R : Set W}
    (hCover : L ∪ R = Set.univ)
    (hNoCross : ∀ ⦃a b⦄, a ∈ L \ R → b ∈ R \ L → ¬ adj a b)
    (hSymm : ∀ ⦃a b⦄, adj a b → adj b a)
    (hPortClosed : MidpointClosed (adj := adj) (L ∩ R))
    {a b c d : W} (hac : a ≠ c) (hbd : b ≠ d)
    (hab : adj a b) (hbc : adj b c)
    (hcd : adj c d) (hda : adj d a)
    (hCross : PrivateBoth4 (sideLocation L R a)
      (sideLocation L R b) (sideLocation L R c)
      (sideLocation L R d)) : False := by
  exact no_cross_private_cycle_four _ _ _ _ hCross
    ⟨sideLocation_step_of_free_adj hCover hNoCross hSymm hab,
     sideLocation_step_of_free_adj hCover hNoCross hSymm hbc,
     sideLocation_step_of_free_adj hCover hNoCross hSymm hcd,
     sideLocation_step_of_free_adj hCover hNoCross hSymm hda⟩
    ⟨sideLocation_no_hidden_midpoint hSymm hPortClosed hac hab hbc,
     sideLocation_no_hidden_midpoint hSymm hPortClosed hbd hbc hcd,
     sideLocation_no_hidden_midpoint hSymm hPortClosed hac.symm hcd hda,
     sideLocation_no_hidden_midpoint hSymm hPortClosed hbd.symm hda hab⟩

/-- No simple five-cycle can meet both private sides of a free gluing
over a midpoint-closed interface. -/
theorem no_mixed_pentagon_of_closed_port
    {W : Type v} {adj : W → W → Prop} {L R : Set W}
    (hCover : L ∪ R = Set.univ)
    (hNoCross : ∀ ⦃a b⦄, a ∈ L \ R → b ∈ R \ L → ¬ adj a b)
    (hSymm : ∀ ⦃a b⦄, adj a b → adj b a)
    (hPortClosed : MidpointClosed (adj := adj) (L ∩ R))
    {a b c d e : W}
    (hac : a ≠ c) (hbd : b ≠ d) (hce : c ≠ e)
    (hda : d ≠ a) (heb : e ≠ b)
    (hab : adj a b) (hbc : adj b c) (hcd : adj c d)
    (hde : adj d e) (hea : adj e a)
    (hCross : PrivateBoth5 (sideLocation L R a)
      (sideLocation L R b) (sideLocation L R c)
      (sideLocation L R d) (sideLocation L R e)) : False := by
  exact no_cross_private_cycle_five _ _ _ _ _ hCross
    ⟨sideLocation_step_of_free_adj hCover hNoCross hSymm hab,
     sideLocation_step_of_free_adj hCover hNoCross hSymm hbc,
     sideLocation_step_of_free_adj hCover hNoCross hSymm hcd,
     sideLocation_step_of_free_adj hCover hNoCross hSymm hde,
     sideLocation_step_of_free_adj hCover hNoCross hSymm hea⟩
    ⟨sideLocation_no_hidden_midpoint hSymm hPortClosed hac hab hbc,
     sideLocation_no_hidden_midpoint hSymm hPortClosed hbd hbc hcd,
     sideLocation_no_hidden_midpoint hSymm hPortClosed hce hcd hde,
     sideLocation_no_hidden_midpoint hSymm hPortClosed hda hde hea,
     sideLocation_no_hidden_midpoint hSymm hPortClosed heb hea hab⟩

end CoherentPort
end StructuralRamsey.Girth
