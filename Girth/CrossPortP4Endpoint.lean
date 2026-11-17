import Girth.PortSideP4Geometry

/-!
# Newly born induced P4 copies have no midpoint between their endpoints

In a free union over a midpoint-closed interface, the endpoints of
a crossing induced P4 lie in the two opposite private sides. A common
neighbour of these endpoints would have to lie in the interface, but
this conflicts with port closure or inducedness of the path.

The theorem below needs neither graph-girth nor a global closure
hypothesis for the P4 itself. In a graph of girth >= 5, the only
possible external common neighbour of two vertices of an induced P4
would be one shared by its endpoints: all shorter-distance pairs
would generate a triangle or a four-cycle. Thus the present lemma
is the key step proving that newly born induced crossing P4 copies
are automatically midpoint-closed in a girth-five free union.

It does not provide any Ramsey arrow or a construction of a
synchronized colour-table witness.
-/

namespace StructuralRamsey.Girth
namespace CoherentPort

universe v
variable {W : Type v} {adj : W → W → Prop}
variable {L R : Set W}

/-- A left-to-right crossing induced P4 cannot have a common neighbour
of its two endpoints, even one lying in the interface. The two missing
chords a-c and b-d are the only inducedness conditions used. -/
theorem crossing_induced_P4_no_endpoint_midpoint
    (hCover : L ∪ R = Set.univ)
    (hNoCross : ∀ ⦃a b⦄, a ∈ L \ R → b ∈ R \ L → ¬ adj a b)
    (hSymm : ∀ ⦃a b⦄, adj a b → adj b a)
    (hPortClosed : MidpointClosed (adj := adj) (L ∩ R))
    {a b c d z : W}
    (ha : a ∈ L \ R) (hd : d ∈ R \ L)
    (hab : adj a b) (hbc : adj b c) (hcd : adj c d)
    (hNoAC : ¬ adj a c) (hNoBD : ¬ adj b d)
    (haz : adj a z) (hdz : adj d z) : False := by
  have hzPort : z ∈ L ∩ R :=
    cross_common_neighbour_mem_port hCover hNoCross hSymm
      ha hd haz hdz
  rcases crossing_path3_internal_port hCover hNoCross
      ha hd hab hbc hcd with hbPort | hcPort
  · by_cases hzb : z = b
    · subst z
      exact hNoBD (hSymm hdz)
    · have hbz : b ≠ z := Ne.symm hzb
      have haPort : a ∈ L ∩ R :=
        hPortClosed hbPort hzPort hbz (hSymm hab) (hSymm haz)
      exact ha.2 haPort.2
  · by_cases hzc : z = c
    · subst z
      exact hNoAC haz
    · have hcz : c ≠ z := Ne.symm hzc
      have hdPort : d ∈ L ∩ R :=
        hPortClosed hcPort hzPort hcz hcd (hSymm hdz)
      exact hd.2 hdPort.1

/-- The reversed path has the same endpoint-midpoint obstruction. -/
theorem crossing_induced_P4_no_endpoint_midpoint_reversed
    (hCover : L ∪ R = Set.univ)
    (hNoCross : ∀ ⦃a b⦄, a ∈ L \ R → b ∈ R \ L → ¬ adj a b)
    (hSymm : ∀ ⦃a b⦄, adj a b → adj b a)
    (hPortClosed : MidpointClosed (adj := adj) (L ∩ R))
    {a b c d z : W}
    (ha : a ∈ R \ L) (hd : d ∈ L \ R)
    (hab : adj a b) (hbc : adj b c) (hcd : adj c d)
    (hNoAC : ¬ adj a c) (hNoBD : ¬ adj b d)
    (haz : adj a z) (hdz : adj d z) : False := by
  apply crossing_induced_P4_no_endpoint_midpoint
    hCover hNoCross hSymm hPortClosed hd ha
      (hSymm hcd) (hSymm hbc) (hSymm hab)
      (by intro h; exact hNoBD (hSymm h))
      (by intro h; exact hNoAC (hSymm h))
      hdz haz

end CoherentPort
end StructuralRamsey.Girth
