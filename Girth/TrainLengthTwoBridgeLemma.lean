import Girth.TrainBigCycleTwoWagonObstruction
import Girth.TrainSimultaneousSupreme

/-!
# Circulation: the exact length-two bridge-and-wagon lemma

The manuscript's Lemma "Bridge edges and common wagons" assumes only:
every acceptable TWO-OCCURRENCE big cycle has a globally legal supreme
copy (without an additional order restriction).

Part (i) says that any two distinct labels meeting one wagon at the
same vertex have actual incident physical bridge edges in that wagon.
Part (ii) excludes two distinct designated labels meeting two distinct
wagons. Both conclusions already follow from the two checked
canonical length-two probes and the necessary local-piece consequence
of a GLOBALLY LEGAL simultaneous supreme plan.

No broader system-Girth preservation or appendix result is used.
-/

namespace StructuralRamsey.Girth.OrderOneData

universe v
variable {V E I P : Type v} (D : OrderOneData V E I P)

/-- The precise premise of the circulation bridge lemma; this is
weaker than requiring the full system-Girth cutoff two, because
only cycles with TWO occurrences are considered. -/
def LengthTwoSupremeBound : Prop :=
  ∀ (C : D.BigCycle 2), C.Acceptable → C.HasSimultaneousSupreme

/-- An acceptable mixed vertex/wagon order-one cycle is a special
two-occurrence big cycle. Its actual globally supreme plan supplies
the order-one bridge bound, without postulating bridges separately. -/
theorem bound_of_lengthTwoSupreme
    (h : D.LengthTwoSupremeBound) : D.Bound := by
  intro C
  have hGlobal : C.toBigCycle.HasSimultaneousSupreme :=
    h C.toBigCycle C.toBigCycle_acceptable
  have hLocal : C.toBigCycle.HasLocalSupreme :=
    BigCycle.localSupreme_of_simultaneous D C.toBigCycle hGlobal
  exact Cycle.hasSupreme_of_bigCycle_localSupreme D C hLocal

/-- Bridge lemma (i): both arbitrary, distinct source labels have
an actual incident source edge belonging to the specified wagon. -/
theorem both_bridges_of_lengthTwoSupreme
    (h : D.LengthTwoSupremeBound)
    (a b : I ⊕ E) (x : V) (p : P)
    (hne : a ≠ b)
    (ha : x ∈ D.carrier a) (hb : x ∈ D.carrier b)
    (hma : D.Meets a p) (hmb : D.Meets b p) :
    D.Bridge a x p ∧ D.Bridge b x p :=
  D.both_bridges (D.bound_of_lengthTwoSupreme h) a b x p
    hne ha hb hma hmb

/-- Bridge lemma (ii): no two distinct designated labels both meet
two distinct wagons, even if the physical wagon carriers may overlap
in one vertex. No system-girth inequality is hidden in the premise. -/
theorem no_two_designated_two_wagons_of_lengthTwoSupreme
    (h : D.LengthTwoSupremeBound)
    (a b : I) (p q : P) (hab : a ≠ b) (hpq : p ≠ q)
    (hap : D.Meets (.inl a) p)
    (haq : D.Meets (.inl a) q)
    (hbp : D.Meets (.inl b) p)
    (hbq : D.Meets (.inl b) q) : False := by
  let C := D.twoWagonBigCycle a b p q hab hpq hap haq hbp hbq
  have hGlobal : C.HasSimultaneousSupreme :=
    h C (D.twoWagonBigCycle_acceptable
      a b p q hab hpq hap haq hbp hbq)
  have hLocal : C.HasLocalSupreme :=
    BigCycle.localSupreme_of_simultaneous D C hGlobal
  exact D.twoWagonBigCycle_no_localSupreme
    a b p q hab hpq hap haq hbp hbq hLocal

end StructuralRamsey.Girth.OrderOneData
