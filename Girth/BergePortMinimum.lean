import Girth.BergePortSignature
import Mathlib.Data.Finset.Max

/-!
# Compress finite Berge-port path signatures to minimum lengths

For fixed girth threshold g, endpoints s,t and side H, only
the shortest *port-avoiding* Berge excursion matters for detecting
a mixed boundary cycle of weight < g. Replacing any realized
excursion by a shorter one on the same side and with the same
endpoints preserves the cycle's port vertices and side colours
and cannot increase its total weight.

This file proves the elementary minimum-existence step, then
builds this replacement *simultaneously for every edge* in a
MixedPortCycle. Consequently the full symbolic mixed-cycle test
is equivalent to its subtest using only minimum costs.

This is a compression theorem for the SIGNATURE TEST, not yet
the theorem relating that signature test to actual hypergraph
Berge girth (which requires the mod-two incidence parity lemma).
-/

namespace StructuralRamsey.Girth
namespace BergePortSignature

universe v
variable {W : Type v}

/-- A signature retaining only the minimum realized private
Berge length for each ordered port pair. -/
def MinShortSignature
    (H : Set (Set W)) (S : Set W) (g : ℕ) :
    Set (PortSymbol S g) :=
  {a | a ∈ ShortSignature H S g ∧
      ∀ k : Fin g,
        (a.1, (a.2.1, k)) ∈ ShortSignature H S g →
        a.2.2.val ≤ k.val}

/-- The minimum-cost signature is a subfamily of the full
existence signature. -/
theorem minShortSignature_subset
    (H : Set (Set W)) (S : Set W) (g : ℕ) :
    MinShortSignature H S g ⊆ ShortSignature H S g :=
  fun _ h => h.1

/-- A nonempty set of realized path lengths has a least
member, in the finite linear order Fin g. -/
theorem exists_minimal_port_cost
    (H : Set (Set W)) (S : Set W) (g : ℕ)
    (s t : S)
    (hex : ∃ k : Fin g,
      (s, (t, k)) ∈ ShortSignature H S g) :
    ∃ k : Fin g,
      (s, (t, k)) ∈ ShortSignature H S g ∧
      (∀ ell : Fin g,
        (s, (t, ell)) ∈ ShortSignature H S g →
        k.val ≤ ell.val) := by
  classical
  let T : Finset (Fin g) :=
    Finset.univ.filter (fun k => (s, (t, k)) ∈ ShortSignature H S g)
  have hT : T.Nonempty := by
    obtain ⟨k, hk⟩ := hex
    exact ⟨k, by simpa [T] using hk⟩
  refine ⟨T.min' hT, ?_, ?_⟩
  · have hm := Finset.min'_mem T hT
    simpa [T] using hm
  · intro ell hell
    have hm : ell ∈ T := by
      simpa [T] using hell
    simpa only [Fin.le_def] using Finset.min'_le T ell hm

/-- Every full signature symbol admits a minimum-cost replacement
on the same ordered port pair, never increasing the cost. -/
theorem exists_minShortSignature_le
    (H : Set (Set W)) (S : Set W) (g : ℕ)
    (a : PortSymbol S g)
    (ha : a ∈ ShortSignature H S g) :
    ∃ k : Fin g,
      (a.1, (a.2.1, k)) ∈ MinShortSignature H S g ∧
      k.val ≤ a.2.2.val := by
  obtain ⟨k, hk, hMin⟩ :=
    exists_minimal_port_cost H S g a.1 a.2.1
      ⟨a.2.2, ha⟩
  exact ⟨k, ⟨hk, hMin⟩, hMin _ ha⟩

/-- A mixed symbolic cycle with arbitrary realized path lengths
can be compressed to one using only the shortest length for
each endpoint pair and side. No physical path realizations
are selected or required to be disjoint. -/
noncomputable def MixedPortCycle.compress
    {HL HR : Set (Set W)} {S : Set W} {g : ℕ}
    (C : MixedPortCycle
      (ShortSignature HL S g) (ShortSignature HR S g)) :
    MixedPortCycle
      (MinShortSignature HL S g) (MinShortSignature HR S g) := by
  classical
  have chooseStep (i : Fin C.length) :
      ∃ k : Fin g,
        k.val ≤ (C.cost i).val ∧
        ((C.port i, (C.port (cyclicSucc i), k)) ∈
          (if C.side i then MinShortSignature HL S g
            else MinShortSignature HR S g) ∨
         (C.port (cyclicSucc i), (C.port i, k)) ∈
          (if C.side i then MinShortSignature HL S g
            else MinShortSignature HR S g)) := by
    have hOld := C.step i
    cases hs : C.side i with
    | false =>
        simp only [hs, Bool.false_eq_true, ite_false] at hOld ⊢
        rcases hOld with hf | hr
        · obtain ⟨k, hk, hle⟩ :=
            exists_minShortSignature_le HR S g _ hf
          exact ⟨k, hle, Or.inl hk⟩
        · obtain ⟨k, hk, hle⟩ :=
            exists_minShortSignature_le HR S g _ hr
          exact ⟨k, hle, Or.inr hk⟩
    | true =>
        simp only [hs, ite_true] at hOld ⊢
        rcases hOld with hf | hr
        · obtain ⟨k, hk, hle⟩ :=
            exists_minShortSignature_le HL S g _ hf
          exact ⟨k, hle, Or.inl hk⟩
        · obtain ⟨k, hk, hle⟩ :=
            exists_minShortSignature_le HL S g _ hr
          exact ⟨k, hle, Or.inr hk⟩
  let newCost : Fin C.length → Fin g :=
    fun i => Classical.choose (chooseStep i)
  have newCost_spec (i : Fin C.length) :
      (newCost i).val ≤ (C.cost i).val ∧
      ((C.port i, (C.port (cyclicSucc i), newCost i)) ∈
        (if C.side i then MinShortSignature HL S g
          else MinShortSignature HR S g) ∨
       (C.port (cyclicSucc i), (C.port i, newCost i)) ∈
        (if C.side i then MinShortSignature HL S g
          else MinShortSignature HR S g)) :=
    Classical.choose_spec (chooseStep i)
  refine {
    length := C.length
    atLeastTwo := C.atLeastTwo
    port := C.port
    port_injective := C.port_injective
    side := C.side
    cost := newCost
    step := fun i => (newCost_spec i).2
    mixed := C.mixed
    totalCost_lt := ?_
  }
  have hle :
      (∑ i : Fin C.length, (newCost i).val) ≤
        ∑ i : Fin C.length, (C.cost i).val := by
    apply Finset.sum_le_sum
    intro i _
    exact (newCost_spec i).1
  exact lt_of_le_of_lt hle C.totalCost_lt

/-- Any mixed cycle formed from minimum-cost entries is also a
cycle in the full signature: the minimum entries were realized. -/
def MixedPortCycle.expand
    {HL HR : Set (Set W)} {S : Set W} {g : ℕ}
    (C : MixedPortCycle
      (MinShortSignature HL S g) (MinShortSignature HR S g)) :
    MixedPortCycle
      (ShortSignature HL S g) (ShortSignature HR S g) := by
  have hSub (side : Bool) :
      (if side then MinShortSignature HL S g
        else MinShortSignature HR S g) ⊆
      (if side then ShortSignature HL S g
        else ShortSignature HR S g) := by
    cases side
    · exact minShortSignature_subset HR S g
    · exact minShortSignature_subset HL S g
  exact {
    length := C.length
    atLeastTwo := C.atLeastTwo
    port := C.port
    port_injective := C.port_injective
    side := C.side
    cost := C.cost
    step := by
      intro i
      rcases C.step i with h | h
      · exact Or.inl (hSub (C.side i) h)
      · exact Or.inr (hSub (C.side i) h)
    mixed := C.mixed
    totalCost_lt := C.totalCost_lt
  }

/-- EXACT finite-state compression: keeping only one shortest
private Berge length per ordered boundary pair and side
does not change whether a short mixed signature cycle exists. -/
theorem noShortMixed_iff_minimum
    (HL HR : Set (Set W)) (S : Set W) (g : ℕ) :
    NoShortMixedPortCycle
        (ShortSignature HL S g) (ShortSignature HR S g) ↔
      NoShortMixedPortCycle
        (MinShortSignature HL S g) (MinShortSignature HR S g) := by
  constructor
  · intro h ⟨C⟩
    exact h ⟨C.expand⟩
  · intro h ⟨C⟩
    exact h ⟨C.compress⟩

end BergePortSignature
end StructuralRamsey.Girth
