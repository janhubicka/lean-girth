import Girth.CanonicalClosedOccurrences
import Mathlib.Data.Finset.Max

/-!
# Canonical first-birth indices for complete closed-copy occurrences

Suppose a construction is given as a finite sequence of vertex stages
S_i in one final host G. The whole type of closed induced A-copies in
G is defined intrinsically, not by choosing a designated owner.

Each occurrence whose carrier appears in some stage has a UNIQUE least
birth stage, namely the first i containing all of its coordinates.
Under a monotone chain, an occurrence remains present after birth.

This does NOT say that the occurrence was formed in a single source
piece: newly born crossing P4 copies are precisely what the
closed-interface birth classification must handle. The construction
does not require a chosen list of A-copy owners.
-/

namespace StructuralRamsey.Girth
namespace CoherentPort

universe v
variable {U V : Type v}

/-- A closed occurrence is present at a stage precisely when its
whole coordinate image is contained in that stage. -/
def OccurrenceAppearsAt
    {A : SimpleGraph U} {G : SimpleGraph V}
    (S : Set V) (a : ClosedGraphOccurrence A G) : Prop :=
  Set.range a.toEmbedding ⊆ S

/-- The finite set of stages at which one intrinsic occurrence is
present. A stage index can be used as an event time. -/
noncomputable def occurrenceStages
    {n : ℕ} {A : SimpleGraph U} {G : SimpleGraph V}
    (S : Fin n → Set V) (a : ClosedGraphOccurrence A G) :
    Finset (Fin n) := by
  classical
  exact Finset.univ.filter (fun i => OccurrenceAppearsAt (S i) a)

/-- A nonempty collection of appearance stages has one canonical least
element in the finite linear order, independent of owner choices. -/
noncomputable def occurrenceFirstBirth
    {n : ℕ} {A : SimpleGraph U} {G : SimpleGraph V}
    (S : Fin n → Set V) (a : ClosedGraphOccurrence A G)
    (h : ∃ i : Fin n, OccurrenceAppearsAt (S i) a) : Fin n := by
  classical
  let T := occurrenceStages S a
  have hT : T.Nonempty := by
    obtain ⟨i, hi⟩ := h
    refine ⟨i, ?_⟩
    simpa [T, occurrenceStages] using hi
  exact T.min' hT

/-- A copy really appears at its first-birth stage. -/
theorem occurrenceFirstBirth_appears
    {n : ℕ} {A : SimpleGraph U} {G : SimpleGraph V}
    (S : Fin n → Set V) (a : ClosedGraphOccurrence A G)
    (h : ∃ i : Fin n, OccurrenceAppearsAt (S i) a) :
    OccurrenceAppearsAt (S (occurrenceFirstBirth S a h)) a := by
  classical
  let T := occurrenceStages S a
  have hT : T.Nonempty := by
    obtain ⟨i, hi⟩ := h
    exact ⟨i, by simpa [T, occurrenceStages] using hi⟩
  have hMem : T.min' hT ∈ T := Finset.min'_mem T hT
  have hAppears : OccurrenceAppearsAt (S (T.min' hT)) a := by
    simpa [T, occurrenceStages] using hMem
  simpa [occurrenceFirstBirth, T] using hAppears

/-- The first-birth stage is no later than any other stage containing
that same occurrence. -/
theorem occurrenceFirstBirth_le
    {n : ℕ} {A : SimpleGraph U} {G : SimpleGraph V}
    (S : Fin n → Set V) (a : ClosedGraphOccurrence A G)
    (h : ∃ i : Fin n, OccurrenceAppearsAt (S i) a)
    (i : Fin n) (hi : OccurrenceAppearsAt (S i) a) :
    occurrenceFirstBirth S a h ≤ i := by
  classical
  let T := occurrenceStages S a
  have hT : T.Nonempty := by
    obtain ⟨j, hj⟩ := h
    exact ⟨j, by simpa [T, occurrenceStages] using hj⟩
  have hiT : i ∈ T := by
    simpa [T, occurrenceStages] using hi
  simpa [occurrenceFirstBirth, T] using (Finset.min'_le T i hiT)

/-- A copy cannot be present before its canonical birth time. -/
theorem occurrence_not_before_birth
    {n : ℕ} {A : SimpleGraph U} {G : SimpleGraph V}
    (S : Fin n → Set V) (a : ClosedGraphOccurrence A G)
    (h : ∃ i : Fin n, OccurrenceAppearsAt (S i) a)
    (i : Fin n) (hi : i < occurrenceFirstBirth S a h) :
    ¬ OccurrenceAppearsAt (S i) a := by
  intro hAppears
  exact (not_le_of_gt hi) (occurrenceFirstBirth_le S a h i hAppears)

/-- A monotone stage chain retains every occurrence after its birth.
This is the elementary event-history invariant on intrinsic copies. -/
theorem occurrence_after_birth
    {n : ℕ} {A : SimpleGraph U} {G : SimpleGraph V}
    (S : Fin n → Set V) (hMono : Monotone S)
    (a : ClosedGraphOccurrence A G)
    (h : ∃ i : Fin n, OccurrenceAppearsAt (S i) a)
    (j : Fin n) (hj : occurrenceFirstBirth S a h ≤ j) :
    OccurrenceAppearsAt (S j) a :=
  Set.Subset.trans (occurrenceFirstBirth_appears S a h) (hMono hj)

end CoherentPort
end StructuralRamsey.Girth
