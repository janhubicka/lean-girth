import Girth.TrainSimultaneousSupreme
import Girth.LabelledWagonCutRestriction

/-!
# What full system girth gives at the first labelled-cut boundary

The linear-pretrain clause of FullSystemGirthGT implies labelled horizontal
cut girth greater than two, including distinct wagon labels with equal
physical carriers. This is a genuine consequence for every cutoff q.

At larger cutoffs, an acceptable edge-only BigCycle cannot occur in a
FullSystemGirthGT witness either. What remains is the geometric *lift*:
from an arbitrary labelled wagon-cut Berge cycle to such an acceptable
edge-only BigCycle with a controlled twice-order. Neither result below
asserts that lift. In particular, no arbitrary cut-girth bound > q is
deduced from FullSystemGirthGT q merely by changing definitions.
-/

namespace StructuralRamsey.Girth

universe v
variable {V P E I : Type v}

/-- Pairwise linearity of a *labelled* family excludes its genuine
labelled Berge two-cycles. Distinct labels are not identified by
equality of their carriers. -/
theorem labelledGirthGT_two_of_pairwiseSubsingleton
    (carrier : P → Set V)
    (hPair : ∀ p q : P, p ≠ q →
      (carrier p ∩ carrier q).Subsingleton) :
    LabelledGirthGT carrier 2 := by
  rintro ⟨C, hSmall⟩
  obtain ⟨n, hn, label, vertex, hLabel, hVertex, hLeft, hRight⟩ := C
  have hLength : n = 2 := by omega
  subst n
  have hpq : label 0 ≠ label 1 := by
    intro h
    exact (by decide : (0 : Fin 2) ≠ 1) (hLabel h)
  have hx : vertex 0 ∈ carrier (label 0) ∩ carrier (label 1) := by
    exact ⟨hLeft 0, by simpa [cyclicSucc] using hRight 0⟩
  have hy : vertex 1 ∈ carrier (label 0) ∩ carrier (label 1) := by
    exact ⟨by simpa [cyclicSucc] using hRight 1, hLeft 1⟩
  have hEq : vertex 0 = vertex 1 := hPair _ _ hpq hx hy
  exact (by decide : (0 : Fin 2) ≠ 1) (hVertex hEq)

namespace OrderOneData

/-- The pairwise wagon-carrier linearity included in any full system-girth
bound already yields exact labelled cut girth greater than two. -/
theorem labelledCutGirth_two_of_fullSystemGirth
    (D : OrderOneData V E I P) (q : ℕ) (h : D.FullSystemGirthGT q) :
    LabelledGirthGT (fun p : P => {x : V | D.WagonVertex p x}) 2 := by
  exact labelledGirthGT_two_of_pairwiseSubsingleton _
    (fun p r hpr => h.1.2 p r hpr)

/-- A genuinely acceptable cycle within the full system-girth budget
must contain a literal designated occurrence. This is a useful
necessary condition for the planned wagon-cycle lifting argument. -/
theorem BigCycle.designated_exists_of_fullSystemGirth
    (D : OrderOneData V E I P) {n : ℕ} (C : D.BigCycle n)
    (q : ℕ) (h : D.FullSystemGirthGT q)
    (hAccept : C.Acceptable) (hOrder : C.twiceOrder ≤ 2 * q) :
    ∃ i : Fin n, D.designated (C.label i) := by
  obtain ⟨k, hk, _⟩ := h.2 n C hAccept hOrder
  exact ⟨k, hk⟩

/-- The useful contrapositive: a short acceptable edge-only big cycle
contradicts full system girth. Constructing such a big cycle from a
labelled cut Berge cycle remains a separate geometric theorem. -/
theorem BigCycle.false_of_acceptable_edgeOnly_fullSystemGirth
    (D : OrderOneData V E I P) {n : ℕ} (C : D.BigCycle n)
    (q : ℕ) (h : D.FullSystemGirthGT q)
    (hAccept : C.Acceptable) (hOrder : C.twiceOrder ≤ 2 * q)
    (hOnly : ∀ i : Fin n, ∃ e : E, C.label i = Sum.inr e) : False := by
  obtain ⟨k, hk⟩ := C.designated_exists_of_fullSystemGirth D q h hAccept hOrder
  obtain ⟨e, he⟩ := hOnly k
  simp only [he, OrderOneData.designated] at hk

end OrderOneData
end StructuralRamsey.Girth
