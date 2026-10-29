import Girth.TrainBigCycleTwoWagonObstruction

set_option Elab.async false

/-!
# A designated hub with two labels at a common vertex

Let a designated copy meet two distinct wagons. Two other labels, each
meeting its prescribed wagon and containing a common vertex, complete a
three-occurrence cycle with connectors wagon / vertex / wagon. The labels
may be designated copies or actual edges. No hypothesis says that the
common vertex already belongs to either wagon or to the hub copy.

The cycle has order two and satisfies A1--A3. A locally supreme occurrence
different from the hub would have to replace the hub between two distinct
wagon connectors, which is impossible. The hub must therefore be locally
supreme; its two mixed replacements give actual hub edges in the prescribed
wagons through the common vertex.

The conclusion uses only the local-piece bound. It neither asserts global
replacement legality nor assumes wagon linearity, carrier injectivity, or
consistency between a raw `OrderOneData` copy carrier and its copy edges.
-/

namespace StructuralRamsey.Girth.OrderOneData

universe v
variable {V E I P : Type v} (D : OrderOneData V E I P)

/-- Three pairwise distinct labels with a designated hub and connector
sequence wagon p / vertex x / wagon q. The other two labels are arbitrary. -/
def twoLabelVertexProbe
    (i : I) (a b : I ⊕ E) (p q : P) (x : V) (hpq : p ≠ q)
    (hia : Sum.inl i ≠ a) (hib : Sum.inl i ≠ b) (hab : a ≠ b)
    (hip : D.Meets (.inl i) p) (hiq : D.Meets (.inl i) q)
    (hxa : x ∈ D.carrier a) (hxb : x ∈ D.carrier b)
    (hap : D.Meets a p) (hbq : D.Meets b q) :
    D.BigCycle 3 where
  length_ge_two := by omega
  label := ![Sum.inl i, a, b]
  connector := ![Sum.inr p, Sum.inl x, Sum.inr q]
  adjacent_ne := by
    intro k
    fin_cases k
    · simpa [cyclicSucc] using hia
    · simpa [cyclicSucc] using hab
    · simpa [cyclicSucc] using hib.symm
  connector_injective := by
    intro k l h
    fin_cases k <;> fin_cases l <;> simp_all
  left_incident := by
    intro k
    fin_cases k
    · exact hip
    · exact hxa
    · exact hbq
  right_incident := by
    intro k
    fin_cases k
    · exact hap
    · exact hxb
    · exact hiq

/-- The two mixed occurrences have weight one and the hub occurrence has
weight two, so the probe has order two. -/
theorem twoLabelVertexProbe_twiceOrder
    (i : I) (a b : I ⊕ E) (p q : P) (x : V) (hpq : p ≠ q)
    (hia : Sum.inl i ≠ a) (hib : Sum.inl i ≠ b) (hab : a ≠ b)
    (hip : D.Meets (.inl i) p) (hiq : D.Meets (.inl i) q)
    (hxa : x ∈ D.carrier a) (hxb : x ∈ D.carrier b)
    (hap : D.Meets a p) (hbq : D.Meets b q) :
    (D.twoLabelVertexProbe i a b p q x hpq hia hib hab hip hiq hxa hxb hap hbq).twiceOrder = 4 := by
  simp [BigCycle.twiceOrder, connectorKind, twoLabelVertexProbe,
    Fin.sum_univ_three, cyclicSucc, twiceOccurrenceWeight]

/-- There is only one vertex position. It is adjacent to both wagon
positions, and neither wagon position has two vertex neighbors; hence A2's
ambient nonedge premise cannot occur. A3 is also immediate. -/
theorem twoLabelVertexProbe_acceptable
    (i : I) (a b : I ⊕ E) (p q : P) (x : V) (hpq : p ≠ q)
    (hia : Sum.inl i ≠ a) (hib : Sum.inl i ≠ b) (hab : a ≠ b)
    (hip : D.Meets (.inl i) p) (hiq : D.Meets (.inl i) q)
    (hxa : x ∈ D.carrier a) (hxb : x ∈ D.carrier b)
    (hap : D.Meets a p) (hbq : D.Meets b q) :
    (D.twoLabelVertexProbe i a b p q x hpq hia hib hab hip hiq hxa hxb hap hbq).Acceptable := by
  let C := D.twoLabelVertexProbe i a b p q x hpq hia hib hab hip hiq hxa hxb hap hbq
  change C.Acceptable
  refine ⟨?_, ?_, ?_⟩
  · intro _
    exact ⟨(0 : Fin 3), trivial⟩
  · constructor
    · intro k w hk j hj
      obtain ⟨z, hz, _⟩ := hj
      fin_cases k <;> fin_cases j <;>
        simp_all [C, twoLabelVertexProbe, cyclicSucc, trainCyclicPred]
    · intro k w u v hk hPrev hNext _ _ _
      fin_cases k
      · simp [C, twoLabelVertexProbe, trainCyclicPred] at hPrev
      · simp [C, twoLabelVertexProbe] at hk
      · simp [C, twoLabelVertexProbe, cyclicSucc] at hNext
  · intro w _
    refine ⟨(1 : Fin 3), ?_⟩
    intro j hj
    fin_cases j
    · obtain ⟨z, hz, _⟩ := hj
      simp [C, twoLabelVertexProbe] at hz
    · exact Or.inl rfl
    · obtain ⟨z, hz, _⟩ := hj
      simp [C, twoLabelVertexProbe] at hz

/-- The hub is forced to be locally supreme: a different supreme label
would replace the hub between two distinct wagon boundaries. Its two mixed
replacement pieces therefore give both prescribed vertex--wagon bridges.
The common vertex need not be a wagon vertex in the hypotheses. -/
theorem copy_bridges_of_two_label_vertex_probe
    (hBound : D.LocalPieceSystemBound 2)
    (i : I) (a b : I ⊕ E) (p q : P) (x : V) (hpq : p ≠ q)
    (hia : Sum.inl i ≠ a) (hib : Sum.inl i ≠ b) (hab : a ≠ b)
    (hip : D.Meets (.inl i) p) (hiq : D.Meets (.inl i) q)
    (hxa : x ∈ D.carrier a) (hxb : x ∈ D.carrier b)
    (hap : D.Meets a p) (hbq : D.Meets b q) :
    D.Bridge (.inl i) x p ∧ D.Bridge (.inl i) x q := by
  let C := D.twoLabelVertexProbe i a b p q x hpq hia hib hab hip hiq hxa hxb hap hbq
  have hAcc : C.Acceptable :=
    D.twoLabelVertexProbe_acceptable i a b p q x hpq hia hib hab hip hiq hxa hxb hap hbq
  have hOrd : C.twiceOrder ≤ 2 * 2 := by
    rw [D.twoLabelVertexProbe_twiceOrder i a b p q x hpq hia hib hab hip hiq hxa hxb hap hbq]
  obtain ⟨k, _hk, hPieces⟩ := hBound 3 C hAcc hOrd
  fin_cases k
  · have hne1 : C.label 1 ≠ C.label 0 := by
      simpa [C, twoLabelVertexProbe] using hia.symm
    have hne2 : C.label 2 ≠ C.label 0 := by
      simpa [C, twoLabelVertexProbe] using hib.symm
    have hPiece1 := hPieces 1 hne1
    have hPiece2 := hPieces 2 hne2
    constructor
    · exact D.piece_mixed_bridge_reverse (.inl i) x p
        (by simpa [C, twoLabelVertexProbe, trainCyclicPred] using hPiece1)
    · exact D.piece_mixed_bridge (.inl i) x q
        (by simpa [C, twoLabelVertexProbe, trainCyclicPred] using hPiece2)
  · have hne : C.label 0 ≠ C.label 1 := by
      simpa [C, twoLabelVertexProbe] using hia
    have hPiece := hPieces 0 hne
    have hqp : q = p := D.piece_two_wagon_forces_eq a q p
      (by simpa [C, twoLabelVertexProbe, trainCyclicPred] using hPiece)
    exact False.elim (hpq hqp.symm)
  · have hne : C.label 0 ≠ C.label 2 := by
      simpa [C, twoLabelVertexProbe] using hib
    have hPiece := hPieces 0 hne
    have hqp : q = p := D.piece_two_wagon_forces_eq b q p
      (by simpa [C, twoLabelVertexProbe, trainCyclicPred] using hPiece)
    exact False.elim (hpq hqp.symm)

end StructuralRamsey.Girth.OrderOneData
