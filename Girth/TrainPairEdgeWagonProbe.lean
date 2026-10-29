import Girth.TrainBigCycleOrderOneExtraction

set_option Elab.async false

/-!
# A pair edge and two labels meeting one wagon

An actual edge through distinct vertices x,y and two other labels F,G give
a three-occurrence cycle with connectors vertex x / wagon p / vertex y,
provided F contains x, G contains y, and both meet p. The cycle is acceptable
when at least one of x,y is not a vertex of p. The ambient pair edge is
present: A2 holds because its two wagon-incidence premises cannot both hold,
not because the vertices are nonadjacent.

Local supremeness cannot occur at the actual edge label. A supreme F supplies
a p-edge through y; a supreme G supplies a p-edge through x. This local bridge
alternative needs neither source linearity nor global replacement legality.
-/

namespace StructuralRamsey.Girth.OrderOneData

universe v
variable {V E I P : Type v} (D : OrderOneData V E I P)

/-- The three labels are an actual pair edge and two arbitrary labels
meeting one wagon. All adjacent label inequalities remain explicit. -/
def pairEdgeWagonProbe
    (g : E) (F G : I ⊕ E) (p : P) (x y : V)
    (hxy : x ≠ y) (hFG : F ≠ G)
    (hgF : Sum.inr g ≠ F) (hgG : Sum.inr g ≠ G)
    (hxg : x ∈ D.edgeCarrier g) (hyg : y ∈ D.edgeCarrier g)
    (hxF : x ∈ D.carrier F) (hyG : y ∈ D.carrier G)
    (hFp : D.Meets F p) (hGp : D.Meets G p) : D.BigCycle 3 where
  length_ge_two := by omega
  label := ![Sum.inr g, F, G]
  connector := ![Sum.inl x, Sum.inr p, Sum.inl y]
  adjacent_ne := by
    intro k
    fin_cases k
    · simpa [cyclicSucc] using hgF
    · simpa [cyclicSucc] using hFG
    · simpa [cyclicSucc] using hgG.symm
  connector_injective := by
    intro k l h
    fin_cases k <;> fin_cases l <;> simp_all
  left_incident := by
    intro k
    fin_cases k
    · exact hxg
    · exact hFp
    · exact hyG
  right_incident := by
    intro k
    fin_cases k
    · exact hxF
    · exact hGp
    · exact hyg

/-- The connector kinds vertex/wagon/vertex give order two. -/
theorem pairEdgeWagonProbe_twiceOrder
    (g : E) (F G : I ⊕ E) (p : P) (x y : V)
    (hxy : x ≠ y) (hFG : F ≠ G)
    (hgF : Sum.inr g ≠ F) (hgG : Sum.inr g ≠ G)
    (hxg : x ∈ D.edgeCarrier g) (hyg : y ∈ D.edgeCarrier g)
    (hxF : x ∈ D.carrier F) (hyG : y ∈ D.carrier G)
    (hFp : D.Meets F p) (hGp : D.Meets G p) :
    (D.pairEdgeWagonProbe g F G p x y hxy hFG hgF hgG hxg hyg hxF hyG hFp hGp).twiceOrder = 4 := by
  simp [BigCycle.twiceOrder, connectorKind, pairEdgeWagonProbe,
    Fin.sum_univ_three, cyclicSucc, twiceOccurrenceWeight]

/-- A2's ambient nonedge clause is vacuous because its two wagon-vertex
premises cannot both hold. No absence of an ambient pair edge is asserted. -/
theorem pairEdgeWagonProbe_acceptable
    (g : E) (F G : I ⊕ E) (p : P) (x y : V)
    (hxy : x ≠ y) (hFG : F ≠ G)
    (hgF : Sum.inr g ≠ F) (hgG : Sum.inr g ≠ G)
    (hxg : x ∈ D.edgeCarrier g) (hyg : y ∈ D.edgeCarrier g)
    (hxF : x ∈ D.carrier F) (hyG : y ∈ D.carrier G)
    (hFp : D.Meets F p) (hGp : D.Meets G p)
    (hMissing : ¬ (D.WagonVertex p x ∧ D.WagonVertex p y)) :
    (D.pairEdgeWagonProbe g F G p x y hxy hFG hgF hgG hxg hyg hxF hyG hFp hGp).Acceptable := by
  let C := D.pairEdgeWagonProbe g F G p x y hxy hFG hgF hgG hxg hyg hxF hyG hFp hGp
  change C.Acceptable
  refine ⟨?_, ?_, ?_⟩
  · intro ht
    have hfour : C.twiceOrder = 4 :=
      D.pairEdgeWagonProbe_twiceOrder g F G p x y hxy hFG hgF hgG hxg hyg hxF hyG hFp hGp
    have heq : (4 : ℕ) = 2 := hfour.symm.trans ht
    exact False.elim ((by decide : (4 : ℕ) ≠ 2) heq)
  · constructor
    · intro k w hk j hj
      fin_cases k
      · simp [C, pairEdgeWagonProbe] at hk
      · fin_cases j
        · exact Or.inl (by decide)
        · obtain ⟨z, hz, _⟩ := hj
          simp [C, pairEdgeWagonProbe] at hz
        · exact Or.inr (by decide)
      · simp [C, pairEdgeWagonProbe] at hk
    · intro k w vx vy hk hPrev hNext _ hvx hvy
      fin_cases k
      · simp [C, pairEdgeWagonProbe] at hk
      · have hw : w = p := by
          simpa [C, pairEdgeWagonProbe] using hk.symm
        have hx : vx = x := by
          simpa [C, pairEdgeWagonProbe, trainCyclicPred] using hPrev.symm
        have hy : vy = y := by
          simpa [C, pairEdgeWagonProbe, cyclicSucc] using hNext.symm
        subst w
        subst vx
        subst vy
        exact False.elim (hMissing ⟨hvx, hvy⟩)
      · simp [C, pairEdgeWagonProbe] at hk
  · intro w _
    refine ⟨(2 : Fin 3), ?_⟩
    intro j hj
    fin_cases j
    · exact Or.inr (by decide)
    · obtain ⟨z, hz, _⟩ := hj
      simp [C, pairEdgeWagonProbe] at hz
    · exact Or.inl rfl

/-- A designated supreme occurrence among F,G supplies a genuine p-edge
through the opposite endpoint. The actual pair edge itself cannot be the
designated supreme occurrence. Only local replacement pieces are used. -/
theorem twoLabel_wagon_bridge_of_pair_edge
    (hBound : D.LocalPieceSystemBound 2)
    (g : E) (F G : I ⊕ E) (p : P) (x y : V)
    (hxy : x ≠ y) (hFG : F ≠ G)
    (hgF : Sum.inr g ≠ F) (hgG : Sum.inr g ≠ G)
    (hxg : x ∈ D.edgeCarrier g) (hyg : y ∈ D.edgeCarrier g)
    (hxF : x ∈ D.carrier F) (hyG : y ∈ D.carrier G)
    (hFp : D.Meets F p) (hGp : D.Meets G p)
    (hMissing : ¬ (D.WagonVertex p x ∧ D.WagonVertex p y)) :
    (D.designated F ∧ D.Bridge F y p) ∨
      (D.designated G ∧ D.Bridge G x p) := by
  let C := D.pairEdgeWagonProbe g F G p x y hxy hFG hgF hgG hxg hyg hxF hyG hFp hGp
  have hAcc : C.Acceptable :=
    D.pairEdgeWagonProbe_acceptable g F G p x y hxy hFG hgF hgG hxg hyg hxF hyG hFp hGp hMissing
  have hOrd : C.twiceOrder ≤ 2 * 2 := by
    rw [D.pairEdgeWagonProbe_twiceOrder g F G p x y hxy hFG hgF hgG hxg hyg hxF hyG hFp hGp]
  obtain ⟨k, hk, hPieces⟩ := hBound 3 C hAcc hOrd
  fin_cases k
  · simp [C, pairEdgeWagonProbe, designated] at hk
  · have hne : C.label 2 ≠ C.label 1 := by
      simpa [C, pairEdgeWagonProbe] using hFG.symm
    have hPiece := hPieces 2 hne
    refine Or.inl ⟨?_, ?_⟩
    · simpa [C, pairEdgeWagonProbe] using hk
    · exact D.piece_mixed_bridge_reverse F y p
        (by simpa [C, pairEdgeWagonProbe, trainCyclicPred] using hPiece)
  · have hne : C.label 1 ≠ C.label 2 := by
      simpa [C, pairEdgeWagonProbe] using hFG
    have hPiece := hPieces 1 hne
    refine Or.inr ⟨?_, ?_⟩
    · simpa [C, pairEdgeWagonProbe] using hk
    · exact D.piece_mixed_bridge G x p
        (by simpa [C, pairEdgeWagonProbe, trainCyclicPred] using hPiece)

end StructuralRamsey.Girth.OrderOneData
