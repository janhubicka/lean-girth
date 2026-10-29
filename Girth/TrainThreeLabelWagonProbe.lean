import Girth.TrainTwoCopyLocalSymmetry

set_option Elab.async false

/-!
# Two vertex boundaries force a common wagon

Every short or long piece between two vertices places the vertices in one
actual wagon. Two designated copies through a pair therefore force a common
wagon under the order-two local bound.

A related three-occurrence probe consists of a designated copy Q through
x,y and labels F,G meeting one wagon p at their respective vertex boundaries.
If no wagon contains x,y, there is no pair edge, making the probe acceptable.
Supremeness at Q gives two p-bridges; supremeness at F or G gives a piece
between x,y. Both alternatives contradict the absence of a common wagon.

These results use only local pieces. No source linearity, copy-edge carrier
consistency, or simultaneous global replacement condition is assumed.
-/

namespace StructuralRamsey.Girth.OrderOneData

universe v
variable {V E I P : Type v} (D : OrderOneData V E I P)

/-- A short or long piece with two vertex boundaries supplies a genuine
wagon containing both vertices. The selected label need not be designated. -/
theorem piece_vertices_common_wagon
    (a : I ⊕ E) (x y : V)
    (h : D.ShortPiece a (.inl x) (.inl y) ∨
      D.LongPiece a (.inl x) (.inl y)) :
    ∃ p : P, D.WagonVertex p x ∧ D.WagonVertex p y := by
  rcases h with ⟨e, _he, hxe, hye⟩ |
    ⟨u, v, p, e, f, hu, hv, _he, _hf, _hef, hep, hfp, hue, hvf, _⟩
  · exact ⟨D.parent e, ⟨e, rfl, hxe⟩, ⟨e, rfl, hye⟩⟩
  · have hux : u = x := (Sum.inl.inj hu).symm
    have hvy : v = y := (Sum.inl.inj hv).symm
    subst u
    subst v
    exact ⟨p, ⟨e, hep, hue⟩, ⟨f, hfp, hvf⟩⟩

/-- Two distinct designated copies through a distinct vertex pair force
some common wagon. No linearity or ambient nonedge hypothesis is needed. -/
theorem common_wagon_of_two_copy_vertex_pair
    (hBound : D.LocalPieceSystemBound 2)
    (i j : I) (x y : V) (hij : i ≠ j) (hxy : x ≠ y)
    (hix : x ∈ D.copyCarrier i) (hiy : y ∈ D.copyCarrier i)
    (hjx : x ∈ D.copyCarrier j) (hjy : y ∈ D.copyCarrier j) :
    ∃ p : P, D.WagonVertex p x ∧ D.WagonVertex p y := by
  exact D.piece_vertices_common_wagon (.inl i) x y
    (D.twoVertexTwoCopyCycle_both_local_pieces hBound
      i j x y hij hxy hix hiy hjx hjy).1

/-- The literal three-occurrence cycle Q x F p G y, where Q is designated
and the other two labels are arbitrary. -/
def threeLabelWagonProbe
    (i : I) (F G : I ⊕ E) (p : P) (x y : V)
    (hxy : x ≠ y) (hiF : Sum.inl i ≠ F) (hiG : Sum.inl i ≠ G) (hFG : F ≠ G)
    (hix : x ∈ D.copyCarrier i) (hiy : y ∈ D.copyCarrier i)
    (hxF : x ∈ D.carrier F) (hyG : y ∈ D.carrier G)
    (hFp : D.Meets F p) (hGp : D.Meets G p) : D.BigCycle 3 where
  length_ge_two := by omega
  label := ![Sum.inl i, F, G]
  connector := ![Sum.inl x, Sum.inr p, Sum.inl y]
  adjacent_ne := by
    intro k
    fin_cases k
    · simpa [cyclicSucc] using hiF
    · simpa [cyclicSucc] using hFG
    · simpa [cyclicSucc] using hiG.symm
  connector_injective := by
    intro k l h
    fin_cases k <;> fin_cases l <;> simp_all
  left_incident := by
    intro k
    fin_cases k
    · exact hix
    · exact hFp
    · exact hyG
  right_incident := by
    intro k
    fin_cases k
    · exact hxF
    · exact hGp
    · exact hiy

/-- The three-occurrence vertex/wagon/vertex probe has order two. -/
theorem threeLabelWagonProbe_twiceOrder
    (i : I) (F G : I ⊕ E) (p : P) (x y : V)
    (hxy : x ≠ y) (hiF : Sum.inl i ≠ F) (hiG : Sum.inl i ≠ G) (hFG : F ≠ G)
    (hix : x ∈ D.copyCarrier i) (hiy : y ∈ D.copyCarrier i)
    (hxF : x ∈ D.carrier F) (hyG : y ∈ D.carrier G)
    (hFp : D.Meets F p) (hGp : D.Meets G p) :
    (D.threeLabelWagonProbe i F G p x y hxy hiF hiG hFG hix hiy hxF hyG hFp hGp).twiceOrder = 4 := by
  simp [BigCycle.twiceOrder, connectorKind, threeLabelWagonProbe,
    Fin.sum_univ_three, cyclicSucc, twiceOccurrenceWeight]

/-- A2 uses the actual ambient no-pair guard. A3 is automatic because the
two vertex positions are consecutive around a three-occurrence cycle. -/
theorem threeLabelWagonProbe_acceptable
    (i : I) (F G : I ⊕ E) (p : P) (x y : V)
    (hxy : x ≠ y) (hiF : Sum.inl i ≠ F) (hiG : Sum.inl i ≠ G) (hFG : F ≠ G)
    (hix : x ∈ D.copyCarrier i) (hiy : y ∈ D.copyCarrier i)
    (hxF : x ∈ D.carrier F) (hyG : y ∈ D.carrier G)
    (hFp : D.Meets F p) (hGp : D.Meets G p)
    (hNoPair : ¬ D.PairEdge x y) :
    (D.threeLabelWagonProbe i F G p x y hxy hiF hiG hFG hix hiy hxF hyG hFp hGp).Acceptable := by
  let C := D.threeLabelWagonProbe i F G p x y hxy hiF hiG hFG hix hiy hxF hyG hFp hGp
  change C.Acceptable
  refine ⟨?_, ?_, ?_⟩
  · intro ht
    have hfour : C.twiceOrder = 4 :=
      D.threeLabelWagonProbe_twiceOrder i F G p x y hxy hiF hiG hFG hix hiy hxF hyG hFp hGp
    have heq : (4 : ℕ) = 2 := hfour.symm.trans ht
    exact False.elim ((by decide : (4 : ℕ) ≠ 2) heq)
  · constructor
    · intro k w hk j hj
      fin_cases k
      · simp [C, threeLabelWagonProbe] at hk
      · fin_cases j
        · exact Or.inl (by decide)
        · obtain ⟨z, hz, _⟩ := hj
          simp [C, threeLabelWagonProbe] at hz
        · exact Or.inr (by decide)
      · simp [C, threeLabelWagonProbe] at hk
    · intro k w vx vy hk hPrev hNext _ _ _
      fin_cases k
      · simp [C, threeLabelWagonProbe] at hk
      · have hx : vx = x := by
          simpa [C, threeLabelWagonProbe, trainCyclicPred] using hPrev.symm
        have hy : vy = y := by
          simpa [C, threeLabelWagonProbe, cyclicSucc] using hNext.symm
        subst vx
        subst vy
        exact hNoPair
      · simp [C, threeLabelWagonProbe] at hk
  · intro w _
    refine ⟨(2 : Fin 3), ?_⟩
    intro j hj
    fin_cases j
    · exact Or.inr (by decide)
    · obtain ⟨z, hz, _⟩ := hj
      simp [C, threeLabelWagonProbe] at hz
    · exact Or.inl rfl

/-- A designated copy through x,y and two other labels meeting one wagon
at those boundaries force some wagon through x,y. Local supremeness at the
designated hub gives two mixed bridges; at either other label it gives a
piece with two vertex boundaries. -/
theorem common_wagon_of_three_label_wagon_probe
    (hBound : D.LocalPieceSystemBound 2)
    (i : I) (F G : I ⊕ E) (p : P) (x y : V)
    (hxy : x ≠ y) (hiF : Sum.inl i ≠ F) (hiG : Sum.inl i ≠ G) (hFG : F ≠ G)
    (hix : x ∈ D.copyCarrier i) (hiy : y ∈ D.copyCarrier i)
    (hxF : x ∈ D.carrier F) (hyG : y ∈ D.carrier G)
    (hFp : D.Meets F p) (hGp : D.Meets G p) :
    ∃ r : P, D.WagonVertex r x ∧ D.WagonVertex r y := by
  classical
  by_contra hNone
  have hNoPair : ¬ D.PairEdge x y := by
    rintro ⟨g, hxg, hyg⟩
    exact hNone ⟨D.parent g, ⟨g, rfl, hxg⟩, ⟨g, rfl, hyg⟩⟩
  let C := D.threeLabelWagonProbe i F G p x y hxy hiF hiG hFG hix hiy hxF hyG hFp hGp
  have hAcc : C.Acceptable :=
    D.threeLabelWagonProbe_acceptable i F G p x y hxy hiF hiG hFG hix hiy hxF hyG hFp hGp hNoPair
  have hOrd : C.twiceOrder ≤ 2 * 2 := by
    rw [D.threeLabelWagonProbe_twiceOrder i F G p x y hxy hiF hiG hFG hix hiy hxF hyG hFp hGp]
  obtain ⟨k, _hk, hPieces⟩ := hBound 3 C hAcc hOrd
  fin_cases k
  · have hne1 : C.label 1 ≠ C.label 0 := by
      simpa [C, threeLabelWagonProbe] using hiF.symm
    have hne2 : C.label 2 ≠ C.label 0 := by
      simpa [C, threeLabelWagonProbe] using hiG.symm
    have hFirst := hPieces 1 hne1
    have hSecond := hPieces 2 hne2
    have hxBridge : D.Bridge (.inl i) x p :=
      D.piece_mixed_bridge (.inl i) x p
        (by simpa [C, threeLabelWagonProbe, trainCyclicPred] using hFirst)
    have hyBridge : D.Bridge (.inl i) y p :=
      D.piece_mixed_bridge_reverse (.inl i) y p
        (by simpa [C, threeLabelWagonProbe, trainCyclicPred] using hSecond)
    obtain ⟨a, _ha, hap, hxa⟩ := hxBridge
    obtain ⟨b, _hb, hbp, hyb⟩ := hyBridge
    exact hNone ⟨p, ⟨a, hap, hxa⟩, ⟨b, hbp, hyb⟩⟩
  · have hne : C.label 0 ≠ C.label 1 := by
      simpa [C, threeLabelWagonProbe] using hiF
    have hPiece := hPieces 0 hne
    obtain ⟨r, hry, hrx⟩ := D.piece_vertices_common_wagon F y x
      (by simpa [C, threeLabelWagonProbe, trainCyclicPred] using hPiece)
    exact hNone ⟨r, hrx, hry⟩
  · have hne : C.label 0 ≠ C.label 2 := by
      simpa [C, threeLabelWagonProbe] using hiG
    have hPiece := hPieces 0 hne
    obtain ⟨r, hry, hrx⟩ := D.piece_vertices_common_wagon G y x
      (by simpa [C, threeLabelWagonProbe, trainCyclicPred] using hPiece)
    exact hNone ⟨r, hrx, hry⟩

end StructuralRamsey.Girth.OrderOneData
