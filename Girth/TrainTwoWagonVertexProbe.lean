import Girth.TrainBigCycleOrderOneExtraction

set_option Elab.async false

/-!
# A copy meeting two wagons inherits their common vertex incidences

Let a designated copy meet two different wagons, and let a vertex belong
to both wagons. The three-occurrence cycle consisting of the copy and
one actual incident edge from each wagon has connectors wagon/vertex/wagon
and order two. Its only vertex position makes A2 and A3 automatic: in
particular, neither wagon connector has two vertex neighbors, so A2's
ambient nonedge clause cannot arise.

The copy is the only designated occurrence. Local supremeness therefore
supplies both mixed short pieces, giving an actual edge of the copy in
each prescribed wagon through the common vertex. This argument uses the
local piece bound directly and assumes no wagon linearity, edge-carrier
injectivity, ambient nonedge condition, or prior vertex membership in
the designated copy.

`OrderOneData` permits arbitrary copy carriers and copy-edge sets. The
bridge result needs no consistency hypothesis between them. The final
carrier-membership corollary explicitly assumes that the copy's edge
carriers are contained in its declared vertex carrier.
-/

namespace StructuralRamsey.Girth.OrderOneData

universe v
variable {V E I P : Type v} (D : OrderOneData V E I P)

/-- A genuine three-occurrence probe with a designated copy, two actual
edge labels and connector sequence wagon p / vertex x / wagon q. Distinct
parent labels force distinct actual edge labels. -/
def twoWagonVertexProbe
    (i : I) (e f : E) (p q : P) (x : V) (hpq : p ≠ q)
    (hip : D.Meets (.inl i) p) (hiq : D.Meets (.inl i) q)
    (hep : D.parent e = p) (hfq : D.parent f = q)
    (hxe : x ∈ D.edgeCarrier e) (hxf : x ∈ D.edgeCarrier f) :
    D.BigCycle 3 where
  length_ge_two := by omega
  label := ![Sum.inl i, Sum.inr e, Sum.inr f]
  connector := ![Sum.inr p, Sum.inl x, Sum.inr q]
  adjacent_ne := by
    have hef : e ≠ f := by
      intro h
      exact hpq (hep.symm.trans ((congrArg D.parent h).trans hfq))
    intro k
    fin_cases k
    · simp [cyclicSucc]
    · simpa [cyclicSucc] using
        (fun h : (Sum.inr e : I ⊕ E) = Sum.inr f => hef (Sum.inr.inj h))
    · simp [cyclicSucc]
  connector_injective := by
    intro k l h
    fin_cases k <;> fin_cases l <;> simp_all
  left_incident := by
    intro k
    fin_cases k
    · exact hip
    · exact hxe
    · exact ⟨f, rfl, hfq⟩
  right_incident := by
    intro k
    fin_cases k
    · exact ⟨e, rfl, hep⟩
    · exact hxf
    · exact hiq

/-- The two mixed occurrences and the pure copy occurrence have weights
one, one and two, giving order two. -/
theorem twoWagonVertexProbe_twiceOrder
    (i : I) (e f : E) (p q : P) (x : V) (hpq : p ≠ q)
    (hip : D.Meets (.inl i) p) (hiq : D.Meets (.inl i) q)
    (hep : D.parent e = p) (hfq : D.parent f = q)
    (hxe : x ∈ D.edgeCarrier e) (hxf : x ∈ D.edgeCarrier f) :
    (D.twoWagonVertexProbe i e f p q x hpq hip hiq hep hfq hxe hxf).twiceOrder = 4 := by
  simp [BigCycle.twiceOrder, connectorKind, twoWagonVertexProbe,
    Fin.sum_univ_three, cyclicSucc, twiceOccurrenceWeight]

/-- All three acceptability conditions hold literally. The sole vertex
position neighbors both wagon positions. Each wagon also neighbors the
other wagon, so the A2 ambient nonedge clause has impossible premises. -/
theorem twoWagonVertexProbe_acceptable
    (i : I) (e f : E) (p q : P) (x : V) (hpq : p ≠ q)
    (hip : D.Meets (.inl i) p) (hiq : D.Meets (.inl i) q)
    (hep : D.parent e = p) (hfq : D.parent f = q)
    (hxe : x ∈ D.edgeCarrier e) (hxf : x ∈ D.edgeCarrier f) :
    (D.twoWagonVertexProbe i e f p q x hpq hip hiq hep hfq hxe hxf).Acceptable := by
  let C := D.twoWagonVertexProbe i e f p q x hpq hip hiq hep hfq hxe hxf
  change C.Acceptable
  refine ⟨?_, ?_, ?_⟩
  · intro _
    exact ⟨(0 : Fin 3), trivial⟩
  · constructor
    · intro k w hk j hj
      obtain ⟨z, hz, _⟩ := hj
      fin_cases k <;> fin_cases j <;>
        simp_all [C, twoWagonVertexProbe, cyclicSucc, trainCyclicPred]
    · intro k w u v hk hPrev hNext _ _ _
      fin_cases k
      · simp [C, twoWagonVertexProbe, trainCyclicPred] at hPrev
      · simp [C, twoWagonVertexProbe] at hk
      · simp [C, twoWagonVertexProbe, cyclicSucc] at hNext
  · intro w _
    refine ⟨(1 : Fin 3), ?_⟩
    intro j hj
    fin_cases j
    · obtain ⟨z, hz, _⟩ := hj
      simp [C, twoWagonVertexProbe] at hz
    · exact Or.inl rfl
    · obtain ⟨z, hz, _⟩ := hj
      simp [C, twoWagonVertexProbe] at hz

/-- The only possible locally supreme occurrence is the designated copy.
Its replacements at the two physical edge occurrences have mixed boundaries,
and therefore give genuine bridges in both specified wagons. -/
theorem copy_bridges_of_two_wagon_vertex_probe
    (hBound : D.LocalPieceSystemBound 2)
    (i : I) (e f : E) (p q : P) (x : V) (hpq : p ≠ q)
    (hip : D.Meets (.inl i) p) (hiq : D.Meets (.inl i) q)
    (hep : D.parent e = p) (hfq : D.parent f = q)
    (hxe : x ∈ D.edgeCarrier e) (hxf : x ∈ D.edgeCarrier f) :
    D.Bridge (.inl i) x p ∧ D.Bridge (.inl i) x q := by
  let C := D.twoWagonVertexProbe i e f p q x hpq hip hiq hep hfq hxe hxf
  have hAcc : C.Acceptable :=
    D.twoWagonVertexProbe_acceptable i e f p q x hpq hip hiq hep hfq hxe hxf
  have hOrd : C.twiceOrder ≤ 2 * 2 := by
    rw [D.twoWagonVertexProbe_twiceOrder i e f p q x hpq hip hiq hep hfq hxe hxf]
  obtain ⟨k, hk, hPieces⟩ := hBound 3 C hAcc hOrd
  fin_cases k
  · have hne1 : C.label 1 ≠ C.label 0 := by
      simp [C, twoWagonVertexProbe]
    have hne2 : C.label 2 ≠ C.label 0 := by
      simp [C, twoWagonVertexProbe]
    have hPiece1 := hPieces 1 hne1
    have hPiece2 := hPieces 2 hne2
    constructor
    · exact D.piece_mixed_bridge_reverse (.inl i) x p
        (by simpa [C, twoWagonVertexProbe, trainCyclicPred] using hPiece1)
    · exact D.piece_mixed_bridge (.inl i) x q
        (by simpa [C, twoWagonVertexProbe, trainCyclicPred] using hPiece2)
  · have hFalse : False := by
      simpa [C, twoWagonVertexProbe, designated] using hk
    exact False.elim hFalse
  · have hFalse : False := by
      simpa [C, twoWagonVertexProbe, designated] using hk
    exact False.elim hFalse

/-- Any designated copy meeting two distinct wagons has actual edges in
both wagons through every common wagon vertex. There is no prior assumption
that the common vertex belongs to the designated copy. -/
theorem copy_bridges_of_common_wagon_vertex
    (hBound : D.LocalPieceSystemBound 2)
    (i : I) (p q : P) (x : V) (hpq : p ≠ q)
    (hip : D.Meets (.inl i) p) (hiq : D.Meets (.inl i) q)
    (hpx : D.WagonVertex p x) (hqx : D.WagonVertex q x) :
    D.Bridge (.inl i) x p ∧ D.Bridge (.inl i) x q := by
  obtain ⟨e, hep, hxe⟩ := hpx
  obtain ⟨f, hfq, hxf⟩ := hqx
  exact D.copy_bridges_of_two_wagon_vertex_probe hBound
    i e f p q x hpq hip hiq hep hfq hxe hxf

/-- Under the natural copy-edge carrier containment, the common wagon
vertex is also in the designated copy's declared vertex carrier. The
containment premise is explicit because raw `OrderOneData` does not impose
consistency between its copy carriers and copy-edge sets. -/
theorem copy_contains_common_wagon_vertex
    (hBound : D.LocalPieceSystemBound 2)
    (i : I)
    (hCarrier : ∀ e : E, e ∈ D.copyEdges i → D.edgeCarrier e ⊆ D.copyCarrier i)
    (p q : P) (x : V) (hpq : p ≠ q)
    (hip : D.Meets (.inl i) p) (hiq : D.Meets (.inl i) q)
    (hpx : D.WagonVertex p x) (hqx : D.WagonVertex q x) :
    x ∈ D.copyCarrier i := by
  obtain ⟨⟨e, he, _hep, hxe⟩, _⟩ :=
    D.copy_bridges_of_common_wagon_vertex hBound i p q x hpq hip hiq hpx hqx
  exact hCarrier e he hxe

end StructuralRamsey.Girth.OrderOneData
