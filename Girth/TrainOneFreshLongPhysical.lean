import Girth.TrainOneFreshLongComplete

/-!
# First-stage fresh long insertion needs NO source designated label

The witness's chosen supreme standard is an entire attached picture,
not necessarily a designated source-cycle occurrence. Thus the first
physical replacement is allowed to use arbitrary actual support
edges of that standard.

We isolate the physical-only long geometry: TWO original vertex
boundaries, two DISTINCT physical edges in the same wagon, actual
endpoint membership, and no ambient pair edge. It makes no reference
to D.edges (C.label source) for any original source index.

With one truly FRESH wagon, the verified arbitrary replacement library
constructs the entire globally legal cycle, verifies acceptability and
unchanged numerical order, and pulls EVERY later indexed supreme label
back to the original cycle. No labelled supreme target is assumed.

The remaining actual geometry is lifting this physical data from a
reduced long piece, then proving a strict decrease of the minimum
number of geometric owner cuts after the new occurrence is inserted.
No appendix.
-/

namespace StructuralRamsey.Girth.OrderOneData

universe v
variable {V E I P : Type v} (D : OrderOneData V E I P)

/-- The exact physical geometry required to replace one original
occurrence by two actual edges and one intervening fresh wagon.
Unlike LongValid, there is NO old designated source-label predicate. -/
def BigCycle.PhysicalLongGeometry
    {n : ℕ} (C : D.BigCycle n) (j : Fin n)
    (e : E) (w : P) (f : E) : Prop :=
  ∃ x y : V,
    C.connector (trainCyclicPred j) = Sum.inl x ∧
    C.connector j = Sum.inl y ∧
    e ≠ f ∧ D.parent e = w ∧ D.parent f = w ∧
    x ∈ D.edgeCarrier e ∧ y ∈ D.edgeCarrier f ∧
    ¬ D.PairEdge x y

/-- A labelled LongValid piece implies the weaker PHYSICAL geometry.
The converse is intentionally not claimed: the original cycle
may have no designated label naming the chosen source standard. -/
theorem BigCycle.physicalLongGeometry_of_longValid
    {n : ℕ} (C : D.BigCycle n)
    (source j : Fin n) (e : E) (w : P) (f : E)
    (hLong : C.LongValid D source j e w f) :
    C.PhysicalLongGeometry D j e w f := by
  obtain ⟨x, y, hLeft, hRight, _hE, _hF,
    hNe, hParE, hParF, hx, hy, hNoPair⟩ := hLong
  exact ⟨x, y, hLeft, hRight,
    hNe, hParE, hParF, hx, hy, hNoPair⟩

/-- The physical-only data already supplies every local incidence
of a one-long expanded cyclic word, with all other entries kept. -/
theorem BigCycle.onlyLongPieces_physical_incidence
    {n : ℕ} (C : D.BigCycle n)
    (j : Fin n) (e : E) (w : P) (f : E)
    (hPhysical : C.PhysicalLongGeometry D j e w f) :
    C.LocalPieceIncidence D (C.onlyLongPieces D j e w f) := by
  obtain ⟨x, y, hLeft, hRight, hNe,
    hParE, hParF, hx, hy, _hNoPair⟩ := hPhysical
  intro k
  by_cases hk : k = j
  · subst k
    simp only [BigCycle.onlyLongPieces, if_pos rfl]
    change e ≠ f ∧
      D.Incident (.inr e) (C.connector (trainCyclicPred j)) ∧
      D.parent e = w ∧ D.parent f = w ∧
      D.Incident (.inr f) (C.connector j)
    refine ⟨hNe, ?_, hParE, hParF, ?_⟩
    · rw [hLeft]
      exact hx
    · rw [hRight]
      exact hy
  · simp [BigCycle.onlyLongPieces, hk]

/-- The actual physical geometry supplies both old vertex contacts,
the common wagon contacts, and its essential no-pair-edge clause. -/
theorem BigCycle.onlyLongPieces_physical_A2Geometry
    {n : ℕ} (C : D.BigCycle n)
    (j : Fin n) (e : E) (w : P) (f : E)
    (hPhysical : C.PhysicalLongGeometry D j e w f) :
    C.LocalLongA2Geometry D (C.onlyLongPieces D j e w f) := by
  obtain ⟨x, y, hLeft, hRight, _hNe,
    hParE, hParF, hx, hy, hNoPair⟩ := hPhysical
  intro k a b p hp
  by_cases hk : k = j
  · subst k
    have hEq : e = a ∧ w = p ∧ f = b := by
      simpa [BigCycle.onlyLongPieces] using hp
    rcases hEq with ⟨rfl, rfl, rfl⟩
    exact ⟨x, y, hLeft, hRight,
      ⟨e, hParE, hx⟩, ⟨f, hParF, hy⟩, hNoPair⟩
  · simp [BigCycle.onlyLongPieces, hk] at hp

/-- One physical-only genuine long piece and fresh wagon suffice for
the ACTUAL globally legal output and indexed supreme pullback; the
old source-label membership required by LongValid is NOT assumed. -/
theorem BigCycle.oneFreshPhysicalLong_complete_of_three_le
    {n : ℕ} (C : D.BigCycle n)
    (hAccept : C.Acceptable) (hLinear : D.LinearPretrain)
    (hn : 3 ≤ n)
    (j : Fin n) (e : E) (w : P) (f : E)
    (hPhysical : C.PhysicalLongGeometry D j e w f)
    (hFresh : ∀ t : Fin n, C.connector t ≠ Sum.inr w) :
    ∃ m : ℕ, ∃ H : D.BigCycle m,
      List.ofFn (fun k : Fin m => (H.label k, H.connector k)) =
        C.resultWord D (C.onlyLongPieces D j e w f) ∧
      H.Acceptable ∧ H.twiceOrder = C.twiceOrder ∧
      (∀ kH : Fin m, H.HasSupremeAt D kH →
        ∃ kC : Fin n, C.label kC = H.label kH ∧
          C.HasSupremeAt D kC) := by
  exact C.arbitrary_replacement_complete_of_three_le
    D hAccept hLinear hn
    (C.onlyLongPieces D j e w f)
    (C.onlyLongPieces_physical_incidence D j e w f hPhysical)
    (C.onlyLongPieces_physical_A2Geometry D j e w f hPhysical)
    (C.onlyLongPieces_fresh D j e w f hFresh)

end StructuralRamsey.Girth.OrderOneData
