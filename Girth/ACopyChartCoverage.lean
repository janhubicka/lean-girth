import Girth.Support

/-! # Exact physical support from embedded relational chart coverage

These statements concern honest induced embeddings of full relational charts.
Irreducible coverage gives every actual copy a chartwise occurrence, and the
quotient identifying occurrences with equal ambient carriers is exactly the
actual support. No rigidity of the physical type is required.

This does not construct the chart embeddings from a binary overlap diagram,
nor prove that a pre-existing raw node equivalence identifies exactly those
occurrences. In particular, completeness of the node domains of gluing links
remains a separate obligation.
-/

namespace StructuralRamsey.Girth.ACopyChartCoverage

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {I U W : Type v} {V : I → Type v}
variable {A : RelStructure L U} {H : RelStructure L W}
variable {C : ∀ i, RelStructure L (V i)}

/-- Every induced irreducible substructure is contained in one full embedded
chart. The chart index remains a label, even if two chart images agree. -/
def CoversIrreducibles (chart : ∀ i, Embedding (C i) H) : Prop :=
  ∀ S : Set W, (H.induce S).Irreducible →
    ∃ i, S ⊆ copyCarrier (chart i)

/-- An irreducible ambient copy factors through a genuinely embedded chart.
The assertion concerns embeddings, not just a cover of its vertices. -/
theorem factors_through_chart
    (chart : ∀ i, Embedding (C i) H)
    (hCover : CoversIrreducibles chart) (hA : A.Irreducible)
    (a : Embedding A H) :
    ∃ i, ∃ b : Embedding A (C i), (chart i).comp b = a := by
  classical
  obtain ⟨i, hi⟩ := hCover (copyCarrier a) (hA.range_embedding a)
  have hInto : ∀ x : U, ∃ y : V i, a x = chart i y := by
    intro x
    obtain ⟨y, hy⟩ := hi ⟨x, rfl⟩
    exact ⟨y, hy.symm⟩
  refine ⟨i, a.factorThroughRange (chart i) hInto, ?_⟩
  apply Embedding.ext
  intro x
  exact (Classical.choose_spec (hInto x)).symm

/-- All recorded copies inside all labelled charts, before duplicate
occurrences are identified. -/
abbrev Occurrence (A : RelStructure L U) (C : ∀ i, RelStructure L (V i)) :=
  (i : I) × Embedding A (C i)

/-- The ambient point carrier of a recorded occurrence. -/
def occurrenceCarrier (chart : ∀ i, Embedding (C i) H)
    (o : Occurrence A C) : Set W :=
  copyCarrier ((chart o.1).comp o.2)

/-- Chart coverage is enough for exact actual support; this needs neither
finiteness nor rigidity of the irreducible physical type. -/
theorem occurrenceCarriers_eq_supportCopies
    (chart : ∀ i, Embedding (C i) H)
    (hCover : CoversIrreducibles chart) (hA : A.Irreducible) :
    Set.range (occurrenceCarrier (A := A) chart) = supportCopies A H := by
  apply Set.Subset.antisymm
  · rintro S ⟨o, rfl⟩
    exact ⟨(chart o.1).comp o.2, rfl⟩
  · rintro S ⟨a, rfl⟩
    obtain ⟨i, b, hab⟩ := factors_through_chart chart hCover hA a
    refine ⟨⟨i, b⟩, ?_⟩
    change copyCarrier ((chart i).comp b) = copyCarrier a
    rw [hab]

/-- Only recorded physical occurrences are quotiented here. Chart labels
themselves are not identified. -/
def occurrenceSetoid (chart : ∀ i, Embedding (C i) H) :
    Setoid (Occurrence A C) :=
  Setoid.ker (occurrenceCarrier chart)

theorem occurrence_quotient_eq_iff
    (chart : ∀ i, Embedding (C i) H) (o p : Occurrence A C) :
    Quotient.mk (occurrenceSetoid chart) o =
        Quotient.mk (occurrenceSetoid chart) p ↔
      occurrenceCarrier chart o = occurrenceCarrier chart p :=
  Quotient.eq

/-- Identifying two chartwise physical occurrences exactly when their
ambient carriers agree gives a bijection with all actual image copies. -/
noncomputable def occurrenceQuotientEquivSupport
    (chart : ∀ i, Embedding (C i) H)
    (hCover : CoversIrreducibles chart) (hA : A.Irreducible) :
    Quotient (occurrenceSetoid (A := A) chart) ≃ supportCopies A H :=
  (Setoid.quotientKerEquivRange (occurrenceCarrier chart)).trans
    (Set.equivOfEq (occurrenceCarriers_eq_supportCopies chart hCover hA))

theorem occurrenceQuotientEquivSupport_mk
    (chart : ∀ i, Embedding (C i) H)
    (hCover : CoversIrreducibles chart) (hA : A.Irreducible)
    (o : Occurrence A C) :
    (occurrenceQuotientEquivSupport chart hCover hA
      (Quotient.mk (occurrenceSetoid chart) o)).val =
        occurrenceCarrier chart o := rfl

/-- For copies of one finite irreducible chart type, every actual copy
equals a designated chart as an image. No injectivity of chart labels or
equality of their embedding maps is asserted. -/
theorem actual_copy_eq_chart
    {B : RelStructure L U} [Finite U]
    (chart : I → Embedding B H)
    (hCover : CoversIrreducibles chart) (hB : B.Irreducible)
    (b : Embedding B H) :
    ∃ i, SameCopy b (chart i) := by
  obtain ⟨i, hi⟩ := hCover (copyCarrier b) (hB.range_embedding b)
  refine ⟨i, sameCopy_of_range_subset b (chart i) ?_⟩
  intro x
  obtain ⟨y, hy⟩ := hi ⟨x, rfl⟩
  exact ⟨y, hy.symm⟩

/-- Coverage is preserved by an actual induced free amalgam. The conclusion
retains the two original indexed chart families, transported through their
side embeddings; no new charts or identifications of labels are introduced. -/
theorem coversIrreducibles_freeAmalgam
    {J D X Y : Type v} {V' : J → Type v}
    {O : RelStructure L D} {H₁ : RelStructure L X}
    {H₂ : RelStructure L Y} {C' : ∀ j, RelStructure L (V' j)}
    {s₁ : Embedding O H₁} {s₂ : Embedding O H₂}
    {e₁ : Embedding H₁ H} {e₂ : Embedding H₂ H}
    (hFree : IsFreeAmalgam s₁ s₂ e₁ e₂)
    (chart₁ : ∀ i, Embedding (C i) H₁)
    (chart₂ : ∀ j, Embedding (C' j) H₂)
    (hCover₁ : CoversIrreducibles chart₁)
    (hCover₂ : CoversIrreducibles chart₂)
    (S : Set W) (hS : (H.induce S).Irreducible) :
    (∃ i, S ⊆ copyCarrier (e₁.comp (chart₁ i))) ∨
      (∃ j, S ⊆ copyCarrier (e₂.comp (chart₂ j))) := by
  classical
  let inc := RelStructure.inclusion H S
  rcases hFree.irreducible_side S hS with hLeft | hRight
  · let a := inc.factorThroughRange e₁ hLeft
    obtain ⟨i, b, hb⟩ := factors_through_chart chart₁ hCover₁ hS a
    refine Or.inl ⟨i, ?_⟩
    intro x hx
    let z : S := ⟨x, hx⟩
    refine ⟨b z, ?_⟩
    have hz : chart₁ i (b z) = a z := congrArg (fun f => f z) hb
    change e₁ (chart₁ i (b z)) = x
    rw [hz]
    exact (Classical.choose_spec (hLeft z)).symm
  · let a := inc.factorThroughRange e₂ hRight
    obtain ⟨j, b, hb⟩ := factors_through_chart chart₂ hCover₂ hS a
    refine Or.inr ⟨j, ?_⟩
    intro x hx
    let z : S := ⟨x, hx⟩
    refine ⟨b z, ?_⟩
    have hz : chart₂ j (b z) = a z := congrArg (fun f => f z) hb
    change e₂ (chart₂ j (b z)) = x
    rw [hz]
    exact (Classical.choose_spec (hRight z)).symm

end StructuralRamsey.Girth.ACopyChartCoverage
