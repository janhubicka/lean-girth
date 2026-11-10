import Girth.ACopyStarChartAdapter

set_option autoImplicit false

/-!
# Irreducible chart coverage is intrinsic to a free relational star

An irreducible vertex set in the genuine free relational union lies in
the core or in ONE source chart. This is not an additional hypothesis:
it follows from the quotient's exact source/core intersections and the
definition of the relation union, even for arbitrarily many standards.

Key argument: choose a vertex outside the core. Every relation tuple
containing it comes from its unique standard; irreducibility then puts
every other point in that standard. Nullary relations do not affect the
argument, and unsupported chart points remain present.

Combining with induced-link relational embeddings gives an actual
CoversIrreducibles proof, eliminating that extra field from the
conditional A-copy support adapter.
-/

namespace StructuralRamsey.Girth.ACopyStarChartCoverage

open StructuralRamsey.RelStructure
open ACopyLayeredStar ACopyDecoratedStar
open ACopyDecoratedRelationalStar ACopyStarChartAdapter
open ACopyChartCoverage ACopyRelationalUnion

universe u v

variable {L : RelLanguage.{u}}
variable {CN I K PC : Type v} {SN SH PS PQ : I → Type v}
variable {N : Diagram CN I SN SH}
variable (D : Data N K PC PS PQ)

/-- Every irreducible set in the free relation union is wholly contained
in the core or in one genuine source standard. No finiteness or
A-linearity is needed. -/
theorem irreducible_set_core_or_source
    (C : RelStructure L (Quotient D.coreEq))
    (S : (i : I) → RelStructure L (Quotient (D.sourceEq i)))
    (T : Set D.Point)
    (hT : ((relationalUnion D C S).induce T).Irreducible) :
    T ⊆ D.coreImage ∨ ∃ i : I, T ⊆ D.sourceImage i := by
  classical
  by_cases hAllCore : T ⊆ D.coreImage
  · exact Or.inl hAllCore
  · right
    obtain ⟨x, hxT, hxNotCore⟩ := Set.not_subset.mp hAllCore
    rcases D.point_has_record x with ⟨c, hc⟩ | ⟨i, p, hp⟩
    · exact False.elim (hxNotCore ⟨c, hc⟩)
    · have hxSource : x ∈ D.sourceImage i := ⟨p, hp⟩
      refine ⟨i, ?_⟩
      intro y hyT
      by_cases hyx : y = x
      · simpa only [hyx] using hxSource
      · have hNe : (⟨x, hxT⟩ : T) ≠ ⟨y, hyT⟩ := by
          intro h
          apply hyx
          exact (congrArg Subtype.val h).symm
        obtain ⟨sym, z, kx, ky, hRel, hX, hY⟩ := hT hNe
        have hxCoord : (z kx).val = x := congrArg Subtype.val hX
        have hyCoord : (z ky).val = y := congrArg Subtype.val hY
        change UnionRel C S D.coreMap D.sourceMap sym
          (fun k => (z k).val) at hRel
        rcases hRel with ⟨t, ht, _⟩ | ⟨j, t, ht, _⟩
        · have hCore : x ∈ D.coreImage := by
            have hRange : x ∈ Set.range D.coreMap :=
              ⟨t kx, (ht kx).trans hxCoord⟩
            rw [core_range D] at hRange
            exact hRange
          exact False.elim (hxNotCore hCore)
        · have hxJ : x ∈ D.sourceImage j := by
            have hRange : x ∈ Set.range (D.sourceMap j) :=
              ⟨t kx, (ht kx).trans hxCoord⟩
            rw [source_range D j] at hRange
            exact hRange
          have hyJ : y ∈ D.sourceImage j := by
            have hRange : y ∈ Set.range (D.sourceMap j) :=
              ⟨t ky, (ht ky).trans hyCoord⟩
            rw [source_range D j] at hRange
            exact hRange
          by_cases hji : j = i
          · subst j
            exact hyJ
          · have hShared : x ∈ D.sharedImage i ∩ D.sharedImage j := by
              rw [← D.distinct_sourceImage_inter i j (Ne.symm hji)]
              exact ⟨hxSource, hxJ⟩
            obtain ⟨q, hq⟩ := hShared.1
            exact False.elim (hxNotCore ⟨D.alpha i q, hq⟩)

/-- The actual family of induced relational star chart embeddings covers
all irreducible substructures. It is unnecessary to assume this field
separately in a faithful relational A-copy realization. -/
theorem starChartCoversIrreducibles
    (C : RelStructure L (Quotient D.coreEq))
    (S : (i : I) → RelStructure L (Quotient (D.sourceEq i)))
    (Q : (i : I) → RelStructure L (PQ i))
    (embedCore : (i : I) → Embedding (Q i) C)
    (embedSource : (i : I) → Embedding (Q i) (S i))
    (hCoreCoord : ∀ i (p : PQ i),
      embedCore i p = Quotient.mk D.coreEq (D.alpha i p))
    (hSourceCoord : ∀ i (p : PQ i),
      embedSource i p = Quotient.mk (D.sourceEq i) (D.beta i p)) :
    CoversIrreducibles
      (chartEmbedding D C S Q embedCore embedSource hCoreCoord hSourceCoord) := by
  intro T hT
  rcases irreducible_set_core_or_source D C S T hT with hCore | ⟨i, hi⟩
  · refine ⟨none, ?_⟩
    change T ⊆ Set.range D.coreMap
    rw [core_range D]
    exact hCore
  · refine ⟨some i, ?_⟩
    change T ⊆ Set.range (D.sourceMap i)
    rw [source_range D i]
    exact hi

end StructuralRamsey.Girth.ACopyStarChartCoverage
