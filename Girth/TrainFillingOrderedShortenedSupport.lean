import Girth.TrainFillingIndexedColourOrder

set_option autoImplicit false

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe v

/-- The increasing enumeration of a coloured edge also embeds the full
order expansion used by the unrestricted shorter-train assertion. -/
def colouredOrderedEdgeEmbedding_withOrder
    {I V : Type v} [LinearOrder V]
    (k : ℕ) (E : Set (Set V))
    (sourceColour : Fin k → I) (targetColour : V → I)
    (ι : Fin k ↪ V) (hι : StrictMono ι)
    (hEdge : Set.range (ι : Fin k → V) ∈ E)
    (hColour : ∀ x : Fin k, targetColour (ι x) = sourceColour x) :
    Embedding (colouredOrderedEdgeSource k sourceColour).ordered
      (colouredOrderedEdgeTarget k E targetColour).ordered := by
  let f := colouredOrderedEdgeEmbedding k E sourceColour targetColour
    ι hEdge hColour (fun _ _ _ => hι.lt_iff_lt.symm)
  refine ⟨f, f.injective, ?_⟩
  intro R x
  cases R with
  | inl R => exact f.map_rel_iff R x
  | inr R => exact hι.lt_iff_lt

namespace IndexedPrivateChoice

variable {C V P X I : Type v} (U : C → PrivateWagonInput V P X)
variable [LinearOrder C] [LinearOrder V] [Fintype V]
variable [LinearOrder P] [LinearOrder X] [LinearOrder I]

/-- The constructed shorter target with the additional full relational
order that appears in the unrestricted induction hypothesis. -/
noncomputable def orderedShortenedTarget {k : ℕ}
    (oldColour : V → I) (templateColour : X → I) :
    RelStructure (colouredOrderedEdgeLanguage I k).withOrder (Vertex U) :=
  letI := colouredChoiceInsertionOrder U oldColour templateColour
  (actualContractedColouredM U oldColour templateColour).ordered

theorem orderedShortenedTarget_extendsOrder {k : ℕ}
    (oldColour : V → I) (templateColour : X → I) :
    @ExtendsOrder (colouredOrderedEdgeLanguage I k) (Vertex U)
      (orderedShortenedTarget U oldColour templateColour)
      (colouredChoiceInsertionOrder U oldColour templateColour).toLT := by
  intro x y hxy
  exact hxy

/-- The ordered embedding of the literal whole-template placement on a
particular contracted first wagon. -/
noncomputable def orderedShortenedEdgeEmbedding
    {k : ℕ}
    (enumerateX : Fin k ≃ X) (hEnumerate : StrictMono enumerateX)
    (oldColour : V → I) (templateColour : X → I)
    (hColour : ∀ c : C, ∀ p : P,
      ∀ z : {v : V // v ∈ (U c).oldCarrier p},
        oldColour z.1 = templateColour ((U c).coordinate p z))
    (hCoordinate : ∀ c : C, ∀ p : P, StrictMono ((U c).coordinate p))
    (hXBlocks : ∀ x y : X, templateColour x ≠ templateColour y →
      x < y → templateColour x < templateColour y)
    (cp : C × P) :
    Embedding (colouredOrderedEdgeSource k
        (fun i => templateColour (enumerateX i))).ordered
      (orderedShortenedTarget U oldColour templateColour) := by
  letI := colouredChoiceInsertionOrder U oldColour templateColour
  let ι := contractedEnumerationOfEquiv U enumerateX cp
  have hι : StrictMono ι := by
    intro i j hij
    exact colouredChoicePlace_lt U oldColour templateColour
      hColour hCoordinate hXBlocks cp (hEnumerate hij)
  have hEdge : Set.range (ι : Fin k → Vertex U) ∈
      Set.range (contractedCarrier U) := by
    rw [contractedEnumerationOfEquiv_range U enumerateX cp]
    exact ⟨cp, rfl⟩
  have hCol (i : Fin k) : contractedVertexColour U oldColour
      templateColour (ι i) = templateColour (enumerateX i) :=
    contractedVertexColour_place U oldColour templateColour hColour
      cp.1 cp.2 (enumerateX i)
  exact colouredOrderedEdgeEmbedding_withOrder k (Set.range (contractedCarrier U))
    (fun i => templateColour (enumerateX i)) (contractedVertexColour U oldColour templateColour)
    ι hι hEdge hCol

@[simp] theorem orderedShortenedEdgeEmbedding_apply
    {k : ℕ}
    (enumerateX : Fin k ≃ X) (hEnumerate : StrictMono enumerateX)
    (oldColour : V → I) (templateColour : X → I)
    (hColour : ∀ c : C, ∀ p : P,
      ∀ z : {v : V // v ∈ (U c).oldCarrier p},
        oldColour z.1 = templateColour ((U c).coordinate p z))
    (hCoordinate : ∀ c : C, ∀ p : P, StrictMono ((U c).coordinate p))
    (hXBlocks : ∀ x y : X, templateColour x ≠ templateColour y →
      x < y → templateColour x < templateColour y)
    (cp : C × P) (x : X) :
    orderedShortenedEdgeEmbedding U enumerateX hEnumerate oldColour
      templateColour hColour hCoordinate hXBlocks cp (ULift.up (enumerateX.symm x)) =
      tagVertex U cp.1 ((U cp.1).place cp.2 x) := by
  change tagVertex U cp.1 ((U cp.1).place cp.2 (enumerateX (enumerateX.symm x))) = _
  rw [Equiv.apply_symm_apply]

/-- Every entire private first-wagon placement lifts to the full-order
edge type. The added order keeps the same complete edge support. -/
theorem orderedShortenedTarget_support_eq
    {k : ℕ}
    (enumerateX : Fin k ≃ X) (hEnumerate : StrictMono enumerateX)
    (oldColour : V → I) (templateColour : X → I)
    (hColour : ∀ c : C, ∀ p : P,
      ∀ z : {v : V // v ∈ (U c).oldCarrier p},
        oldColour z.1 = templateColour ((U c).coordinate p z))
    (hCoordinate : ∀ c : C, ∀ p : P, StrictMono ((U c).coordinate p))
    (hXBlocks : ∀ x y : X, templateColour x ≠ templateColour y →
      x < y → templateColour x < templateColour y) :
    supportCopies (colouredOrderedEdgeSource k
        (fun i => templateColour (enumerateX i))).ordered
      (orderedShortenedTarget U oldColour templateColour) =
      Set.range (contractedCarrier U) := by
  letI := colouredChoiceInsertionOrder U oldColour templateColour
  apply Set.Subset.antisymm
  · rintro e ⟨f, rfl⟩
    let f₀ : Embedding (colouredOrderedEdgeSource k
        (fun i => templateColour (enumerateX i)))
        (actualContractedColouredM U oldColour templateColour) :=
      ⟨f, f.injective, fun R t => f.map_rel_iff (.inl R) t⟩
    exact colouredOrderedEdgeEmbedding_carrier_mem k
      (Set.range (contractedCarrier U))
      (fun i => templateColour (enumerateX i))
      (contractedVertexColour U oldColour templateColour) f₀
  · rintro e ⟨cp, rfl⟩
    let f := orderedShortenedEdgeEmbedding U enumerateX hEnumerate oldColour
      templateColour hColour hCoordinate hXBlocks cp
    refine ⟨f, ?_⟩
    rw [← contractedEnumerationOfEquiv_range U enumerateX cp]
    ext y
    exact ⟨fun ⟨i, hi⟩ => ⟨ULift.up i, hi⟩, fun ⟨i, hi⟩ => ⟨i.down, hi⟩⟩

/-- Full vertex coverage for the same shortened target follows from
coverage by the actual first wagons. -/
theorem orderedShortenedTarget_supportCovers
    {k : ℕ}
    (enumerateX : Fin k ≃ X) (hEnumerate : StrictMono enumerateX)
    (oldColour : V → I) (templateColour : X → I)
    (hColour : ∀ c : C, ∀ p : P,
      ∀ z : {v : V // v ∈ (U c).oldCarrier p},
        oldColour z.1 = templateColour ((U c).coordinate p z))
    (hCoordinate : ∀ c : C, ∀ p : P, StrictMono ((U c).coordinate p))
    (hXBlocks : ∀ x y : X, templateColour x ≠ templateColour y →
      x < y → templateColour x < templateColour y)
    (hOldCover : ∀ c : C, ∀ v : V, ∃ p : P, v ∈ (U c).oldCarrier p)
    (z : Vertex U) :
    ∃ e : {e : Set (Vertex U) // e ∈ supportCopies
      (colouredOrderedEdgeSource k (fun i => templateColour (enumerateX i))).ordered
      (orderedShortenedTarget U oldColour templateColour)}, z ∈ e.1 := by
  obtain ⟨cp, hz⟩ := contractedFamily_covers U hOldCover z
  refine ⟨⟨contractedCarrier U cp, ?_⟩, hz⟩
  rw [orderedShortenedTarget_support_eq U enumerateX hEnumerate oldColour
    templateColour hColour hCoordinate hXBlocks]
  exact ⟨cp, rfl⟩

end IndexedPrivateChoice
end StructuralRamsey.Girth
