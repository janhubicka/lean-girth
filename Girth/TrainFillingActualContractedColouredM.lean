import Girth.TrainFillingIndexedContractedEnumeration
import Girth.TrainFillingColouredOrderedEdgePresentation
import Girth.TrainFillingRelationalSelectedSupport

set_option Elab.async false

/-!
# The actual coloured contracted M on all heterogeneous G0 vertices

The earlier checked interfaces established separately:
- all physical G0 first-wagon carriers, as labelled subsets of the
  actual heterogeneous Sigma vertex type;
- their full X-enumerations and source-independent unary colours;
- a coloured ordered one-edge relational structure whose FULL
  A-support is exactly a declared family of k-edges.

This module composes them, constructing a literal contracted relational
M on G0's actual tagged vertices. Assuming a common global order on
the tagged vertices which restricts correctly to every private
first-wagon X-placement, M's complete A-support equals exactly the
set of full contracted first-wagon carriers.

No independently chosen M support family, embedded selected copy or
new physical edge type is an input. The common compatible global
order is still a genuine construction obligation and is explicitly
exposed rather than smuggled into the result. No girth/Ramsey arrow
or ambient edge pruning is claimed.
-/

namespace StructuralRamsey.Girth.IndexedPrivateChoice

open StructuralRamsey.RelStructure

universe u v
variable {C V P X : Type v}
variable {I : Type u}
variable (U : C → PrivateWagonInput V P X)

/-- Coloured ordered M defined LITERALLY on the complete tagged G0
vertex set, with precisely all whole first-wagon carriers as edges. -/
def actualContractedColouredM
    {k : ℕ}
    (oldColour : V → I) (templateColour : X → I)
    [LinearOrder (Vertex U)] :
    RelStructure (colouredOrderedEdgeLanguage I k) (Vertex U) :=
  colouredOrderedEdgeTarget k
    (Set.range (contractedCarrier U))
    (contractedVertexColour U oldColour templateColour)

/-- Every G0 first-wagon carrier is a genuine induced coloured
one-edge support of M, and conversely. The source one-edge structure
uses the fixed X-colour profile through the chosen enumeration X ≃ Fin k.

The only order hypothesis is the actual requirement for each complete
X-placement to respect within-colour orders, *not* a postulated output
support equality or selected-copy embedding. -/
theorem actualContractedColouredM_support_eq
    {k : ℕ} [LinearOrder (Vertex U)]
    (enumerateX : Fin k ≃ X)
    (oldColour : V → I) (templateColour : X → I)
    (hColour : ∀ c : C, ∀ p : P,
      ∀ z : {v : V // v ∈ (U c).oldCarrier p},
        oldColour z.1 =
          templateColour ((U c).coordinate p z))
    (hOrdered : ∀ e : C × P, ∀ i j : Fin k,
      templateColour (enumerateX i) = templateColour (enumerateX j) →
      (i < j ↔
        contractedEnumerationOfEquiv U enumerateX e i <
          contractedEnumerationOfEquiv U enumerateX e j)) :
    supportCopies
        (colouredOrderedEdgeSource k
          (fun i => templateColour (enumerateX i)))
        (actualContractedColouredM U oldColour templateColour) =
      Set.range (contractedCarrier U) := by
  change supportCopies
      (colouredOrderedEdgeSource k
        (fun i => templateColour (enumerateX i)))
      (colouredOrderedEdgeTarget k
        (Set.range (contractedCarrier U))
        (contractedVertexColour U oldColour templateColour)) =
    Set.range (contractedCarrier U)
  apply colouredOrderedEdgeSupport_exact
    k (Set.range (contractedCarrier U))
    (fun i => templateColour (enumerateX i))
    (contractedVertexColour U oldColour templateColour)
  intro e he
  obtain ⟨cp, rfl⟩ := he
  refine ⟨contractedEnumerationOfEquiv U enumerateX cp,
    contractedEnumerationOfEquiv_range U enumerateX cp, ?_, ?_⟩
  · intro i
    change contractedVertexColour U oldColour templateColour
      (tagVertex U cp.1 ((U cp.1).place cp.2 (enumerateX i))) =
        templateColour (enumerateX i)
    exact contractedVertexColour_place U oldColour templateColour
      hColour cp.1 cp.2 (enumerateX i)
  · intro i j hij
    exact hOrdered cp i j hij

/-- The constructed M is covered by its actual A-support, given
coverage of the old V-carrier by its first wagons. This rules out
isolated private vertices without an extra axiom on M. -/
theorem actualContractedColouredM_supportCovers
    {k : ℕ} [LinearOrder (Vertex U)]
    (enumerateX : Fin k ≃ X)
    (oldColour : V → I) (templateColour : X → I)
    (hColour : ∀ c : C, ∀ p : P,
      ∀ z : {v : V // v ∈ (U c).oldCarrier p},
        oldColour z.1 =
          templateColour ((U c).coordinate p z))
    (hOrdered : ∀ e : C × P, ∀ i j : Fin k,
      templateColour (enumerateX i) = templateColour (enumerateX j) →
      (i < j ↔
        contractedEnumerationOfEquiv U enumerateX e i <
          contractedEnumerationOfEquiv U enumerateX e j))
    (hOldCover : ∀ c : C, ∀ v : V,
      ∃ p : P, v ∈ (U c).oldCarrier p)
    (z : Vertex U) :
    ∃ e : {f : Set (Vertex U) //
       f ∈ supportCopies
         (colouredOrderedEdgeSource k
           (fun i => templateColour (enumerateX i)))
         (actualContractedColouredM U oldColour templateColour)},
      z ∈ e.1 := by
  obtain ⟨cp, hz⟩ := contractedFamily_covers U hOldCover z
  have hCarrier : contractedCarrier U cp ∈ supportCopies
      (colouredOrderedEdgeSource k
        (fun i => templateColour (enumerateX i)))
      (actualContractedColouredM U oldColour templateColour) := by
    rw [actualContractedColouredM_support_eq U enumerateX
      oldColour templateColour hColour hOrdered]
    exact ⟨cp, rfl⟩
  exact ⟨⟨contractedCarrier U cp, hCarrier⟩, hz⟩

/-- The genuinely selected relational M-copy in N now supplies the
physical old-edge embedding of every contracted G0 first wagon.

This is NOT a separately assumed edge map: source-edge membership
comes from the proved full support equality, image membership from
composition of relational A-embeddings, and injectivity from the
physical distinctness of actual G0 contracted carriers. -/
def actualContractedSelectedOldEdgeEmbedding
    {Y : Type v} {k : ℕ}
    [Nontrivial X] [LinearOrder (Vertex U)]
    (enumerateX : Fin k ≃ X)
    (oldColour : V → I) (templateColour : X → I)
    (hColour : ∀ c : C, ∀ p : P,
      ∀ z : {v : V // v ∈ (U c).oldCarrier p},
        oldColour z.1 =
          templateColour ((U c).coordinate p z))
    (hOrdered : ∀ e : C × P, ∀ i j : Fin k,
      templateColour (enumerateX i) = templateColour (enumerateX j) →
      (i < j ↔
        contractedEnumerationOfEquiv U enumerateX e i <
          contractedEnumerationOfEquiv U enumerateX e j))
    (hLinear : ∀ c : C, ∀ p q : P, p ≠ q →
      ((U c).oldCarrier p ∩ (U c).oldCarrier q).Subsingleton)
    (N : RelStructure (colouredOrderedEdgeLanguage I k) Y)
    (b : Embedding (actualContractedColouredM U oldColour templateColour) N)
    (H : UniformFillingData Y X)
    (hOldSupport : H.oldEdges =
      supportCopies
        (colouredOrderedEdgeSource k
          (fun i => templateColour (enumerateX i))) N) :
    (C × P) ↪ H.OldEdge :=
  H.oldEdgeEmbedding_from_vertex (contractedCarrier U)
    (contractedCarrier_injective U hLinear)
    b.toFunctionEmbedding
    (by
      intro cp
      rw [hOldSupport]
      have hSrc : contractedCarrier U cp ∈
          supportCopies
            (colouredOrderedEdgeSource k
              (fun i => templateColour (enumerateX i)))
            (actualContractedColouredM U oldColour templateColour) := by
        rw [actualContractedColouredM_support_eq U enumerateX
          oldColour templateColour hColour hOrdered]
        exact ⟨cp, rfl⟩
      exact supportCopy_image_mem
        (colouredOrderedEdgeSource k
          (fun i => templateColour (enumerateX i)))
        (actualContractedColouredM U oldColour templateColour)
        N b ⟨contractedCarrier U cp, hSrc⟩)

/-- The old N edge selected above has exactly the full vertex image
of its corresponding G0 first-wagon carrier. -/
@[simp] theorem actualContractedSelectedOldEdgeEmbedding_carrier
    {Y : Type v} {k : ℕ}
    [Nontrivial X] [LinearOrder (Vertex U)]
    (enumerateX : Fin k ≃ X)
    (oldColour : V → I) (templateColour : X → I)
    (hColour : ∀ c : C, ∀ p : P,
      ∀ z : {v : V // v ∈ (U c).oldCarrier p},
        oldColour z.1 =
          templateColour ((U c).coordinate p z))
    (hOrdered : ∀ e : C × P, ∀ i j : Fin k,
      templateColour (enumerateX i) = templateColour (enumerateX j) →
      (i < j ↔
        contractedEnumerationOfEquiv U enumerateX e i <
          contractedEnumerationOfEquiv U enumerateX e j))
    (hLinear : ∀ c : C, ∀ p q : P, p ≠ q →
      ((U c).oldCarrier p ∩ (U c).oldCarrier q).Subsingleton)
    (N : RelStructure (colouredOrderedEdgeLanguage I k) Y)
    (b : Embedding (actualContractedColouredM U oldColour templateColour) N)
    (H : UniformFillingData Y X)
    (hOldSupport : H.oldEdges =
      supportCopies
        (colouredOrderedEdgeSource k
          (fun i => templateColour (enumerateX i))) N)
    (cp : C × P) :
    (actualContractedSelectedOldEdgeEmbedding U enumerateX
      oldColour templateColour hColour hOrdered hLinear
      N b H hOldSupport cp).1 =
      b.toFunctionEmbedding '' contractedCarrier U cp := rfl

end StructuralRamsey.Girth.IndexedPrivateChoice
