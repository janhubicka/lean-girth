import Girth.TrainFillingPrivateColouredInsertionOrder
import Girth.TrainFillingIndexedContractedEnumeration
import Girth.TrainFillingActualContractedColouredM

set_option Elab.async false

/-!
# One colour-block total order on the ENTIRE heterogeneous G0

The checked heterogeneous source has the actual vertex type
Σ c, (U c).Vertex. Each choice's private vertices have an insertion
key derived from the original coordinate map into X; these keys
already separate old vertices and all private owner tokens.

Order first by predicate colour, then by the choice tag c, then by
the private insertion key within that choice. This gives ONE total
order on all of G0, with no independent output order field.

For each choice c and first wagon p, the literal whole-X placement
is strictly increasing provided:
- original old coordinates preserve unary predicate colours;
- old coordinates are strictly monotone in their prescribed orders;
- X's total order lists different predicate blocks in the common
  colour order.

Consequently any increasing common enumeration Fin k ≃ X yields
the exact within-predicate ordered enumeration required by the
checked coloured relational M support theorem (#897). Only those
actual input-order hypotheses remain; no support edge or selected
copy is supplied by hand.
-/

namespace StructuralRamsey.Girth.IndexedPrivateChoice

universe v
variable {C V P X I : Type v}
variable (U : C → PrivateWagonInput V P X)
variable [LinearOrder C] [LinearOrder V] [Fintype V]
variable [LinearOrder P] [LinearOrder X] [LinearOrder I]

/-- One ordered key on the actual complete Sigma vertex set. -/
noncomputable def colouredChoiceInsertionKey
    (oldColour : V → I) (templateColour : X → I) :
    Vertex U → I ×ₗ (C ×ₗ (WithTop V ×ₗ WithTop (P ×ₗ X))) :=
  fun z => toLex
    (contractedVertexColour U oldColour templateColour z,
      toLex (z.1, PrivateWagonInput.insertionKey (U z.1) z.2))

/-- Choice tags distinguish vertices from different choices; within
one choice, the old/private insertion key is injective. -/
theorem colouredChoiceInsertionKey_injective
    (oldColour : V → I) (templateColour : X → I) :
    Function.Injective
      (colouredChoiceInsertionKey U oldColour templateColour) := by
  rintro ⟨c, z⟩ ⟨d, w⟩ h
  have hChoice : c = d :=
    congrArg
      (fun q : I ×ₗ (C ×ₗ (WithTop V ×ₗ WithTop (P ×ₗ X))) =>
        (ofLex (ofLex q).2).1) h
  subst d
  have hKey :
      PrivateWagonInput.insertionKey (U c) z =
        PrivateWagonInput.insertionKey (U c) w :=
    congrArg
      (fun q : I ×ₗ (C ×ₗ (WithTop V ×ₗ WithTop (P ×ₗ X))) =>
        (ofLex (ofLex q).2).2) h
  exact congrArg (Sigma.mk c)
    ((PrivateWagonInput.insertionKey_injective (U c)) hKey)

/-- A single order on the whole heterogeneous union, with predicate
blocks in the common order, then choices, then private insertion. -/
noncomputable def colouredChoiceInsertionOrder
    (oldColour : V → I) (templateColour : X → I) :
    LinearOrder (Vertex U) :=
  LinearOrder.lift'
    (colouredChoiceInsertionKey U oldColour templateColour)
    (colouredChoiceInsertionKey_injective U oldColour templateColour)

/-- Every whole first-wagon coordinate preserves the order of X in
the ONE global heterogeneous union order. -/
theorem colouredChoicePlace_lt
    (oldColour : V → I) (templateColour : X → I)
    (hColour : ∀ c : C, ∀ p : P,
      ∀ z : {v : V // v ∈ (U c).oldCarrier p},
        oldColour z.1 = templateColour ((U c).coordinate p z))
    (hCoordinate : ∀ c : C, ∀ p : P,
      StrictMono ((U c).coordinate p))
    (hXBlocks : ∀ x y : X,
      templateColour x ≠ templateColour y →
      x < y → templateColour x < templateColour y)
    (cp : C × P) {x y : X} (hxy : x < y) :
    @LT.lt (Vertex U)
      (colouredChoiceInsertionOrder U oldColour templateColour).toLT
      (tagVertex U cp.1 ((U cp.1).place cp.2 x))
      (tagVertex U cp.1 ((U cp.1).place cp.2 y)) := by
  change colouredChoiceInsertionKey U oldColour templateColour
      (tagVertex U cp.1 ((U cp.1).place cp.2 x)) <
    colouredChoiceInsertionKey U oldColour templateColour
      (tagVertex U cp.1 ((U cp.1).place cp.2 y))
  have hCx : contractedVertexColour U oldColour templateColour
      (tagVertex U cp.1 ((U cp.1).place cp.2 x)) =
      templateColour x :=
    contractedVertexColour_place U oldColour templateColour hColour
      cp.1 cp.2 x
  have hCy : contractedVertexColour U oldColour templateColour
      (tagVertex U cp.1 ((U cp.1).place cp.2 y)) =
      templateColour y :=
    contractedVertexColour_place U oldColour templateColour hColour
      cp.1 cp.2 y
  by_cases hs : templateColour x = templateColour y
  · have hk : PrivateWagonInput.insertionKey (U cp.1)
        ((U cp.1).place cp.2 x) <
        PrivateWagonInput.insertionKey (U cp.1)
          ((U cp.1).place cp.2 y) :=
      PrivateWagonInput.insertionOrder_place_lt
        (U cp.1) (hCoordinate cp.1) cp.2 hxy
    have hInside :
        (toLex (cp.1, PrivateWagonInput.insertionKey (U cp.1)
              ((U cp.1).place cp.2 x)) :
          C ×ₗ (WithTop V ×ₗ WithTop (P ×ₗ X))) <
        toLex (cp.1, PrivateWagonInput.insertionKey (U cp.1)
              ((U cp.1).place cp.2 y)) :=
      Prod.Lex.toLex_lt_toLex.mpr (Or.inr ⟨rfl, hk⟩)
    exact Prod.Lex.toLex_lt_toLex.mpr
      (Or.inr ⟨by simpa only [hCx, hCy] using hs, hInside⟩)
  · exact Prod.Lex.toLex_lt_toLex.mpr
      (Or.inl (by simpa only [hCx, hCy] using
        (hXBlocks x y hs hxy)))

/-- A globally increasing enumeration of the common ordered X is
increasing on every actual contracted first wagon, including all
private vertices, not only the chosen W* support edge positions. -/
theorem colouredChoiceEnumerate_lt_iff
    {k : ℕ}
    (oldColour : V → I) (templateColour : X → I)
    (enumerateX : Fin k ≃ X) (hEnumerate : StrictMono enumerateX)
    (hColour : ∀ c : C, ∀ p : P,
      ∀ z : {v : V // v ∈ (U c).oldCarrier p},
        oldColour z.1 = templateColour ((U c).coordinate p z))
    (hCoordinate : ∀ c : C, ∀ p : P,
      StrictMono ((U c).coordinate p))
    (hXBlocks : ∀ x y : X,
      templateColour x ≠ templateColour y →
      x < y → templateColour x < templateColour y)
    (cp : C × P) (i j : Fin k) :
    (i < j ↔
      @LT.lt (Vertex U)
        (colouredChoiceInsertionOrder U oldColour templateColour).toLT
        (contractedEnumerationOfEquiv U enumerateX cp i)
        (contractedEnumerationOfEquiv U enumerateX cp j)) := by
  have hComposed :
      StrictMono
        (fun i : Fin k => (toLex
          (contractedVertexColour U oldColour templateColour
            (contractedEnumerationOfEquiv U enumerateX cp i),
           toLex (cp.1,
             PrivateWagonInput.insertionKey (U cp.1)
               ((U cp.1).place cp.2 (enumerateX i)))) :
          I ×ₗ (C ×ₗ (WithTop V ×ₗ WithTop (P ×ₗ X))))) := by
    intro a b hab
    exact colouredChoicePlace_lt U oldColour templateColour
      hColour hCoordinate hXBlocks cp (hEnumerate hab)
  -- Reduce the chosen order to the injective lexicographic key.
  change i < j ↔
    colouredChoiceInsertionKey U oldColour templateColour
      (contractedEnumerationOfEquiv U enumerateX cp i) <
    colouredChoiceInsertionKey U oldColour templateColour
      (contractedEnumerationOfEquiv U enumerateX cp j)
  exact (hComposed.lt_iff_lt).symm

/-- The actual contracted M with a CONSTRUCTED colour-first order on
all tagged heterogeneous G0 vertices, not an assumed global order. -/
noncomputable def actualIndexedContractedM
    {k : ℕ}
    (oldColour : V → I) (templateColour : X → I) :
    RelStructure (colouredOrderedEdgeLanguage I k) (Vertex U) :=
  letI : LinearOrder (Vertex U) :=
    colouredChoiceInsertionOrder U oldColour templateColour
  actualContractedColouredM U oldColour templateColour

/-- Exact physical support of the actual contracted M, WITHOUT a
separately postulated global order or full-edge support equality.

The old coordinates and template X really must respect the common
colour order. Under those actual input conditions the constructed
colour-first order provides all ordered enumerations, and the checked
support theorem #897 proves the conclusion. -/
theorem actualIndexedContractedM_support_eq
    {k : ℕ}
    (enumerateX : Fin k ≃ X) (hEnumerate : StrictMono enumerateX)
    (oldColour : V → I) (templateColour : X → I)
    (hColour : ∀ c : C, ∀ p : P,
      ∀ z : {v : V // v ∈ (U c).oldCarrier p},
        oldColour z.1 = templateColour ((U c).coordinate p z))
    (hCoordinate : ∀ c : C, ∀ p : P,
      StrictMono ((U c).coordinate p))
    (hXBlocks : ∀ x y : X,
      templateColour x ≠ templateColour y →
      x < y → templateColour x < templateColour y) :
    supportCopies
        (colouredOrderedEdgeSource k
          (fun i => templateColour (enumerateX i)))
        (actualIndexedContractedM U oldColour templateColour) =
      Set.range (contractedCarrier U) := by
  letI : LinearOrder (Vertex U) :=
    colouredChoiceInsertionOrder U oldColour templateColour
  change supportCopies
      (colouredOrderedEdgeSource k
        (fun i => templateColour (enumerateX i)))
      (actualContractedColouredM U oldColour templateColour) =
    Set.range (contractedCarrier U)
  apply actualContractedColouredM_support_eq
    U enumerateX oldColour templateColour hColour
  intro cp i j _
  exact colouredChoiceEnumerate_lt_iff U oldColour templateColour
    enumerateX hEnumerate hColour hCoordinate hXBlocks cp i j

end StructuralRamsey.Girth.IndexedPrivateChoice
