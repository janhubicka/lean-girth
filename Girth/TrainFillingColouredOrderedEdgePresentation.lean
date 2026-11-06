import Girth.Support

set_option Elab.async false

/-!
# Exact physical support of a coloured ordered one-edge presentation

A coloured edge has k vertices, a unary colour predicate for each
i ∈ I, a symmetric irreflexive k-ary edge relation, and a binary
order restricted to pairs of the SAME colour. A finite ordered
uniform hypergraph has a relational presentation whose edge tuples
are exactly the injective enumerations of its declared carriers.

For an edge enumeration preserving colours and the within-colour
orders, ALL relations are preserved and reflected: an injective
self-map of Fin k is surjective, while a repeated-entry tuple
cannot be an edge. Consequently the complete relational support
of the prescribed one-edge type is exactly the declared carrier
family, without any accidental induced edge copies.

This is the literal coloured/order core of the G0→M contraction.
Constructing a common ambient order on the full tagged private
vertex set and instantiating it for every first wagon are still
separate application tasks. No girth, Ramsey arrow or output
induced-copy property is postulated.
-/

namespace StructuralRamsey.Girth

universe u v
variable {I : Type u} {V : Type v}

/-- One full edge relation, unary colour predicates, and a binary
order relation restricted to equal-colour vertices. -/
def colouredOrderedEdgeLanguage (I : Type u) (k : ℕ) : RelLanguage.{u} where
  Symbol := (Unit ⊕ I) ⊕ Unit
  arity := by
    intro R
    cases R with
    | inl s =>
      cases s with
      | inl _ => exact k
      | inr _ => exact 1
    | inr _ => exact 2

/-- The ordered k-point one-edge type. Its source order is the
natural order on Fin k restricted to each unary predicate. -/
def colouredOrderedEdgeSource (k : ℕ) (sourceColour : Fin k → I) :
    RelStructure (colouredOrderedEdgeLanguage I k) (Fin k) where
  rel R := by
    cases R with
    | inl s =>
      cases s with
      | inl _ => exact fun x => Function.Injective x
      | inr i => exact fun x => sourceColour (x 0) = i
    | inr _ =>
      exact fun x =>
        sourceColour (x 0) = sourceColour (x 1) ∧ x 0 < x 1

/-- Retain exactly the declared k-edges, the genuine colour
predicates, and the ambient within-colour order. -/
def colouredOrderedEdgeTarget
    (k : ℕ) (E : Set (Set V)) (targetColour : V → I)
    [LinearOrder V] :
    RelStructure (colouredOrderedEdgeLanguage I k) V where
  rel R := by
    cases R with
    | inl s =>
      cases s with
      | inl _ => exact fun x => Function.Injective x ∧ Set.range x ∈ E
      | inr i => exact fun x => targetColour (x 0) = i
    | inr _ =>
      exact fun x =>
        targetColour (x 0) = targetColour (x 1) ∧ x 0 < x 1

/-- An actual enumerated edge is a complete INDUCED copy of the
coloured ordered one-edge structure. All predicate and order
reflection requirements are explicit properties of the genuine
edge enumeration, not consequences assumed about the output copy. -/
def colouredOrderedEdgeEmbedding
    [LinearOrder V]
    (k : ℕ) (E : Set (Set V))
    (sourceColour : Fin k → I) (targetColour : V → I)
    (ι : Fin k ↪ V)
    (hEdge : Set.range (ι : Fin k → V) ∈ E)
    (hColour : ∀ x : Fin k, targetColour (ι x) = sourceColour x)
    (hWithinOrder : ∀ x y : Fin k, sourceColour x = sourceColour y →
      (x < y ↔ ι x < ι y)) :
    RelStructure.Embedding
      (colouredOrderedEdgeSource k sourceColour)
      (colouredOrderedEdgeTarget k E targetColour) where
  toFun := ι
  injective := ι.injective
  map_rel_iff := by
    intro R x
    cases R with
    | inl s =>
      cases s with
      | inl _ =>
        change (Function.Injective ((ι : Fin k → V) ∘ x) ∧
          Set.range ((ι : Fin k → V) ∘ x) ∈ E) ↔
            Function.Injective x
        constructor
        · intro h
          intro a b hab
          exact h.1 (congrArg (ι : Fin k → V) hab)
        · intro hx
          have hSurj : Function.Surjective x :=
            Finite.injective_iff_surjective.mp hx
          have hRange :
              Set.range ((ι : Fin k → V) ∘ x) =
                Set.range (ι : Fin k → V) := by
            ext y
            constructor
            · rintro ⟨t, rfl⟩
              exact ⟨x t, rfl⟩
            · rintro ⟨t, rfl⟩
              obtain ⟨s, hs⟩ := hSurj t
              exact ⟨s, by simp only [Function.comp_apply, hs]⟩
          exact ⟨ι.injective.comp hx, by simpa only [hRange] using hEdge⟩
      | inr colour =>
        change targetColour (ι (x 0)) = colour ↔
          sourceColour (x 0) = colour
        rw [hColour (x 0)]
    | inr _ =>
      change (targetColour (ι (x 0)) = targetColour (ι (x 1)) ∧
        ι (x 0) < ι (x 1)) ↔
        (sourceColour (x 0) = sourceColour (x 1) ∧ x 0 < x 1)
      have hc :
          (targetColour (ι (x 0)) = targetColour (ι (x 1))) ↔
            sourceColour (x 0) = sourceColour (x 1) := by
        simp only [hColour]
      constructor
      · rintro ⟨hColourEq, hLt⟩
        have hs := hc.mp hColourEq
        exact ⟨hs, (hWithinOrder (x 0) (x 1) hs).mpr hLt⟩
      · rintro ⟨hs, hLt⟩
        exact ⟨hc.mpr hs, (hWithinOrder (x 0) (x 1) hs).mp hLt⟩

/-- Every genuine one-edge embedding in the relational target uses
one of the DECLARED full physical edges. Testing the identity
k-tuple suffices; no edge closure or ambient pruning premise. -/
theorem colouredOrderedEdgeEmbedding_carrier_mem
    [LinearOrder V]
    (k : ℕ) (E : Set (Set V))
    (sourceColour : Fin k → I) (targetColour : V → I)
    (f : RelStructure.Embedding
      (colouredOrderedEdgeSource k sourceColour)
      (colouredOrderedEdgeTarget k E targetColour)) :
    copyCarrier f ∈ E := by
  have h := (f.map_rel_iff (.inl (.inl ()))
    (fun x : Fin k => x)).mpr
    (Function.injective_id : Function.Injective (fun x : Fin k => x))
  change Function.Injective (f ∘ (fun x : Fin k => x)) ∧
    Set.range (f ∘ (fun x : Fin k => x)) ∈ E at h
  simpa only [copyCarrier, Function.comp_id] using h.2

/-- The FULL support of the coloured ordered one-edge type equals
the declared edge family, whenever each edge admits its actual
colour- and within-part-order-preserving enumeration. -/
theorem colouredOrderedEdgeSupport_exact
    [LinearOrder V]
    (k : ℕ) (E : Set (Set V))
    (sourceColour : Fin k → I) (targetColour : V → I)
    (hEnumerate : ∀ e ∈ E, ∃ ι : Fin k ↪ V,
      Set.range (ι : Fin k → V) = e ∧
      (∀ x, targetColour (ι x) = sourceColour x) ∧
      (∀ x y, sourceColour x = sourceColour y →
        (x < y ↔ ι x < ι y))) :
    supportCopies (colouredOrderedEdgeSource k sourceColour)
      (colouredOrderedEdgeTarget k E targetColour) = E := by
  apply Set.Subset.antisymm
  · rintro e ⟨f, hEq⟩
    rw [hEq]
    exact colouredOrderedEdgeEmbedding_carrier_mem
      k E sourceColour targetColour f
  · intro e he
    obtain ⟨ι, hRange, hColour, hWithinOrder⟩ :=
      hEnumerate e he
    have hiE : Set.range (ι : Fin k → V) ∈ E := by
      rw [hRange]
      exact he
    let f := colouredOrderedEdgeEmbedding k E
      sourceColour targetColour ι hiE hColour hWithinOrder
    refine ⟨f, ?_⟩
    change e = Set.range (ι : Fin k → V)
    exact hRange.symm

end StructuralRamsey.Girth
