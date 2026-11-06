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
  arity := fun
    | .inl (.inl _) => k
    | .inl (.inr _) => 1
    | .inr _ => 2

/-- The ordered k-point one-edge type, lifted into the universe of its
ambient vertex type. The lift has exactly k elements. -/
def colouredOrderedEdgeSource (k : ℕ) (sourceColour : Fin k → I) :
    RelStructure (colouredOrderedEdgeLanguage I k)
      (ULift.{v} (Fin k)) where
  rel R := by
    cases R with
    | inl s =>
      cases s with
      | inl _ =>
        exact fun (x : Fin k → ULift.{v} (Fin k)) => Function.Injective x
      | inr i =>
        exact fun (x : Fin 1 → ULift.{v} (Fin k)) =>
          sourceColour (x 0).down = i
    | inr _ =>
      exact fun (x : Fin 2 → ULift.{v} (Fin k)) =>
        sourceColour (x 0).down = sourceColour (x 1).down ∧
          (x 0).down < (x 1).down

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
      | inl _ =>
        exact fun (x : Fin k → V) =>
          Function.Injective x ∧ Set.range x ∈ E
      | inr i =>
        exact fun (x : Fin 1 → V) => targetColour (x 0) = i
    | inr _ =>
      exact fun (x : Fin 2 → V) =>
        targetColour (x 0) = targetColour (x 1) ∧ x 0 < x 1

/-- An actual enumerated edge is an induced copy of the coloured
ordered one-edge structure. -/
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
  toFun := fun t => ι t.down
  injective := by
    intro x y h
    apply ULift.down_injective
    exact ι.injective h
  map_rel_iff := by
    intro R x
    cases R with
    | inl s =>
      cases s with
      | inl _ =>
        change (Function.Injective
            ((fun t : ULift.{v} (Fin k) => ι t.down) ∘ x) ∧
            Set.range ((fun t : ULift.{v} (Fin k) => ι t.down) ∘ x) ∈ E) ↔
          Function.Injective x
        constructor
        · intro h
          intro a b hab
          exact h.1 (congrArg
            (fun t : ULift.{v} (Fin k) => ι t.down) hab)
        · intro hx
          have hDown : Function.Injective
              (fun t : Fin k => (x t).down) := by
            intro a b h
            exact hx (ULift.down_injective h)
          have hSurj : Function.Surjective
              (fun t : Fin k => (x t).down) :=
            Finite.injective_iff_surjective.mp hDown
          have hRange :
              Set.range ((fun t : ULift.{v} (Fin k) => ι t.down) ∘ x) =
                Set.range (ι : Fin k → V) := by
            ext y
            constructor
            · rintro ⟨t, rfl⟩
              exact ⟨(x t).down, rfl⟩
            · rintro ⟨t, rfl⟩
              obtain ⟨q, hq⟩ := hSurj t
              exact ⟨q, by
                change ι ((x q).down) = ι t
                rw [hq]⟩
          exact ⟨ι.injective.comp hDown,
            by simpa only [hRange] using hEdge⟩
      | inr colour =>
        change targetColour (ι (x 0).down) = colour ↔
          sourceColour (x 0).down = colour
        rw [hColour]
    | inr _ =>
      change (targetColour (ι (x 0).down) =
          targetColour (ι (x 1).down) ∧
          ι (x 0).down < ι (x 1).down) ↔
        (sourceColour (x 0).down = sourceColour (x 1).down ∧
          (x 0).down < (x 1).down)
      have hc :
          (targetColour (ι (x 0).down) =
            targetColour (ι (x 1).down)) ↔
          sourceColour (x 0).down = sourceColour (x 1).down := by
        simp only [hColour]
      constructor
      · rintro ⟨hColourEq, hLt⟩
        have hs := hc.mp hColourEq
        exact ⟨hs,
          (hWithinOrder (x 0).down (x 1).down hs).mpr hLt⟩
      · rintro ⟨hs, hLt⟩
        exact ⟨hc.mpr hs,
          (hWithinOrder (x 0).down (x 1).down hs).mp hLt⟩

/-- The induced lifted source copy covers exactly the image of its
chosen full physical edge enumeration. -/
@[simp] theorem colouredOrderedEdgeEmbedding_carrier
    [LinearOrder V]
    (k : ℕ) (E : Set (Set V))
    (sourceColour : Fin k → I) (targetColour : V → I)
    (ι : Fin k ↪ V)
    (hEdge : Set.range (ι : Fin k → V) ∈ E)
    (hColour : ∀ x : Fin k, targetColour (ι x) = sourceColour x)
    (hWithinOrder : ∀ x y : Fin k, sourceColour x = sourceColour y →
      (x < y ↔ ι x < ι y)) :
    copyCarrier (colouredOrderedEdgeEmbedding k E sourceColour targetColour
        ι hEdge hColour hWithinOrder) =
      Set.range (ι : Fin k → V) := by
  ext y
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨t.down, rfl⟩
  · rintro ⟨t, rfl⟩
    exact ⟨ULift.up t, rfl⟩

/-- Every genuine one-edge embedding uses a declared full physical edge. -/
theorem colouredOrderedEdgeEmbedding_carrier_mem
    [LinearOrder V]
    (k : ℕ) (E : Set (Set V))
    (sourceColour : Fin k → I) (targetColour : V → I)
    (f : RelStructure.Embedding
      (colouredOrderedEdgeSource k sourceColour)
      (colouredOrderedEdgeTarget k E targetColour)) :
    copyCarrier f ∈ E := by
  let up : Fin k → ULift.{v} (Fin k) := ULift.up
  have hup : Function.Injective up := by
    intro a b h
    exact congrArg ULift.down h
  have h := (f.map_rel_iff (.inl (.inl ())) up).mpr hup
  change Function.Injective (f ∘ up) ∧ Set.range (f ∘ up) ∈ E at h
  have heq : Set.range (f ∘ up) = copyCarrier f := by
    ext y
    constructor
    · rintro ⟨t, rfl⟩
      exact ⟨up t, rfl⟩
    · rintro ⟨t, rfl⟩
      exact ⟨t.down, by cases t; rfl⟩
  rw [heq] at h
  exact h.2

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
    change e = copyCarrier
      (colouredOrderedEdgeEmbedding k E sourceColour targetColour
        ι hiE hColour hWithinOrder)
    rw [colouredOrderedEdgeEmbedding_carrier]
    exact hRange.symm

end StructuralRamsey.Girth
