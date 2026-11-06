import Girth.Support

set_option Elab.async false

/-!
# A relational presentation with exactly the declared uniform hyperedges

For a k-uniform hypergraph, use a single symmetric irreflexive k-ary
relation: a tuple is related precisely when it is injective and its
range is one of the declared physical edges. The k-vertex single-edge
source has its relation on precisely the injective self-tuples.

Every induced embedding of that source has image one declared edge,
because the full injective tuple of all source vertices is related.
Conversely, every injected enumeration of a declared physical edge
is an induced embedding: an injective endomap of Fin k is surjective,
so all full edge permutations are related, and no proper repeated-entry
tuple is. Thus no accidental physical support copy appears.

This is the uncoloured relational presentation core of the cutoff-two
G0-to-M contraction. Colour predicates and within-predicate orders
still need to be transported in the actual application. No output
girth, selected embedding or Ramsey arrow is assumed.
-/

namespace StructuralRamsey.Girth

universe v
variable {V : Type v}

/-- The one-symbol k-uniform relational language. -/
def uniformEdgeLanguage (k : ℕ) : RelLanguage where
  Symbol := Unit
  arity := fun _ => k

/-- A single complete k-edge, including every permutation of its
distinct k endpoints and excluding repeated-entry tuples. -/
def uniformEdgeSource (k : ℕ) :
    RelStructure (uniformEdgeLanguage k) (Fin k) where
  rel _ x := Function.Injective x

/-- The relational reduct of the declared physical k-edge family.
No other k-ary tuples are added. -/
def uniformEdgeTarget (k : ℕ) (E : Set (Set V)) :
    RelStructure (uniformEdgeLanguage k) V where
  rel _ x := Function.Injective x ∧ Set.range x ∈ E

/-- Every injectively enumerated declared edge is a genuine INDUCED
copy of the one-edge type. It is not just a positive homomorphism. -/
def uniformEdgeEmbedding (k : ℕ) (E : Set (Set V))
    (i : Fin k ↪ V)
    (hEdge : Set.range (i : Fin k → V) ∈ E) :
    RelStructure.Embedding (uniformEdgeSource k) (uniformEdgeTarget k E) where
  toFun := i
  injective := i.injective
  map_rel_iff := by
    intro R x
    change (Function.Injective ((i : Fin k → V) ∘ x) ∧
      Set.range ((i : Fin k → V) ∘ x) ∈ E) ↔
        Function.Injective x
    constructor
    · intro h
      intro a b hab
      exact h.1 (congrArg (i : Fin k → V) hab)
    · intro hx
      have hSurj : Function.Surjective x :=
        Finite.injective_iff_surjective.mp hx
      have hRange :
          Set.range ((i : Fin k → V) ∘ x) =
            Set.range (i : Fin k → V) := by
        ext y
        constructor
        · rintro ⟨t, rfl⟩
          exact ⟨x t, rfl⟩
        · rintro ⟨t, rfl⟩
          obtain ⟨s, hs⟩ := hSurj t
          exact ⟨s, by simp only [Function.comp_apply, hs]⟩
      exact ⟨i.injective.comp hx, by simpa only [hRange] using hEdge⟩

/-- Every genuine induced one-edge support copy in the target is one of
the declared whole physical hyperedges. No spurious supports. -/
theorem uniformEdgeEmbedding_carrier_mem (k : ℕ) (E : Set (Set V))
    (f : RelStructure.Embedding (uniformEdgeSource k) (uniformEdgeTarget k E)) :
    copyCarrier f ∈ E := by
  have h := (f.map_rel_iff () (fun x : Fin k => x)).mpr
    (Function.injective_id : Function.Injective (fun x : Fin k => x))
  change Function.Injective (f ∘ (fun x : Fin k => x)) ∧
    Set.range (f ∘ (fun x : Fin k => x)) ∈ E at h
  simpa only [copyCarrier, Function.comp_id] using h.2

/-- Exact physical support after choosing an injective enumeration for
each declared edge. This is satisfied by every genuine k-uniform
hypergraph, and it is the only input concerning edge cardinalities. -/
theorem uniformEdgeSupport_exact (k : ℕ) (E : Set (Set V))
    (hEnumerate : ∀ e ∈ E, ∃ i : Fin k ↪ V,
      Set.range (i : Fin k → V) = e) :
    supportCopies (uniformEdgeSource k) (uniformEdgeTarget k E) = E := by
  apply Set.Subset.antisymm
  · rintro e ⟨f, hEq⟩
    rw [hEq]
    exact uniformEdgeEmbedding_carrier_mem k E f
  · intro e he
    obtain ⟨i, hi⟩ := hEnumerate e he
    have hiE : Set.range (i : Fin k → V) ∈ E := by
      rw [hi]
      exact he
    let f := uniformEdgeEmbedding k E i hiE
    refine ⟨f, ?_⟩
    change e = Set.range (i : Fin k → V)
    exact hi.symm

/-- A uniformly enumerated family of physical edges has exactly that
family as its relational one-edge support, even with repeated labels. -/
theorem uniformEdgeSupport_of_enumerations {S : Type v}
    (k : ℕ) (enumerate : S → Fin k ↪ V) :
    supportCopies (uniformEdgeSource k)
        (uniformEdgeTarget k (Set.range (fun s : S =>
          Set.range (enumerate s : Fin k → V)))) =
      Set.range (fun s : S => Set.range (enumerate s : Fin k → V)) := by
  apply uniformEdgeSupport_exact
  rintro e ⟨s, rfl⟩
  exact ⟨enumerate s, rfl⟩

end StructuralRamsey.Girth
