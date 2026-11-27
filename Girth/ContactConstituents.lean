import Girth.ContactPictureInvariant

/-! The actual constituents used to reduce a contact polygon.
They are standard contact domains and enlarged core edges. Their
intersections are exact on the core, and the intersection of two
distinct constituents containing two core points lies in one wagon.
-/

namespace StructuralRamsey.Girth
universe v
variable {V E I P U F J R V₀ E₀ I₀ P₀ : Type v}

namespace ContactPictureData
variable {D : OrderOneData V E I P} {L : OrderOneData V₀ E₀ I₀ P₀}
    {H : OrderOneData U F J R} (A : ContactPictureData D L H)

def coreConstituent (_A : ContactPictureData D L H) : I ⊕ E → Set (V ⊕ P)
  | .inl i => D.contactCopyClique i
  | .inr e => {z | match z with
    | .inl x => x ∈ D.edgeCarrier e
    | .inr p => p = D.parent e}

def constituent : I ⊕ E → Set (U ⊕ R)
  | .inl i => A.contactDomain i
  | .inr e => A.core.contactMap '' A.coreConstituent (.inr e)

theorem core_constituent_iff (a : I ⊕ E) (z : V ⊕ P) :
    A.core.contactMap z ∈ A.constituent a ↔ z ∈ A.coreConstituent a := by
  cases a with
  | inl i => exact A.core_contact_in_standard i z
  | inr e =>
    constructor
    · rintro ⟨t,ht,he⟩
      simpa only [A.core.contactMap_injective he] using ht
    · intro hz
      exact ⟨z,hz,rfl⟩

theorem core_edge_subset_wagon (e : E) :
    A.coreConstituent (.inr e) ⊆ D.contactWagonClique (D.parent e) := by
  intro z hz
  cases z with
  | inl x => exact ⟨e,rfl,hz⟩
  | inr p => exact hz

theorem enlarged_edge_subset_wagon (e : E) :
    A.constituent (.inr e) ⊆ H.contactWagonClique (A.core.wagon (D.parent e)) := by
  rintro z ⟨t,ht,rfl⟩
  exact A.core.wagon_clique_preserve _ (A.core_edge_subset_wagon e ht)

/-- Each constituent's core points lie in a genuine generating clique. -/
theorem core_constituent_cover (a : I ⊕ E) :
    ∃ b : I ⊕ P, A.coreConstituent a ⊆ D.contactClique b := by
  cases a with
  | inl i => exact ⟨Sum.inl i,fun _ h => h⟩
  | inr e => exact ⟨Sum.inr (D.parent e),A.core_edge_subset_wagon e⟩

theorem shared_constituent_core (a b : I ⊕ E) (hab : a ≠ b)
    {z : U ⊕ R} (ha : z ∈ A.constituent a) (hb : z ∈ A.constituent b) :
    z ∈ Set.range A.core.contactMap := by
  cases a with
  | inr e =>
    obtain ⟨t,_,he⟩ := ha
    exact ⟨t,he⟩
  | inl i =>
    cases b with
    | inr e =>
      obtain ⟨t,_,he⟩ := hb
      exact ⟨t,he⟩
    | inl j =>
      obtain ⟨t,ht,_,_⟩ := A.shared_contact_in_core i j
        (fun he => hab (congrArg Sum.inl he)) z ha hb
      exact ⟨t,ht⟩

/-- The core intersection of two distinct constituents lies in a wagon
whenever it contains a pair. Core edges are already in wagon cliques. -/
theorem core_constituent_shared_pair (h2 : D.ContactG2)
    (a b : I ⊕ E) (hab : a ≠ b) {x y : V ⊕ P} (hxy : x ≠ y)
    (hxa : x ∈ A.coreConstituent a) (hya : y ∈ A.coreConstituent a)
    (hxb : x ∈ A.coreConstituent b) (hyb : y ∈ A.coreConstituent b) :
    ∃ p, x ∈ D.contactWagonClique p ∧ y ∈ D.contactWagonClique p := by
  cases a with
  | inr e => exact ⟨D.parent e,A.core_edge_subset_wagon e hxa,A.core_edge_subset_wagon e hya⟩
  | inl i =>
    cases b with
    | inr e => exact ⟨D.parent e,A.core_edge_subset_wagon e hxb,A.core_edge_subset_wagon e hyb⟩
    | inl j =>
      exact D.contact_shared_pair_in_wagon h2
        (a := Sum.inl i) (b := Sum.inl j)
        (fun he => hab (congrArg Sum.inl (Sum.inl.inj he))) hxy hxa hya hxb hyb

theorem core_contact_weight (x y : V ⊕ P) :
    contactWeight (A.core.contactMap x) (A.core.contactMap y) = contactWeight x y := by
  cases x <;> cases y <;> rfl

end ContactPictureData
end StructuralRamsey.Girth
