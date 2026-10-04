import Girth.Support
import Mathlib.Data.Set.Subsingleton

/-! # Closure structure of the Ramsey target

This file isolates the elementary combinatorics of the two closure functions
used in the A-linear Ramsey input.  It does not depend on the external EHN
Ramsey theorem.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {U V : Type v}

/-- Three vertices lie together in some ambient copy of A. -/
def TripleInACopy
    (A : RelStructure L U) (B : RelStructure L V)
    (x y z : V) : Prop :=
  ∃ a : Embedding A B,
    x ∈ copyCarrier a ∧ y ∈ copyCarrier a ∧ z ∈ copyCarrier a

/-- Combinatorial closure conditions induced on the target by c_A and c_B.

The first clause closes every distinct pair lying in an A-copy to that whole
copy.  The second closes any triple with at least two distinct entries, not
contained in one A-copy, to the whole target.
-/
def TargetClosed
    (A : RelStructure L U) (B : RelStructure L V)
    (S : Set V) : Prop :=
  (∀ x, x ∈ S → ∀ y, y ∈ S → x ≠ y →
      ∀ a : Embedding A B,
        x ∈ copyCarrier a → y ∈ copyCarrier a →
          copyCarrier a ⊆ S) ∧
  (∀ x, x ∈ S → ∀ y, y ∈ S → ∀ z, z ∈ S →
      (x ≠ y ∨ x ≠ z ∨ y ≠ z) →
      ¬ TripleInACopy A B x y z →
      S = Set.univ)

/-- A common pair of distinct vertices determines an A-copy in an A-linear
ambient structure. -/
theorem sameCopy_of_common_distinct_pair
    {A : RelStructure L U} {B : RelStructure L V}
    (hLinear : ALinear A B)
    (a b : Embedding A B)
    {x y : V}
    (hxa : x ∈ copyCarrier a) (hya : y ∈ copyCarrier a)
    (hxb : x ∈ copyCarrier b) (hyb : y ∈ copyCarrier b)
    (hxy : x ≠ y) :
    SameCopy a b := by
  by_contra hne
  have hs := hLinear a b hne
  exact hxy (hs ⟨hxa, hxb⟩ ⟨hya, hyb⟩)

/-- The full target is closed. -/
theorem targetClosed_univ
    (A : RelStructure L U) (B : RelStructure L V) :
    TargetClosed A B Set.univ := by
  constructor
  · intro x _ y _ _ a _ _ z _
    exact Set.mem_univ z
  · intro x _ y _ z _ _ _
    rfl

/-- Every singleton is target-closed. -/
theorem targetClosed_singleton
    (A : RelStructure L U) (B : RelStructure L V)
    (x : V) :
    TargetClosed A B {x} := by
  constructor
  · intro y hy z hz hyz
    have : y = z := by
      simpa only [Set.mem_singleton_iff] using
        (hy.trans hz.symm)
    exact (hyz this).elim
  · intro y hy z hz w hw hdist
    have hyx : y = x := by simpa using hy
    have hzx : z = x := by simpa using hz
    have hwx : w = x := by simpa using hw
    subst y
    subst z
    subst w
    exact (hdist (Or.elim (fun h => (h rfl).elim)
      (fun h => Or.elim (fun h' => (h' rfl).elim)
        (fun h' => (h' rfl).elim)) h)).elim

/-- In an A-linear target, every A-copy carrier is target-closed. -/
theorem targetClosed_copy
    {A : RelStructure L U} {B : RelStructure L V}
    (hLinear : ALinear A B)
    (a : Embedding A B) :
    TargetClosed A B (copyCarrier a) := by
  constructor
  · intro x hx y hy hxy b hxb hyb
    have hsame :=
      sameCopy_of_common_distinct_pair hLinear b a
        hxb hyb hx hy hxy
    intro z hz
    change copyCarrier b = copyCarrier a at hsame
    rw [← hsame]
    exact hz
  · intro x hx y hy z hz _ hno
    exact (hno ⟨a, hx, hy, hz⟩).elim

/-- A target-closed set containing two distinct points is either exactly their
A-copy or the whole target. -/
theorem targetClosed_of_distinct_pair
    {A : RelStructure L U} {B : RelStructure L V}
    {S : Set V}
    (hLinear : ALinear A B)
    (hClosed : TargetClosed A B S)
    {x y : V} (hx : x ∈ S) (hy : y ∈ S) (hxy : x ≠ y) :
    (∃ a : Embedding A B, S = copyCarrier a) ∨
      S = Set.univ := by
  by_cases hpair :
      ∃ a : Embedding A B,
        x ∈ copyCarrier a ∧ y ∈ copyCarrier a
  · rcases hpair with ⟨a, hxa, hya⟩
    have haS : copyCarrier a ⊆ S :=
      hClosed.1 x hx y hy hxy a hxa hya
    by_cases hSa : S ⊆ copyCarrier a
    · exact Or.inl ⟨a, Set.Subset.antisymm hSa haS⟩
    · right
      push Not at hSa
      rcases hSa with ⟨z, hzS, hza⟩
      apply hClosed.2 x hx y hy z hzS (Or.inl hxy)
      intro htriple
      rcases htriple with ⟨b, hxb, hyb, hzb⟩
      have hsame :=
        sameCopy_of_common_distinct_pair hLinear b a
          hxb hyb hxa hya hxy
      apply hza
      change copyCarrier b = copyCarrier a at hsame
      rw [← hsame]
      exact hzb
  · right
    apply hClosed.2 x hx y hy y hy (Or.inl hxy)
    intro htriple
    rcases htriple with ⟨a, hxa, hya, _⟩
    exact hpair ⟨a, hxa, hya⟩

/-- Classification of target-closed sets. -/
theorem targetClosed_classify
    {A : RelStructure L U} {B : RelStructure L V}
    {S : Set V}
    (hLinear : ALinear A B)
    (hClosed : TargetClosed A B S) :
    S.Subsingleton ∨
      (∃ a : Embedding A B, S = copyCarrier a) ∨
      S = Set.univ := by
  by_cases hsub : S.Subsingleton
  · exact Or.inl hsub
  · right
    rw [Set.not_subsingleton_iff] at hsub
    rcases hsub with ⟨x, hx, y, hy, hxy⟩
    exact targetClosed_of_distinct_pair hLinear hClosed hx hy hxy

/-- Nonempty target-closed sets are exactly singletons, A-copy carriers, or
the whole target. -/
theorem targetClosed_classify_nonempty
    {A : RelStructure L U} {B : RelStructure L V}
    {S : Set V}
    (hLinear : ALinear A B)
    (hClosed : TargetClosed A B S)
    (hne : S.Nonempty) :
    (∃ x : V, S = {x}) ∨
      (∃ a : Embedding A B, S = copyCarrier a) ∨
      S = Set.univ := by
  rcases targetClosed_classify hLinear hClosed with hsub | hrest
  · rcases hne with ⟨x, hx⟩
    left
    refine ⟨x, Set.Subset.antisymm ?_ ?_⟩
    · intro y hy
      show y ∈ ({x} : Set V)
      simpa using hsub hy hx
    · rintro y rfl
      exact hx
  · exact Or.inr hrest

end StructuralRamsey.Girth
