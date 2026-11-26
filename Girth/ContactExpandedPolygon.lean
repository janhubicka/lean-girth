import Girth.ContactSideSubdivision
import Girth.ContactBoundary

/-! The expansion of a polygon is a finite cyclic indexing of its
original vertices and the selected fresh inserted wagons.  All geometric
consequences below are proved from the exact indexing conditions.
Constructing this finite indexing with the stated weight equality is
a separate purely combinatorial obligation. -/

namespace StructuralRamsey.Girth
universe v
variable {V E I P U F R V₀ E₀ I₀ P₀ : Type v}

namespace ContactPictureData.SidePlan
variable {D : OrderOneData V E I P} {L : OrderOneData V₀ E₀ I₀ P₀}
    {H : OrderOneData U F (I × I₀) R} {A : ContactPictureData D L H}
    {B : ContactPolygon U R} (S : A.SidePlan B)

/-- Exact index data of the polygon obtained by inserting the chosen
wagon between the endpoints of each split side. There are no other
vertices. The final field is the numeric identity of this subdivision. -/
structure Expansion where
  polygon : ContactPolygon U R
  original : Fin B.length → Fin polygon.length
  inserted : ∀ i p, S.insert i = some p → Fin polygon.length
  original_eq : ∀ i, polygon.vertex (original i) = B.vertex i
  inserted_eq : ∀ i p (h : S.insert i = some p),
    polygon.vertex (inserted i p h) = Sum.inr (A.core.wagon p)
  cover : ∀ k : Fin polygon.length,
    (∃ i, original i = k) ∨ (∃ i p (h : S.insert i = some p), inserted i p h = k)
  direct_next : ∀ i, S.insert i = none →
    cyclicSucc (original i) = original (cyclicSucc i)
  split_first : ∀ i p (h : S.insert i = some p),
    cyclicSucc (original i) = inserted i p h
  split_second : ∀ i p (h : S.insert i = some p),
    cyclicSucc (inserted i p h) = original (cyclicSucc i)
  weight_eq : polygon.twiceWeight = B.twiceWeight

namespace Expansion
variable {S : A.SidePlan B} (X : S.Expansion)

/-- Every side of the expanded polygon has a constituent witness. -/
theorem sides_in_constituents (k : Fin X.polygon.length) :
    ∃ a : I ⊕ E, X.polygon.vertex k ∈ A.constituent a ∧
      X.polygon.vertex (cyclicSucc k) ∈ A.constituent a := by
  rcases X.cover k with ⟨i,rfl⟩ | ⟨i,p,h,rfl⟩
  · cases h : S.insert i with
    | none =>
      obtain ⟨a,ha,ha'⟩ := S.direct i h
      exact ⟨a,by rw [X.original_eq]; exact ha,
        by rw [X.direct_next i h,X.original_eq]; exact ha'⟩
    | some p =>
      obtain ⟨a,b,_,ha,ha',_,_⟩ := S.split_half_sides i p h
      exact ⟨a,by rw [X.original_eq]; exact ha,
        by rw [X.split_first i p h,X.inserted_eq]; exact ha'⟩
  · obtain ⟨a,b,_,_,_,hb,hb'⟩ := S.split_half_sides i p h
    exact ⟨b,by rw [X.inserted_eq]; exact hb,
      by rw [X.split_second i p h,X.original_eq]; exact hb'⟩

/-- The only potential nonconsecutive pair in a wagon trace has been
split because its original endpoints have no common constituent.
This proves exactly the pair fact used by all boundary contradictions. -/
theorem consecutive_trace (hb : B.Bad H.contactClique) :
    A.ConsecutiveTrace X.polygon := by
  classical
  intro p a k l hkl hkw hlw hkc hlc
  have original_pair : ∀ i j : Fin B.length, X.original i ≠ X.original j →
      B.vertex i ∈ H.contactWagonClique (A.core.wagon p) →
      B.vertex j ∈ H.contactWagonClique (A.core.wagon p) →
      B.vertex i ∈ A.constituent a → B.vertex j ∈ A.constituent a →
      cyclicSucc (X.original i) = X.original j ∨
        cyclicSucc (X.original j) = X.original i := by
    intro i j hij hi hj hi' hj'
    have hn : i ≠ j := fun he => hij (congrArg X.original he)
    have hadj : contactAdjacent H.contactClique (B.vertex i) (B.vertex j) :=
      ⟨fun he => hn (B.vertex_injective he),Sum.inr (A.core.wagon p),hi,hj⟩
    rcases B.consecutive_of_no_chord hb.2.2 hn hadj with he | he
    · have hnone : S.insert i = none := by
        cases h : S.insert i with
        | none => rfl
        | some w => exact (S.not_direct i w h ⟨a,hi',by rw [he]; exact hj'⟩).elim
      left
      rw [X.direct_next i hnone,he]
    · have hnone : S.insert j = none := by
        cases h : S.insert j with
        | none => rfl
        | some w => exact (S.not_direct j w h ⟨a,hj',by rw [he]; exact hi'⟩).elim
      right
      rw [X.direct_next j hnone,he]
  have original_inserted : ∀ (i j : Fin B.length) (w : P) (h : S.insert j = some w),
      B.vertex i ∈ H.contactWagonClique (A.core.wagon p) →
      X.polygon.vertex (X.inserted j w h) ∈ H.contactWagonClique (A.core.wagon p) →
      cyclicSucc (X.original i) = X.inserted j w h ∨
        cyclicSucc (X.inserted j w h) = X.original i := by
    intro i j w h hi hj
    rw [X.inserted_eq] at hj
    have he : w = p := A.core.wagon.injective (show A.core.wagon w = A.core.wagon p from hj)
    subst w
    rcases S.split_wagon_trace hb j p h i hi with he | he
    · left
      rw [he]
      exact X.split_first j p h
    · right
      rw [he]
      exact X.split_second j p h
  rcases X.cover k with ⟨i,rfl⟩ | ⟨i,w,hi,rfl⟩
  · rcases X.cover l with ⟨j,rfl⟩ | ⟨j,w,hj,rfl⟩
    · rw [X.original_eq] at hkw hlw hkc hlc
      exact original_pair i j hkl hkw hlw hkc hlc
    · rw [X.original_eq] at hkw
      exact original_inserted i j w hj hkw hlw
  · rcases X.cover l with ⟨j,rfl⟩ | ⟨j,w',hj,rfl⟩
    · rw [X.original_eq] at hlw
      rcases original_inserted j i w hi hlw hkw with he | he
      · exact Or.inr he
      · exact Or.inl he
    · rw [X.inserted_eq] at hkw hlw
      have he : w = p := A.core.wagon.injective (show A.core.wagon w = A.core.wagon p from hkw)
      have he' : w' = p := A.core.wagon.injective (show A.core.wagon w' = A.core.wagon p from hlw)
      subst w
      subst w'
      have hij := S.split_injective hb i j p hi hj
      subst j
      exact (hkl rfl).elim

theorem not_in_wagon (hb : B.Bad H.contactClique) (p : P) :
    ¬ ∀ k, X.polygon.vertex k ∈ H.contactWagonClique (A.core.wagon p) := by
  intro h
  apply hb.2.1
  refine ⟨Sum.inr (A.core.wagon p),?_⟩
  intro i
  rw [← X.original_eq i]
  exact h (X.original i)

theorem not_in_constituent {q : ℕ}
    (C : ContactPictureCopies A) (h1 : D.ContactG1) (h2 : D.ContactG2)
    (htwo : ∀ i r x y, x ≠ y → x ∈ A.standard i → y ∈ A.standard i →
      x ∈ H.contactWagonCarrier r → y ∈ H.contactWagonCarrier r → A.meets i r)
    (h4 : ContactG4 L.contactClique q) (hw : B.twiceWeight ≤ 2*q)
    (hb : B.Bad H.contactClique) (a : I ⊕ E) :
    ¬ ∀ k, X.polygon.vertex k ∈ A.constituent a := by
  intro h
  cases a with
  | inl i =>
    apply C.bad_not_in_standard h1 h2 htwo h4 B hw hb i
    intro j
    rw [← X.original_eq j]
    exact h (X.original j)
  | inr e =>
    apply X.not_in_wagon hb (D.parent e)
    intro k
    exact A.enlarged_edge_subset_wagon e (h k)

/-- Construct actual incoming-side owners and then maximal segments.
There is no segmentation hypothesis in the resulting theorem. -/
noncomputable def segments {q : ℕ}
    (C : ContactPictureCopies A) (h1 : D.ContactG1) (h2 : D.ContactG2)
    (htwo : ∀ i r x y, x ≠ y → x ∈ A.standard i → y ∈ A.standard i →
      x ∈ H.contactWagonCarrier r → y ∈ H.contactWagonCarrier r → A.meets i r)
    (h4 : ContactG4 L.contactClique q) (hw : B.twiceWeight ≤ 2*q)
    (hb : B.Bad H.contactClique) :
    ContactRunSegments X.polygon.vertex A.constituent := by
  classical
  choose out hout using X.sides_in_constituents
  let prev : Fin X.polygon.length → Fin X.polygon.length :=
    fun i => Classical.choose (contactSucc_surjective i)
  have hp : ∀ i, cyclicSucc (prev i) = i :=
    fun i => Classical.choose_spec (contactSucc_surjective i)
  let owner : Fin X.polygon.length → I ⊕ E := fun i => out (prev i)
  have hm : ∀ k, X.polygon.vertex k ∈ A.constituent (owner k) ∧
      X.polygon.vertex k ∈ A.constituent (owner (cyclicSucc k)) := by
    intro k
    constructor
    · have h := (hout (prev k)).2
      rw [hp] at h
      exact h
    · change X.polygon.vertex k ∈ A.constituent (out (prev (cyclicSucc k)))
      have he : prev (cyclicSucc k) = k :=
        ContactCyclicRestriction.contactCyclicSucc_injective (hp (cyclicSucc k))
      rw [he]
      exact (hout k).1
  have hn : ¬ ∃ a, ∀ k, owner k = a := by
    rintro ⟨a,ha⟩
    apply X.not_in_constituent C h1 h2 htwo h4 hw hb a
    intro k
    have h := (hm k).1
    rw [ha k] at h
    exact h
  exact contactSegments_of_owners (by have := X.polygon.hlength; omega)
    owner X.polygon.vertex A.constituent hm hn

/-- The positive-core case of G4 preservation, once the pure finite
subdivision indexing has been constructed. This calls the actual
maximal-run enumeration and the full boundary contradiction. -/
theorem false_of_core_G4 {q : ℕ}
    (C : ContactPictureCopies A) (hlin : D.ContactLinear)
    (h1 : D.ContactG1) (h2 : D.ContactG2)
    (htwo : ∀ i r x y, x ≠ y → x ∈ A.standard i → y ∈ A.standard i →
      x ∈ H.contactWagonCarrier r → y ∈ H.contactWagonCarrier r → A.meets i r)
    (h4core : ContactG4 D.contactClique q) (h4local : ContactG4 L.contactClique q)
    (hw : B.twiceWeight ≤ 2*q) (hb : B.Bad H.contactClique) : False := by
  apply A.boundary_contradiction_of_G4 hlin h2 h4core X.polygon
    (X.segments C h1 h2 htwo h4local hw hb)
  · rw [X.weight_eq]
    exact hw
  · exact X.consecutive_trace hb
  · exact X.not_in_constituent C h1 h2 htwo h4local hw hb
  · exact X.not_in_wagon hb

end Expansion
end ContactPictureData.SidePlan
end StructuralRamsey.Girth
