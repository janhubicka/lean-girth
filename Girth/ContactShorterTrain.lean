import Girth.ContactParentMap
import Girth.ContactWagonPadding
import Girth.ContactRefinementGirth

/-! The actual shorter train in the cutoff-two construction.
Its edges are the old first wagon labels, padded to the common
template. Higher wagon labels and all their incidences on original
vertices are inherited from the original train. -/

namespace StructuralRamsey.Girth
universe v
variable {V E I X : Type v}

namespace ContactTrainData
variable {m : ℕ} (T : ContactTrainData E (m+1))

abbrev FirstWagon := T.Wagon (0 : Fin (m+1)).succ

/-- Every higher wagon has an actual first wagon as descendant. -/
noncomputable def shorterParent (μ : Fin (m+1)) (p : T.FirstWagon) :
    T.Wagon μ.succ :=
  T.parentMap (0 : Fin (m+1)).succ μ.succ (by
    change 1 ≤ μ.val+1
    omega) p

theorem shorterParent_first (μ : Fin (m+1)) (e : E) :
    T.shorterParent μ (T.parent (0 : Fin (m+1)).succ e) = T.parent μ.succ e :=
  T.parentMap_parent _ _ _ e

/-- Drop the first cut, with first wagons becoming the edges.
At the new bottom their labels are unchanged, so equality is
still exactly the bottom equivalence. -/
noncomputable def shorterTrain : ContactTrainData T.FirstWagon m where
  Wagon := fun μ => T.Wagon μ.succ
  parent := T.shorterParent
  surj := by
    intro μ p
    obtain ⟨e,he⟩ := T.surj μ.succ p
    exact ⟨T.parent (0 : Fin (m+1)).succ e,(T.shorterParent_first μ e).trans he⟩
  nested := by
    intro μ ν h p r he
    obtain ⟨e,he'⟩ := T.surj (0 : Fin (m+1)).succ p
    obtain ⟨f,hf'⟩ := T.surj (0 : Fin (m+1)).succ r
    subst p
    subst r
    change T.shorterParent μ _ = T.shorterParent μ _ at he
    change T.shorterParent ν _ = T.shorterParent ν _
    rw [T.shorterParent_first,T.shorterParent_first] at he ⊢
    exact T.nested μ.succ ν.succ (by
      change μ.val+1 ≤ ν.val+1
      exact Nat.succ_le_succ h) e f he
  bottom := by
    intro p r he
    obtain ⟨e,he'⟩ := T.surj (0 : Fin (m+1)).succ p
    obtain ⟨f,hf'⟩ := T.surj (0 : Fin (m+1)).succ r
    subst p
    subst r
    exact (T.shorterParent_first 0 e).symm.trans (he.trans (T.shorterParent_first 0 f))
  top := by
    intro p r
    obtain ⟨e,he⟩ := T.surj (0 : Fin (m+1)).succ p
    obtain ⟨f,hf⟩ := T.surj (0 : Fin (m+1)).succ r
    subst p
    subst r
    change T.shorterParent ⟨m,by omega⟩ _ = T.shorterParent ⟨m,by omega⟩ _
    rw [T.shorterParent_first,T.shorterParent_first]
    exact T.top e f

theorem shorterTrain_parent_first (μ : Fin (m+1)) (e : E) :
    T.shorterTrain.parent μ (T.parent (0 : Fin (m+1)).succ e) =
      T.parent μ.succ e :=
  T.shorterParent_first μ e

theorem shorterParent_zero (p : T.FirstWagon) :
    T.shorterParent 0 p = p := by
  obtain ⟨e,rfl⟩ := T.surj (0 : Fin (m+1)).succ p
  exact T.shorterParent_first 0 e

end ContactTrainData

namespace ContactWagonPadding
variable {m : ℕ} {D : ContactHypergraphData V E I}
    {T : ContactTrainData E (m+1)}
    (A : ContactWagonPadding
      (D.atCut (T.parent (0 : Fin (m+1)).succ)).contactWagonCarrier X)

theorem original_union_eq (μ : Fin (m+1)) (p : T.Wagon μ.succ) :
    A.oldUnionCarrier (T.shorterParent μ) p =
      (D.atCut (T.parent μ.succ)).contactWagonCarrier p := by
  ext x
  constructor
  · rintro ⟨r,hr,e,he,hx⟩
    refine ⟨e,?_,hx⟩
    exact (T.shorterParent_first μ e).symm.trans
      ((congrArg (T.shorterParent μ) he).trans hr)
  · rintro ⟨e,he,hx⟩
    exact ⟨T.parent (0 : Fin (m+1)).succ e,
      (T.shorterParent_first μ e).trans he,e,rfl,hx⟩

theorem shorter_carrier_eq (μ : Fin (m+1)) (p : T.Wagon μ.succ) :
    (A.paddedHypergraph.atCut (T.shorterTrain.parent μ)).contactWagonCarrier p =
      A.unionCarrier (T.shorterParent μ) p := rfl

/-- Girth of the shorter train at every proper cut is exactly
inherited from the corresponding positive cut of the old train.
No girth hypothesis on the newly constructed carrier family. -/
theorem shorter_wagonGirth (μ : Fin (m+1)) {g : ℕ}
    (hg : LabelledGirthGT (D.atCut (T.parent μ.succ)).contactWagonCarrier g) :
    LabelledGirthGT
      (A.paddedHypergraph.atCut (T.shorterTrain.parent μ)).contactWagonCarrier g := by
  rw [A.shorter_carrier_eq μ]
  have he : A.oldUnionCarrier (T.shorterParent μ) =
      (D.atCut (T.parent μ.succ)).contactWagonCarrier := by
    funext p
    exact A.original_union_eq μ p
  apply A.union_girth
  rw [he]
  exact hg

theorem shorter_wagonBounds (q : Fin (m+1) → ℕ)
    (hg : ∀ μ : Fin (m+1), μ.val < m →
      LabelledGirthGT (D.atCut (T.parent μ.succ)).contactWagonCarrier (q μ)) :
    A.paddedHypergraph.WagonBounds T.shorterTrain q :=
  fun μ h => A.shorter_wagonGirth μ (hg μ h)

/-- The padded edge family is linear if the original first wagons
are linear; private positions introduce no new intersections. -/
theorem shorter_linear
    (hlin : ∀ p r : T.FirstWagon, p ≠ r →
      ((D.atCut (T.parent (0 : Fin (m+1)).succ)).contactWagonCarrier p ∩
        (D.atCut (T.parent (0 : Fin (m+1)).succ)).contactWagonCarrier r).Subsingleton) :
    ∀ p r : T.FirstWagon, p ≠ r →
      (A.paddedHypergraph.edgeCarrier p ∩ A.paddedHypergraph.edgeCarrier r).Subsingleton := by
  intro p r hne x hx y hy
  change x ∈ A.padded p ∩ A.padded r at hx
  change y ∈ A.padded p ∩ A.padded r at hy
  rw [A.padded_intersection p r hne] at hx hy
  obtain ⟨u,hu,rfl⟩ := hx
  obtain ⟨v,hv,rfl⟩ := hy
  exact congrArg A.oldVertex (hlin p r hne hu hv)

/-- Parameters at all retained levels transfer via the original
shared vertex. Distinct padded edges meet only at a point which
was already in the corresponding two first wagons. -/
theorem shorter_parameter (μ ν : Fin (m+1)) (allowed : Set V)
    (h : D.Parameter T μ.succ ν.succ allowed) :
    A.paddedHypergraph.Parameter T.shorterTrain μ ν (A.oldVertex '' allowed) := by
  intro p r x hpar hx hy hnot
  by_cases he : p = r
  · subst r
    rfl
  · change x ∈ A.padded p at hx
    change x ∈ A.padded r at hy
    have hm : x ∈ A.padded p ∩ A.padded r := ⟨hx,hy⟩
    rw [A.padded_intersection p r he] at hm
    obtain ⟨z,⟨⟨e,he',hze⟩,⟨f,hf',hzf⟩⟩,rfl⟩ := hm
    change T.parent (0 : Fin (m+1)).succ e = p at he'
    change T.parent (0 : Fin (m+1)).succ f = r at hf'
    subst p
    subst r
    change T.shorterParent ν _ = T.shorterParent ν _ at hpar
    rw [T.shorterParent_first,T.shorterParent_first] at hpar
    change T.shorterParent μ _ = T.shorterParent μ _
    rw [T.shorterParent_first,T.shorterParent_first]
    exact h e f z hpar hze hzf (fun hz => hnot ⟨z,hz,rfl⟩)

end ContactWagonPadding
end StructuralRamsey.Girth
