import Girth.ContactComparisonGraph
import Girth.SupportedTree

/-! Necessity in the small-induced-substructure criterion.
Each construction step freely adjoins an ordered copy of B. Every new
vertex has all its neighbours in that clique, so a cycle of length at
least four through a new vertex has a chord between its neighbours. -/

namespace StructuralRamsey.Girth
open StructuralRamsey.RelStructure
universe u v
variable {L : RelLanguage.{u}} {U V W X : Type v}

private theorem contactSucc_cube_ne {n : ℕ} (hn : 4 ≤ n) (i : Fin n) :
    cyclicSucc (cyclicSucc (cyclicSucc i)) ≠ i := by
  intro he
  have hv := congrArg Fin.val he
  have h0 := contactSucc_value i
  have h1 := contactSucc_value (cyclicSucc i)
  have h2 := contactSucc_value (cyclicSucc (cyclicSucc i))
  have hi := i.isLt
  have hs := (cyclicSucc i).isLt
  have ht := (cyclicSucc (cyclicSucc i)).isLt
  split_ifs at h0 h1 h2 <;> omega

theorem contactChordal_of_complete {G : SimpleGraph W}
    (h : ∀ x y, x ≠ y → G.Adj x y) : ContactChordal G := by
  intro n z hn hi _
  let a : Fin n := ⟨0,by omega⟩
  let b : Fin n := ⟨2,by omega⟩
  have hab : a ≠ b := by intro h; have := congrArg Fin.val h; dsimp [a,b] at this; omega
  refine ⟨a,b,hab,?_,?_,h _ _ (fun he => hab (hi he))⟩
  · intro he
    have hv := congrArg Fin.val he
    rw [contactSucc_value] at hv
    change (if 0+1 < n then 0+1 else 0) = 2 at hv
    rw [ite_eq_left (by omega)] at hv
    omega
  · intro he
    have hv := congrArg Fin.val he
    rw [contactSucc_value] at hv
    change (if 2+1 < n then 2+1 else 0) = 0 at hv
    rw [ite_eq_left (by omega)] at hv
    omega

/-- Adjoining a clique freely to an induced chordal subgraph preserves
chordality. The overlap size and the finiteness of the vertex sets are irrelevant. -/
theorem contactChordal_cliqueExtension
    {H : SimpleGraph V} {G : SimpleGraph W} (f : V ↪ W)
    (hf : ∀ x y, G.Adj (f x) (f y) ↔ H.Adj x y)
    (hH : ContactChordal H) (Q : Set W) (hQ : ContactClique G Q)
    (hside : ∀ x y, G.Adj x y →
      (x ∈ Set.range f ∧ y ∈ Set.range f) ∨ (x ∈ Q ∧ y ∈ Q)) :
    ContactChordal G := by
  classical
  intro n z hn hi hs
  by_cases hall : ∀ i, z i ∈ Set.range f
  · choose p hp using hall
    have hpInj : Function.Injective p := by
      intro i j he
      apply hi
      rw [← hp i,← hp j,he]
    obtain ⟨i,j,hij,h1,h2,hadj⟩ := hH n p hn hpInj (by
      intro i
      apply (hf _ _).mp
      rw [hp i,hp (cyclicSucc i)]
      exact hs i)
    exact ⟨i,j,hij,h1,h2,by simpa only [hp] using (hf _ _).mpr hadj⟩
  · push Not at hall
    obtain ⟨i,hiOld⟩ := hall
    obtain ⟨j,hj⟩ := contactSucc_surjective i
    let k := cyclicSucc i
    have hjk : j ≠ k := by
      intro he
      have h := contactSucc_sq_ne (show 3 ≤ n by omega) j
      rw [hj] at h
      exact h he.symm
    have hjk' : cyclicSucc j ≠ k := by
      rw [hj]
      exact (contactSucc_ne (show 2 ≤ n by omega) i).symm
    have hkj : cyclicSucc k ≠ j := by
      have h := contactSucc_cube_ne hn j
      simpa only [hj,k] using h
    have hjQ : z j ∈ Q := by
      rcases hside _ _ (hs j) with hleft | hright
      · exact (hiOld (hj ▸ hleft.2)).elim
      · exact hright.1
    have hkQ : z k ∈ Q := by
      rcases hside _ _ (hs i) with hleft | hright
      · exact (hiOld hleft.1).elim
      · exact hright.2
    exact ⟨j,k,hjk,hjk',hkj,hQ _ hjQ _ hkQ (fun he => hjk (hi he))⟩

theorem contactComparisonGraph_freeAmalgam_side
    {D : RelStructure L.withOrder U} {C₀ : RelStructure L.withOrder V}
    {B : RelStructure L.withOrder W} {C : RelStructure L.withOrder X}
    {f₀ : Embedding D C₀} {fB : Embedding D B}
    {i₀ : Embedding C₀ C} {iB : Embedding B C}
    (hfree : IsFreeAmalgam f₀ fB i₀ iB) (x y : X)
    (h : (contactComparisonGraph C).Adj x y) :
    (x ∈ Set.range i₀ ∧ y ∈ Set.range i₀) ∨
      (x ∈ Set.range iB ∧ y ∈ Set.range iB) := by
  have aux (a b : X) (hab : C.rel (.inr ()) ![a,b]) :
      (a ∈ Set.range i₀ ∧ b ∈ Set.range i₀) ∨
        (a ∈ Set.range iB ∧ b ∈ Set.range iB) := by
    rcases (hfree.rel_iff (.inr ()) ![a,b]).mp hab with ⟨p,_,he⟩ | ⟨p,_,he⟩
    · exact Or.inl ⟨⟨p (0 : Fin 2),(congrFun he (0 : Fin 2)).symm⟩,
        ⟨p (1 : Fin 2),(congrFun he (1 : Fin 2)).symm⟩⟩
    · exact Or.inr ⟨⟨p (0 : Fin 2),(congrFun he (0 : Fin 2)).symm⟩,
        ⟨p (1 : Fin 2),(congrFun he (1 : Fin 2)).symm⟩⟩
  rcases h.2 with hxy | hyx
  · exact aux x y hxy
  · rcases aux y x hyx with hleft | hright
    · exact Or.inl hleft.symm
    · exact Or.inr hright.symm

theorem contactComparisonGraph_freeAmalgam_chordal
    {D : RelStructure L.withOrder U} {C₀ : RelStructure L.withOrder V}
    {B : RelStructure L W} [LinearOrder W] {C : RelStructure L.withOrder X}
    {f₀ : Embedding D C₀} {fB : Embedding D B.ordered}
    {i₀ : Embedding C₀ C} {iB : Embedding B.ordered C}
    (hfree : IsFreeAmalgam f₀ fB i₀ iB)
    (hC₀ : ContactChordal (contactComparisonGraph C₀)) :
    ContactChordal (contactComparisonGraph C) :=
  contactChordal_cliqueExtension ⟨i₀,i₀.injective⟩
    (contactComparisonGraph_embedding i₀) hC₀ (Set.range iB)
    (contactComparisonGraph_embedding_ordered iB)
    (contactComparisonGraph_freeAmalgam_side hfree)

/-- Every supported tree amalgam of ordered B-copies has a chordal
comparison graph. No extra ordering on the amalgam is assumed. -/
theorem ASupportedTreeAmalgam.comparison_chordal
    {A : RelStructure L.withOrder U} {B : RelStructure L V} [LinearOrder V]
    {T : RelStructure L.withOrder W} (hT : ASupportedTreeAmalgam A B.ordered W T) :
    ContactChordal (contactComparisonGraph T) := by
  induction hT with
  | copy h =>
      apply contactChordal_of_complete
      intro x y hne
      obtain ⟨a,rfl⟩ := h.toEquiv.surjective x
      obtain ⟨b,rfl⟩ := h.toEquiv.surjective y
      exact (contactComparisonGraph_embedding h.toEmbedding a b).mpr
        ((contactComparisonGraph_ordered_adj B a b).mpr
          (fun he => hne (congrArg h.toEquiv he)))
  | glueA _ _ _ _ _ hfree ih =>
      exact contactComparisonGraph_freeAmalgam_chordal hfree ih
  | gluePoint _ _ _ _ _ _ _ hfree ih =>
      exact contactComparisonGraph_freeAmalgam_chordal hfree ih

/-- Necessity in the manuscript's chordality criterion, for any induced
embedding into the tree amalgam, including the empty source. -/
theorem contactComparisonGraph_chordal_of_supportedTree_embedding
    {A : RelStructure L.withOrder U} {B : RelStructure L V} [LinearOrder V]
    {C : RelStructure L.withOrder W} {T : RelStructure L.withOrder X}
    (e : Embedding C T) (hT : ASupportedTreeAmalgam A B.ordered X T) :
    ContactChordal (contactComparisonGraph C) :=
  contactComparisonGraph_chordal_of_embedding e hT.comparison_chordal

end StructuralRamsey.Girth
