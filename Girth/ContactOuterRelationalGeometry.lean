import Girth.ContactQualitativeCompletion
import Girth.ContactJoinTreeCharacterization
import Girth.ContactIsolatedPadding

/-! The conformality argument in the relational restoration.
Three designated bags suffice: a minimal uncovered clique has
three one-point deletion witnesses, and their completion is a join tree.
This proof does not assume that the ambient family has a join tree. -/

namespace StructuralRamsey.Girth
universe v
variable {V I E : Type v}

/-- The two-section of a family with qualitative completion through
three is conformal. The completion may use arbitrarily many other
members; the conclusion concerns the original family. -/
theorem contact_conformal_of_threeCompletable (F : I → Set V)
    (hComp : ContactCompletable F 3) : ContactConformal F := by
  classical
  intro s hs hv hp
  have aux : ∀ n : ℕ, ∀ s : Finset V, s.card = n → s.Nonempty →
      (∀ x ∈ s, ∃ i, x ∈ F i) →
      (∀ x ∈ s, ∀ y ∈ s, x ≠ y → ∃ i, x ∈ F i ∧ y ∈ F i) →
      ∃ i, (↑s : Set V) ⊆ F i := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro s hn hs hv hp
      obtain ⟨x,hx⟩ := hs
      by_cases hone : ∀ y ∈ s, y = x
      · obtain ⟨i,hi⟩ := hv x hx
        exact ⟨i,fun y hy => (hone y hy).symm ▸ hi⟩
      push_neg at hone
      obtain ⟨y,hy,hyx⟩ := hone
      by_cases htwo : ∀ z ∈ s, z = x ∨ z = y
      · obtain ⟨i,hxi,hyi⟩ := hp x hx y hy hyx.symm
        refine ⟨i,?_⟩
        intro z hz
        rcases htwo z hz with rfl | rfl
        · exact hxi
        · exact hyi
      push_neg at htwo
      obtain ⟨z,hz,hzx,hzy⟩ := htwo
      have deletion (w : V) (hw : w ∈ s) (u : V) (hu : u ∈ s) (huw : u ≠ w) :
          ∃ i, (↑(s.erase w) : Set V) ⊆ F i := by
        apply ih (s.erase w).card (by rw [← hn]; exact Finset.card_erase_lt_of_mem hw)
          (s.erase w) rfl ⟨u,Finset.mem_erase.mpr ⟨huw,hu⟩⟩
        · intro a ha
          exact hv a (Finset.mem_of_mem_erase ha)
        · intro a ha b hb hab
          exact hp a (Finset.mem_of_mem_erase ha) b (Finset.mem_of_mem_erase hb) hab
      obtain ⟨i,hi⟩ := deletion x hx y hy hyx
      obtain ⟨j,hj⟩ := deletion y hy z hz hzy
      obtain ⟨k,hk⟩ := deletion z hz x hx hzx.symm
      let t₀ : Finset I := {i,j,k}
      have ht₀ : t₀.Nonempty := ⟨i,by simp [t₀]⟩
      have htcard : t₀.card ≤ 3 := by
        calc
          t₀.card ≤ ({j,k} : Finset I).card + 1 := Finset.card_insert_le _ _
          _ ≤ ({k} : Finset I).card + 1 + 1 := by
            have h := Finset.card_insert_le j ({k} : Finset I)
            omega
          _ = 3 := by simp
      obtain ⟨t,ht,⟨J⟩⟩ := hComp t₀ ht₀ htcard
      let i' : {a : I // a ∈ t} := ⟨i,ht (by simp [t₀])⟩
      let j' : {a : I // a ∈ t} := ⟨j,ht (by simp [t₀])⟩
      let k' : {a : I // a ∈ t} := ⟨k,ht (by simp [t₀])⟩
      have hv' (u : V) (hu : u ∈ s) : ∃ a : {a : I // a ∈ t}, u ∈ F a.val := by
        by_cases hux : u = x
        · exact ⟨j',hj (Finset.mem_erase.mpr ⟨fun h => hyx (h.symm.trans hux),hu⟩)⟩
        · exact ⟨i',hi (Finset.mem_erase.mpr ⟨hux,hu⟩)⟩
      have hp' (u : V) (hu : u ∈ s) (w : V) (hw : w ∈ s) (_ : u ≠ w) :
          ∃ a : {a : I // a ∈ t}, u ∈ F a.val ∧ w ∈ F a.val := by
        by_cases hxi : u ≠ x ∧ w ≠ x
        · exact ⟨i',hi (Finset.mem_erase.mpr ⟨hxi.1,hu⟩),hi (Finset.mem_erase.mpr ⟨hxi.2,hw⟩)⟩
        by_cases hyj : u ≠ y ∧ w ≠ y
        · exact ⟨j',hj (Finset.mem_erase.mpr ⟨hyj.1,hu⟩),hj (Finset.mem_erase.mpr ⟨hyj.2,hw⟩)⟩
        have hh : u ≠ z ∧ w ≠ z := by
          by_contra hn
          have either (p : V) (h : ¬ (u ≠ p ∧ w ≠ p)) : u = p ∨ w = p := by
            by_cases hu : u = p
            · exact Or.inl hu
            · exact Or.inr (by by_contra hw; exact h ⟨hu,hw⟩)
          rcases either x hxi with h | h <;> rcases either y hyj with h' | h' <;>
            rcases either z hn with h'' | h'' <;> subst_vars <;> contradiction
        exact ⟨k',hk (Finset.mem_erase.mpr ⟨hh.1,hu⟩),hk (Finset.mem_erase.mpr ⟨hh.2,hw⟩)⟩
      obtain ⟨a,ha⟩ := J.conformal s ⟨x,hx⟩ hv' hp'
      exact ⟨a.val,ha⟩
  exact aux s.card s rfl hs hv hp

/-- Private padding preserves all previously allowed intersections. -/
theorem ContactDesignatedEmbeddings.padded_pairwise
    {U F J : Type v} {D : ContactHypergraphData V E I}
    {H : ContactHypergraphData U F J} {T : ContactTrainData E 1}
    {S : ContactTrainData F 1}
    (M : ContactDesignatedEmbeddings D.trimIsolated T H S)
    (h : H.bottomCut.ZeroPairwise) :
    M.paddedGraph.bottomCut.ZeroPairwise := by
  intro a b hne
  rw [M.padded_piece_intersection a b hne]
  rcases h a b hne with hs | ⟨e,ha,hb,he⟩
  · exact Or.inl (contact_image_subsingleton M.paddedCore hs)
  · exact Or.inr ⟨e,ha,hb,congrArg (fun s : Set U => M.paddedCore '' s) he⟩

/-- The same tree on the same chosen labels remains a join tree
after padding, even for completions much larger than the local cutoff. -/
theorem ContactDesignatedEmbeddings.padded_joinTree
    {U F J K : Type v} {D : ContactHypergraphData V E I}
    {H : ContactHypergraphData U F J} {T : ContactTrainData E 1}
    {S : ContactTrainData F 1}
    (M : ContactDesignatedEmbeddings D.trimIsolated T H S)
    (sel : K ↪ (J ⊕ F))
    (J₀ : ContactJoinTree (fun a : K => H.bottomCut.carrier (sel a))) :
    Nonempty (ContactJoinTree (fun a : K => M.paddedGraph.bottomCut.carrier (sel a))) := by
  let U₀ := J₀.mapVertices M.paddedCore
  have he : (fun a : K =>
      M.paddedGraph.bottomCut.carrier (sel a) ∩ Set.range M.paddedCore) =
      (fun a : K => M.paddedCore '' H.bottomCut.carrier (sel a)) :=
    funext (fun a => M.padded_piece_trace (sel a))
  let U₁ : ContactJoinTree (fun a : K =>
      M.paddedGraph.bottomCut.carrier (sel a) ∩ Set.range M.paddedCore) := he.symm ▸ U₀
  refine ⟨U₁.restoreOutside ?_⟩
  intro x hx a ha b hb
  by_contra hn
  exact hx (M.padded_piece_shared (sel a) (sel b)
    (fun h => hn (sel.injective h)) x ha hb)

end StructuralRamsey.Girth
