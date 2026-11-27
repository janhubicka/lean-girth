import Girth.ContactJoinTreeCharacterization
import Girth.ContactJoinTreeLift

/-! Small local families with repeated labels and short auxiliary
traces. The chordal/conformal characterization lets us pass from
a family of distinct old members to its repeated occurrences and
added singleton/empty members without explicitly adding leaves. -/

namespace StructuralRamsey.Girth
universe v
variable {V I K : Type v}

/-- If the nontrivial members of a finite family are taken from a
family with a join tree, and every member of that latter family is
represented, adding short members or repetitions preserves the
existence of a join tree on the actual indices. -/
theorem contact_joinTree_of_repeated_short [Fintype V] [Fintype I]
    [Fintype K] [Nonempty K]
    (F : K → Set V) (G : I → Set V) (T : ContactJoinTree G)
    (hF : ∀ k, (F k).Subsingleton ∨ ∃ i, F k = G i)
    (hG : ∀ i, ∃ k, F k = G i) :
    Nonempty (ContactJoinTree F) := by
  classical
  have hgraph : contactFamilyGraph F = contactFamilyGraph G := by
    ext x y
    constructor
    · rintro ⟨hne,k,hx,hy⟩
      rcases hF k with hs | ⟨i,hi⟩
      · exact (hne (hs hx hy)).elim
      · exact ⟨hne,i,hi ▸ hx,hi ▸ hy⟩
    · rintro ⟨hne,i,hx,hy⟩
      obtain ⟨k,hk⟩ := hG i
      exact ⟨hne,k,hk.symm ▸ hx,hk.symm ▸ hy⟩
  apply contact_joinTree_of_chordal_conformal
  · rw [hgraph]
    exact T.chordal
  · intro s hs hv hp
    by_cases hsub : (↑s : Set V).Subsingleton
    · obtain ⟨x,hx⟩ := hs
      obtain ⟨k,hk⟩ := hv x hx
      refine ⟨k,?_⟩
      intro y hy
      exact (hsub hx hy) ▸ hk
    · have hpair : ∀ x ∈ s, ∀ y ∈ s, x ≠ y →
          ∃ i, x ∈ G i ∧ y ∈ G i := by
        intro x hx y hy hne
        obtain ⟨k,hx,hy⟩ := hp x hx y hy hne
        rcases hF k with hs | ⟨i,hi⟩
        · exact (hne (hs hx hy)).elim
        · exact ⟨i,hi ▸ hx,hi ▸ hy⟩
      have hvertex : ∀ x ∈ s, ∃ i, x ∈ G i := by
        intro x hx
        obtain ⟨u,hu,w,hw,huw⟩ := Set.not_subsingleton_iff.mp hsub
        by_cases hxu : x = u
        · have hxw : x ≠ w := fun he => huw (hxu.symm.trans he)
          obtain ⟨i,hi,_⟩ := hpair x hx w hw hxw
          exact ⟨i,hi⟩
        · obtain ⟨i,hi,_⟩ := hpair x hx u hu hxu
          exact ⟨i,hi⟩
      obtain ⟨i,hi⟩ := T.conformal s hs hvertex hpair
      obtain ⟨k,hk⟩ := hG i
      exact ⟨k,by rw [hk]; exact hi⟩

/-- A family of only short members has a join tree; all its edges
are absent and every nonempty clique is a singleton. -/
theorem contact_joinTree_of_all_short [Fintype V] [Fintype K] [Nonempty K]
    (F : K → Set V) (hF : ∀ k, (F k).Subsingleton) :
    Nonempty (ContactJoinTree F) := by
  apply contact_joinTree_of_chordal_conformal
  · intro n z hn hInj hs
    let k : Fin n := ⟨0,by omega⟩
    obtain ⟨hne,i,hx,hy⟩ := hs k
    exact (hne (hF i hx hy)).elim
  · intro s hs hv hp
    obtain ⟨x,hx⟩ := hs
    obtain ⟨i,hi⟩ := hv x hx
    refine ⟨i,?_⟩
    intro y hy
    have he : y = x := by
      by_contra hne
      obtain ⟨k,hyk,hxk⟩ := hp y hy x hx hne
      exact hne (hF k hyk hxk)
    simpa only [he] using hi

/-- The local budget is counted on actual auxiliary occurrences,
before discarding duplicates. A small-family join-tree property
of the old system therefore suffices for all local completions. -/
theorem contact_localCompletion [Fintype V] [Fintype K] [Nonempty K]
    (F : K → Set V) (G : I → Set V) (q : ℕ)
    (hcard : Fintype.card K ≤ q)
    (hlocal : ∀ s : Finset I, s.Nonempty → s.card ≤ q →
      Nonempty (ContactJoinTree (fun i : {i // i ∈ s} => G i.val)))
    (hF : ∀ k, (F k).Subsingleton ∨ ∃ i, F k = G i) :
    Nonempty (ContactJoinTree F) := by
  classical
  by_cases hshort : ∀ k, (F k).Subsingleton
  · exact contact_joinTree_of_all_short F hshort
  · push_neg at hshort
    obtain ⟨k₀,hk₀'⟩ := hshort
    have hk₀ : ¬ (F k₀).Subsingleton := Set.not_subsingleton_iff.mpr hk₀'
    let L := {k : K // ¬ (F k).Subsingleton}
    letI : Fintype L := Fintype.ofFinite L
    have hex : ∀ k : L, ∃ i, F k.val = G i := by
      intro k
      rcases hF k.val with hs | hs
      · exact (k.property hs).elim
      · exact hs
    choose chooseLabel hlabel using hex
    let s : Finset I := Finset.univ.image chooseLabel
    have hs : s.Nonempty :=
      ⟨chooseLabel ⟨k₀,hk₀⟩,Finset.mem_image.mpr ⟨⟨k₀,hk₀⟩,Finset.mem_univ _,rfl⟩⟩
    have hle : s.card ≤ q := by
      calc
        s.card ≤ (Finset.univ : Finset L).card := Finset.card_image_le
        _ = Fintype.card L := Finset.card_univ
        _ ≤ Fintype.card K := Fintype.card_le_of_injective
          (fun k : L => k.val) Subtype.val_injective
        _ ≤ q := hcard
    obtain ⟨T⟩ := hlocal s hs hle
    apply contact_joinTree_of_repeated_short F (fun i : {i // i ∈ s} => G i.val) T
    · intro k
      by_cases hk : (F k).Subsingleton
      · exact Or.inl hk
      · let j : L := ⟨k,hk⟩
        exact Or.inr ⟨⟨chooseLabel j,Finset.mem_image.mpr
          ⟨j,Finset.mem_univ _,rfl⟩⟩,hlabel j⟩
    · intro i
      obtain ⟨k,_,hk⟩ := Finset.mem_image.mp i.property
      exact ⟨k.val,(hlabel k).trans (congrArg G hk)⟩

end StructuralRamsey.Girth
