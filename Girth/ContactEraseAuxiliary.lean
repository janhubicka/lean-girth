import Girth.ContactEraseNode
import Girth.ContactEdgeTraces

/-! Erasing auxiliary nodes in the direct forest increment. A short
node (empty, singleton, or one edge) has neighbour traces that
are subsingletons or the whole node. The trace-tree theorem supplies
the rewiring tree, and the general erasure theorem removes the node.
This is independent of the number of its incident separators. -/

namespace StructuralRamsey.Girth
universe v
variable {V I : Type v}

namespace ContactJoinTree

theorem eraseShort [Fintype V] [Fintype I] {F : I → Set V}
    (T : ContactJoinTree F) (a : I)
    (h : ∀ i : I, i ≠ a →
      (F a ∩ F i).Subsingleton ∨ F a ∩ F i = F a)
    [Nonempty {i : I // i ∈ ({a} : Set I)ᶜ}] :
    Nonempty (ContactJoinTree (contactEraseSet F a)) := by
  classical
  let L := T.tree.neighborSet a
  letI : Fintype L := Fintype.ofFinite L
  have hne : Nonempty L := by
    obtain ⟨i⟩ := (inferInstance : Nonempty {i : I // i ∈ ({a} : Set I)ᶜ})
    have hi : i.val ≠ a := by simpa only [Set.mem_compl_iff,Set.mem_singleton_iff] using i.property
    obtain ⟨b,hb,_⟩ := T.exists_neighbor_reachable_after_delete hi
    exact ⟨⟨b,hb⟩⟩
  letI : Nonempty L := hne
  let K : L → Set V := T.neighborTraces a
  let edge : PUnit.{v+1} → Set V := fun _ => F a
  have ht : ContactEdgeTraces edge K := by
    intro i
    rcases h i.val i.property.ne.symm with hh | hh
    · exact Or.inl hh
    · exact Or.inr ⟨PUnit.unit,hh⟩
  have hlin : ∀ e f : PUnit.{v+1}, e ≠ f →
      (edge e ∩ edge f).Subsingleton := by
    intro e f he
    exact (he (Subsingleton.elim e f)).elim
  have hg : LabelledGirthGT edge (Fintype.card L) := by
    rintro ⟨C,_⟩
    have hcard := Fintype.card_le_of_injective C.label C.label_injective
    simp only [Fintype.card_fin,Fintype.card_punit] at hcard
    have := C.hlength
    omega
  obtain ⟨R⟩ := contact_trace_joinTree edge K ht hlin le_rfl hg
  exact ⟨T.eraseWithTraces a R⟩

/-- Delete every nonselected auxiliary node under the short
intersection condition. The original selected labels survive
unchanged, even when distinct labels have equal carriers. -/
theorem restrictOfShort [Fintype V] [Fintype I] {F : I → Set V}
    (T : ContactJoinTree F) (keep : Set I) (hkeep : keep.Nonempty)
    (hshort : ∀ a ∉ keep, ∀ b : I, b ≠ a →
      (F a ∩ F b).Subsingleton ∨ F a ∩ F b = F a) :
    Nonempty (ContactJoinTree (fun i : keep => F i.val)) := by
  classical
  have aux : ∀ n : ℕ, ∀ (J : Type v) [Fintype J] (K : J → Set V)
      (p : Set J), Fintype.card J = n → p.Nonempty →
      ContactJoinTree K →
      (∀ a ∉ p, ∀ b : J, b ≠ a →
        (K a ∩ K b).Subsingleton ∨ K a ∩ K b = K a) →
      Nonempty (ContactJoinTree (fun i : p => K i.val)) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro J inst K p hn hp T hshort
      by_cases hall : ∀ a : J, a ∈ p
      · let e : p ≃ J := {
          toFun := Subtype.val
          invFun := fun a => ⟨a,hall a⟩
          left_inv := fun _ => Subtype.ext rfl
          right_inv := fun _ => rfl
        }
        exact ⟨T.reindex e⟩
      · push_neg at hall
        obtain ⟨a,ha⟩ := hall
        let J' := {i : J // i ∈ ({a} : Set J)ᶜ}
        letI : Fintype J' := Fintype.ofFinite J'
        let p' : Set J' := {i | i.val ∈ p}
        let K' := contactEraseSet K a
        have hp' : p'.Nonempty := by
          obtain ⟨b,hb⟩ := hp
          have hne : b ≠ a := fun he => ha (he ▸ hb)
          exact ⟨⟨b,by simpa only [Set.mem_compl_iff,Set.mem_singleton_iff] using hne⟩,hb⟩
        letI : Nonempty J' := by obtain ⟨b,_⟩ := hp'; exact ⟨b⟩
        obtain ⟨T'⟩ := T.eraseShort a (hshort a ha)
        have hlt : Fintype.card J' < n := by
          rw [← hn]
          apply Fintype.card_lt_of_injective_not_surjective (fun x : J' => x.val)
            Subtype.val_injective
          intro hsur
          obtain ⟨b,hb⟩ := hsur a
          have hn : b.val ≠ a := by
            simpa only [Set.mem_compl_iff,Set.mem_singleton_iff] using b.property
          exact hn hb
        have hshort' : ∀ b ∉ p', ∀ c : J', c ≠ b →
            (K' b ∩ K' c).Subsingleton ∨ K' b ∩ K' c = K' b := by
          intro b hb c hne
          exact hshort b.val hb c.val (fun h => hne (Subtype.ext h))
        obtain ⟨U⟩ := ih _ hlt J' K' p' rfl hp' T' hshort'
        let e : p ≃ p' := {
          toFun := fun b => ⟨⟨b.val,by
            have hn : b.val ≠ a := fun he => ha (he ▸ b.property)
            simpa only [Set.mem_compl_iff,Set.mem_singleton_iff] using hn⟩,b.property⟩
          invFun := fun b => ⟨b.val.val,b.property⟩
          left_inv := fun _ => Subtype.ext rfl
          right_inv := fun _ => Subtype.ext (Subtype.ext rfl)
        }
        exact ⟨U.reindex e⟩
  exact aux _ I F keep rfl hkeep T hshort

end ContactJoinTree
end StructuralRamsey.Girth
