import Girth.ContactTreeRewire

/-! General node erasure: replace the deleted star by any join tree
on its actual neighbour traces. The tree is constructed on the
surviving labels and running intersection is proved by mapping
the trace occurrence paths into the new tree. -/

namespace StructuralRamsey.Girth
universe v
variable {V ι : Type v}

namespace ContactJoinTree

def neighborTraces {F : ι → Set V} (J : ContactJoinTree F) (center : ι) :
    J.tree.neighborSet center → Set V :=
  fun r => F center ∩ F r.val

/-- Erase a node with a join tree on its neighbour separators. -/
noncomputable def eraseWithTraces {F : ι → Set V} [Fintype ι]
    (J : ContactJoinTree F) (center : ι)
    (R : ContactJoinTree (J.neighborTraces center)) :
    ContactJoinTree (contactEraseSet F center) := by
  classical
  let survivor := {i : ι // i ∈ (({center} : Set ι)ᶜ)}
  refine
    { tree := J.rewireAfterDelete center R.tree
      isTree := J.rewireAfterDelete_isTree center R.tree R.isTree
      running := ?_ }
  intro x
  change
    ((J.rewireAfterDelete center R.tree).induce
      {k : survivor | x ∈ F k.1}).Preconnected
  intro a b
  have ha : a.1.1 ≠ center := by
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using a.1.2
  have hb : b.1.1 ≠ center := by
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using b.1.2
  have hmono :
      ((J.tree.induce (({center} : Set ι)ᶜ)).induce
        {k : {t : ι // t ∈ (({center} : Set ι)ᶜ)} |
        x ∈ F k.1}) ≤
      ((J.rewireAfterDelete center R.tree).induce
        {k : {t : ι // t ∈ (({center} : Set ι)ᶜ)} |
        x ∈ F k.1}) := by
    intro u v huv
    have hle :
        J.tree.induce (({center} : Set ι)ᶜ) ≤
          J.rewireAfterDelete center R.tree := le_sup_left
    exact hle huv
  by_cases hxCenter : x ∈ F center
  · obtain ⟨ra, hra, hreachA⟩ :=
      J.exists_neighbor_reachable_after_delete ha
    obtain ⟨rb, hrb, hreachB⟩ :=
      J.exists_neighbor_reachable_after_delete hb
    let raN : J.tree.neighborSet center := ⟨ra, hra⟩
    let rbN : J.tree.neighborSet center := ⟨rb, hrb⟩
    have hxra : x ∈ F ra :=
      J.mem_root_of_mem_center_and_reachable_after_delete
        hra ha hreachA hxCenter a.2
    have hxrb : x ∈ F rb :=
      J.mem_root_of_mem_center_and_reachable_after_delete
        hrb hb hreachB hxCenter b.2
    have hOccA :=
      J.reachable_occurrence_after_delete
        hra.ne.symm ha hxra a.2 hreachA
    have hOccB :=
      J.reachable_occurrence_after_delete
        hrb.ne.symm hb hxrb b.2 hreachB
    have hA :
        ((J.rewireAfterDelete center R.tree).induce
          {k : {t : ι // t ∈ (({center} : Set ι)ᶜ)} |
        x ∈ F k.1}).Reachable
          a
          ⟨J.neighborToErasedEmbedding center raN, hxra⟩ := by
      have h := (hOccA.mono hmono).symm
      convert h using 1 <;> apply Subtype.ext <;>
        apply Subtype.ext <;> rfl
    have hB :
        ((J.rewireAfterDelete center R.tree).induce
          {k : {t : ι // t ∈ (({center} : Set ι)ᶜ)} |
        x ∈ F k.1}).Reachable
          ⟨J.neighborToErasedEmbedding center rbN, hxrb⟩
          b := by
      have h := hOccB.mono hmono
      convert h using 1 <;> apply Subtype.ext <;>
        apply Subtype.ext <;> rfl
    let occ : Set (J.tree.neighborSet center) :=
      {r | x ∈ F center ∩ F r.val}
    let raF : occ := ⟨raN,hxCenter,hxra⟩
    let rbF : occ := ⟨rbN,hxCenter,hxrb⟩
    have hRroots : (R.tree.induce occ).Reachable raF rbF :=
      R.running x raF rbF
    let phi :
        (R.tree.induce occ) →g
        ((J.rewireAfterDelete center R.tree).induce
          {k : survivor | x ∈ F k.1}) :=
      { toFun := fun z => ⟨J.neighborToErasedEmbedding center z.1,z.2.2⟩
        map_rel' := by
          intro z w hzw
          change (J.rewireAfterDelete center R.tree).Adj
            (J.neighborToErasedEmbedding center z.1)
            (J.neighborToErasedEmbedding center w.1)
          have hle : R.tree.map (J.neighborToErasedEmbedding center) ≤
            J.rewireAfterDelete center R.tree := le_sup_right
          apply hle
          simpa using hzw }
    have hRoots0 := hRroots.map phi
    have hRoots :
        ((J.rewireAfterDelete center R.tree).induce
          {k : {t : ι // t ∈ (({center} : Set ι)ᶜ)} |
        x ∈ F k.1}).Reachable
          ⟨J.neighborToErasedEmbedding center raN, hxra⟩
          ⟨J.neighborToErasedEmbedding center rbN, hxrb⟩ := by
      convert hRoots0 using 1 <;> apply Subtype.ext <;>
        apply Subtype.ext <;> rfl
    exact hA.trans (hRoots.trans hB)
  · have h :=
      J.reachable_occurrence_after_delete_of_not_mem_center
        ha hb a.2 b.2 hxCenter
    exact h.mono hmono




/-- A rewired separator is exactly the intersection of the original
two incident separators. This explains why no new large separator
is introduced when distinct edge separators are linear. -/
theorem new_separator_eq {F : ι → Set V}
    (J : ContactJoinTree F) (center : ι)
    (a b : J.tree.neighborSet center) (hne : a ≠ b) :
    F a.val ∩ F b.val =
      J.neighborTraces center a ∩ J.neighborTraces center b := by
  ext x
  constructor
  · intro hx
    have hn : ¬ (J.tree.induce (({center} : Set ι)ᶜ)).Reachable
        (J.neighborToErasedEmbedding center a) (J.neighborToErasedEmbedding center b) := by
      intro h
      exact hne (Subtype.ext (J.neighbor_eq_of_reachable_after_delete a.property b.property h))
    have hc := J.mem_center_of_shared_not_reachable_after_delete
      a.property.ne.symm b.property.ne.symm hx.1 hx.2 hn
    exact ⟨⟨hc,hx.1⟩,⟨hc,hx.2⟩⟩
  · intro hx
    exact ⟨hx.1.2,hx.2.2⟩

end ContactJoinTree
end StructuralRamsey.Girth
