import Girth.ContactEraseAuxiliary
import Girth.ContactJoinTreeGlue
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

/-! Quantitative completion by a minimum number of added pieces.
There is no separator-history invariant. A minimal auxiliary node
has at least g+1 neighbours by the trace-tree and erasure theorems.
The tree degree sum then gives the sharp budget. -/

namespace StructuralRamsey.Girth
universe v
variable {V E N : Type v}

/-- The elementary numerical conclusion of the minimum completion
argument, separated from the join-tree construction. -/
theorem contact_completion_degree_budget
    (s x d g : ℕ) (hs : 2 ≤ s) (hg : 2 ≤ g)
    (hTree : d+1 = s+x) (hDegree : s+(g+1)*x ≤ 2*d) :
    (g-1)*x ≤ s-2 := by
  have hp : (g-1)*x+2*x = (g+1)*x := by
    rw [← Nat.add_mul]
    congr 1
    omega
  omega

/-- Minimality only concerns the number of added designated pieces.
A positive-size selected family stays present throughout. Every
permitted auxiliary piece has girth greater than g on its own
edge labels; all its neighbour traces are short or actual edges. -/
theorem contact_minimumCompletion_cost
    [Fintype V] [DecidableEq N]
    (F : N → Set V) (edge : E → Set V) (supports : N → Set E)
    (add : N → Prop) (g : ℕ) (hg : 2 ≤ g)
    (hlin : ∀ e f, e ≠ f → (edge e ∩ edge f).Subsingleton)
    (hLocalGirth : ∀ a, add a →
      LabelledGirthGT (fun e : supports a => edge e.val) g)
    (hSep : ∀ a b, a ≠ b → add a →
      (F a ∩ F b).Subsingleton ∨
        ∃ e ∈ supports a, F a ∩ F b = edge e)
    (s : Finset N) (hs : 2 ≤ s.card)
    (hex : ∃ t : Finset N, s ⊆ t ∧
      (∀ a ∈ t, a ∉ s → add a) ∧
      Nonempty (ContactJoinTree (fun i : {i // i ∈ t} => F i.val))) :
    ∃ t : Finset N, s ⊆ t ∧
      (∀ a ∈ t, a ∉ s → add a) ∧
      Nonempty (ContactJoinTree (fun i : {i // i ∈ t} => F i.val)) ∧
      (g-1)*(t \ s).card ≤ s.card-2 := by
  classical
  let p (k : ℕ) : Prop := ∃ t : Finset N, s ⊆ t ∧
    (∀ a ∈ t, a ∉ s → add a) ∧
    Nonempty (ContactJoinTree (fun i : {i // i ∈ t} => F i.val)) ∧
    t.card = k
  have hp : ∃ k, p k := by
    obtain ⟨t,hst,ha,hT⟩ := hex
    exact ⟨t.card,t,hst,ha,hT,rfl⟩
  obtain ⟨t,hst,ha,⟨T⟩,hmin⟩ := Nat.find_spec hp
  let Q := {i : N // i ∈ t}
  have ht : 2 ≤ t.card := hs.trans (Finset.card_le_card hst)
  have hQ : Fintype.card Q = t.card := by simp [Q]
  letI : Nontrivial Q :=
    Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  have hdeg (a : Q) : 1 ≤ T.tree.degree a := by
    obtain ⟨b,hb⟩ := exists_ne a
    obtain ⟨j,hj,_⟩ := T.exists_neighbor_reachable_after_delete hb
    exact (T.tree.degree_pos_iff_exists_adj a).mpr ⟨j,hj⟩
  have hbig (a : Q) (hna : a.val ∉ s) : g+1 ≤ T.tree.degree a := by
    by_contra hn
    have hd : T.tree.degree a ≤ g := by omega
    let L := T.tree.neighborSet a
    letI : Nonempty L := by
      obtain ⟨b,hb⟩ := exists_ne a
      obtain ⟨j,hj,_⟩ := T.exists_neighbor_reachable_after_delete hb
      exact ⟨⟨j,hj⟩⟩
    let e : supports a.val → Set V := fun j => edge j.val
    have he : ContactEdgeTraces e (T.neighborTraces a) := by
      intro b
      rcases hSep a.val b.val.val
        (fun h => b.property.ne (Subtype.ext h)) (ha a.val a.property hna)
        with h | ⟨k,hk,h⟩
      · exact Or.inl h
      · exact Or.inr ⟨⟨k,hk⟩,h⟩
    have hl : ∀ j k : supports a.val, j ≠ k →
        (e j ∩ e k).Subsingleton :=
      fun j k hn => hlin j.val k.val (fun h => hn (Subtype.ext h))
    have hc : Fintype.card L ≤ g := by
      rw [T.tree.card_neighborSet_eq_degree]
      exact hd
    obtain ⟨R⟩ := contact_trace_joinTree e (T.neighborTraces a) he hl hc
      (hLocalGirth a.val (ha a.val a.property hna))
    let t' := t.erase a.val
    have hs' : s ⊆ t' := by
      intro z hz
      exact Finset.mem_erase.mpr ⟨fun h => hna (h ▸ hz),hst hz⟩
    have ha' : ∀ z ∈ t', z ∉ s → add z :=
      fun z hz hn => ha z (Finset.mem_of_mem_erase hz) hn
    let J := T.eraseWithTraces a R
    let r : {i : N // i ∈ t'} ≃ {i : Q // i ∈ ({a} : Set Q)ᶜ} := {
      toFun := fun z => ⟨⟨z.val,Finset.mem_of_mem_erase z.property⟩,by
        have h : z.val ≠ a.val := (Finset.mem_erase.mp z.property).1
        simpa only [Set.mem_compl_iff,Set.mem_singleton_iff] using
          (fun he => h (congrArg Subtype.val he) :
            (⟨z.val,Finset.mem_of_mem_erase z.property⟩ : Q) ≠ a)⟩
      invFun := fun z => ⟨z.val.val,Finset.mem_erase.mpr
        ⟨fun h => by
          have hn : z.val ∉ ({a} : Set Q) := z.property
          exact hn (Set.mem_singleton_iff.mpr (Subtype.ext h)),
          z.val.property⟩⟩
      left_inv := fun _ => Subtype.ext rfl
      right_inv := fun _ => Subtype.ext (Subtype.ext rfl) }
    have htree : Nonempty (ContactJoinTree (fun i : {i // i ∈ t'} => F i.val)) :=
      ⟨J.reindex r⟩
    have hsmall : Nat.find hp ≤ t'.card :=
      Nat.find_min' hp ⟨t',hs',ha',htree,rfl⟩
    have hlt : t'.card < t.card := Finset.card_erase_lt_of_mem a.property
    omega
  let sel : Finset Q := Finset.univ.filter (fun a : Q => a.val ∈ s)
  let aux : Finset Q := Finset.univ.filter (fun a : Q => a.val ∉ s)
  let es : {a : Q // a ∈ sel} ≃ {a : N // a ∈ s} := {
    toFun := fun a => ⟨a.val.val,(Finset.mem_filter.mp a.property).2⟩
    invFun := fun a => ⟨⟨a.val,hst a.property⟩,Finset.mem_filter.mpr
      ⟨Finset.mem_univ _,a.property⟩⟩
    left_inv := fun _ => Subtype.ext (Subtype.ext rfl)
    right_inv := fun _ => Subtype.ext rfl }
  let ea : {a : Q // a ∈ aux} ≃ {a : N // a ∈ t \ s} := {
    toFun := fun a => ⟨a.val.val,Finset.mem_sdiff.mpr
      ⟨a.val.property,(Finset.mem_filter.mp a.property).2⟩⟩
    invFun := fun a => ⟨⟨a.val,(Finset.mem_sdiff.mp a.property).1⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_sdiff.mp a.property).2⟩⟩
    left_inv := fun _ => Subtype.ext (Subtype.ext rfl)
    right_inv := fun _ => Subtype.ext rfl }
  have hsc : sel.card = s.card := by
    simpa using Fintype.card_congr es
  have hac : aux.card = (t \ s).card := by
    simpa using Fintype.card_congr ea
  have hsdeg : s.card ≤ ∑ a ∈ sel, T.tree.degree a := by
    calc
      s.card = ∑ _a ∈ sel, (1 : ℕ) := by simp [hsc]
      _ ≤ _ := Finset.sum_le_sum (fun a _ => hdeg a)
  have hadeg : (g+1)*(t \ s).card ≤ ∑ a ∈ aux, T.tree.degree a := by
    calc
      (g+1)*(t \ s).card = ∑ _a ∈ aux, (g+1) := by
        simp [hac,Nat.mul_comm]
      _ ≤ _ := Finset.sum_le_sum (fun a ha => hbig a (Finset.mem_filter.mp ha).2)
  have hsum : (∑ a ∈ sel, T.tree.degree a) + (∑ a ∈ aux, T.tree.degree a) =
      ∑ a : Q, T.tree.degree a := by
    exact Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun a : Q => a.val ∈ s) (fun a => T.tree.degree a)
  have hd := T.tree.sum_degrees_eq_twice_card_edges
  have he := T.isTree.card_edgeFinset
  rw [hQ] at he
  have htcard := Finset.card_sdiff_add_card_eq_card hst
  refine ⟨t,hst,ha,⟨T⟩,?_⟩
  apply contact_completion_degree_budget s.card (t \ s).card T.tree.edgeFinset.card g hs hg
  · omega
  · calc
      s.card + (g+1)*(t \ s).card ≤
          (∑ a ∈ sel, T.tree.degree a) + (∑ a ∈ aux, T.tree.degree a) :=
        Nat.add_le_add hsdeg hadeg
      _ = ∑ a : Q, T.tree.degree a := hsum
      _ = 2*T.tree.edgeFinset.card := hd

end StructuralRamsey.Girth
