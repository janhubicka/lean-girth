import Girth.ContactLocalCompletion
import Girth.ContactEraseAuxiliary
import Girth.ContactCompletionBudget
import Girth.ContactZeroJoinTrees

/-! Direct forest increment at the level of selected vertex carriers.
The two cases of the manuscript are both constructed. When all owners
are distinct, use the high-girth trace tree. Otherwise use the small
outer join tree, add its separators to each local family, lift and
erase. All auxiliary labels and local budgets are explicit. -/

namespace StructuralRamsey.Girth
universe v
variable {U E N Q : Type v}

/-- Restoring private points to an indexed family preserves its
running-intersection tree. -/
def ContactJoinTree.restoreOutside {F : N → Set U} {C : Set U}
    (T : ContactJoinTree (fun n => F n ∩ C))
    (hpriv : ∀ x, x ∉ C → {n | x ∈ F n}.Subsingleton) :
    ContactJoinTree F where
  tree := T.tree
  isTree := T.isTree
  running := by
    intro x
    by_cases hx : x ∈ C
    · have he : {n | x ∈ F n ∩ C} = {n | x ∈ F n} := by
        ext n
        simp [hx]
      have h := T.running x
      change (T.tree.induce {n | x ∈ F n ∩ C}).Preconnected at h
      rw [he] at h
      exact h
    · letI : Subsingleton {n : N | x ∈ F n} := (hpriv x hx).coe_sort
      exact SimpleGraph.Preconnected.of_subsingleton

/-- A surjective noninjective owner assignment uses strictly fewer
labels than the selected family. -/
theorem contact_owner_card_lt [Fintype N] [Fintype Q]
    (owner : N → Q) (hsurj : Function.Surjective owner)
    (hnot : ¬ Function.Injective owner) :
    Fintype.card Q < Fintype.card N := by
  classical
  let rep : Q → N := fun q => Classical.choose (hsurj q)
  have hrep : ∀ q, owner (rep q) = q :=
    fun q => Classical.choose_spec (hsurj q)
  have hrepInj : Function.Injective rep := by
    intro a b he
    exact (hrep a).symm.trans ((congrArg owner he).trans (hrep b))
  apply Fintype.card_lt_of_injective_not_surjective rep hrepInj
  intro honto
  apply hnot
  intro a b he
  obtain ⟨u,rfl⟩ := honto a
  obtain ⟨w,rfl⟩ := honto b
  exact congrArg rep ((hrep u).symm.trans (he.trans (hrep w)))

/-- Every separator is short or a full ambient edge. Its intersection
with any other separator or selected strong member is short or
the whole separator. -/
theorem contact_auxiliary_intersection (edge : E → Set U)
    (hlin : ∀ e f : E, e ≠ f → (edge e ∩ edge f).Subsingleton)
    (A B : Set U)
    (hA : A.Subsingleton ∨ ∃ e, A = edge e)
    (hB : ∀ e, (edge e ∩ B).Nontrivial → edge e ⊆ B) :
    (A ∩ B).Subsingleton ∨ A ∩ B = A := by
  classical
  rcases hA with hs | ⟨e,he⟩
  · exact Or.inl (fun _ hx _ hy => hs hx.1 hy.1)
  · rw [he]
    by_cases hsub : (edge e ∩ B).Subsingleton
    · exact Or.inl hsub
    · right
      have hn : (edge e ∩ B).Nontrivial := Set.not_subsingleton_iff.mp hsub
      exact Set.inter_eq_left.mpr (hB e hn)

theorem contact_edgeTrace_strong (edge : E → Set U)
    (hlin : ∀ e f : E, e ≠ f → (edge e ∩ edge f).Subsingleton)
    (A : Set U) (hA : A.Subsingleton ∨ ∃ e, A = edge e) :
    ∀ e, (edge e ∩ A).Nontrivial → edge e ⊆ A := by
  intro e hn
  obtain ⟨x,hx,y,hy,hne⟩ := hn
  rcases hA with hsub | ⟨f,hf⟩
  · exact (hne (hsub hx.2 hy.2)).elim
  · rw [hf] at hx hy ⊢
    by_cases he : e = f
    · rw [he]
    · exact (hne (hlin e f he hx hy)).elim

/-- Join-tree part of direct forest increment. The only local
inputs are the small-family join-tree properties of the two source
systems, actual carrier containment and the strongness and trace
facts supplied by the picture construction.

The family edge consists of the embedded core edges, not all
output edges. Thus hg assumes high girth only in the core.
G q lists the old pieces available in owner q (including its edge
copies). The outer carriers are the full lifted standards or
uncovered core edges; the core trace condition prevents noncore
intersections of distinct owners. The proof never assumes a join
tree of the selected output members or their local completions. -/
theorem contact_directIncrement_joinTree [Fintype U] [Fintype N] [Nonempty N]
    [Fintype Q] [Nonempty Q] {J : Q → Type v}
    (edge : E → Set U) (F : N → Set U) (P : Q → Set U)
    (G : (i : Q) → J i → Set U) (C : Set U)
    (owner : N → Q) (hsurj : Function.Surjective owner)
    (q : ℕ) (hcard : Fintype.card N ≤ q)
    (hlin : ∀ e f : E, e ≠ f → (edge e ∩ edge f).Subsingleton)
    (hg : LabelledGirthGT edge q)
    (hContain : ∀ n, F n ⊆ P (owner n))
    (hCross : ∀ i j, i ≠ j → P i ∩ P j ⊆ C)
    (hTrace : ContactEdgeTraces edge (fun n => F n ∩ C))
    (hStrong : ∀ n e, (edge e ∩ F n).Nontrivial → edge e ⊆ F n)
    (hSep : ∀ i j, i ≠ j → (P i ∩ P j).Subsingleton ∨
      (∃ e, P i ∩ P j = edge e))
    (hLocalSel : ∀ n, ∃ a : J (owner n), F n = G (owner n) a)
    (hLocalSep : ∀ i j, i ≠ j → ¬ (P i ∩ P j).Subsingleton →
      ∃ a : J i, P i ∩ P j = G i a)
    (hlocal : ∀ i (s : Finset (J i)), s.Nonempty → s.card ≤ q →
      Nonempty (ContactJoinTree (fun a : {a // a ∈ s} => G i a.val)))
    (houter : Fintype.card Q ≤ q-1 → Nonempty (ContactJoinTree P)) :
    Nonempty (ContactJoinTree F) := by
  classical
  by_cases hinj : Function.Injective owner
  · obtain ⟨T⟩ := contact_trace_joinTree edge (fun n => F n ∩ C)
      hTrace hlin hcard hg
    apply Nonempty.intro
    apply T.restoreOutside
    intro x hx n hn m hm
    by_contra hne
    have hown : owner n ≠ owner m := fun he => hne (hinj he)
    exact hx (hCross _ _ hown ⟨hContain n hn,hContain m hm⟩)
  · have hsmall : Fintype.card Q ≤ q-1 := by
      have hh := contact_owner_card_lt owner hsurj hinj
      omega
    obtain ⟨T⟩ := houter hsmall
    let K : Q → Type v := fun i =>
      {n : N // owner n = i} ⊕ T.tree.neighborSet i
    letI : ∀ i, Fintype (K i) := fun i => inferInstanceAs
      (Fintype ({n : N // owner n = i} ⊕ T.tree.neighborSet i))
    letI : ∀ i, Nonempty (K i) := by
      intro i
      obtain ⟨n,hn⟩ := hsurj i
      exact ⟨Sum.inl ⟨n,hn⟩⟩
    let H : (i : Q) → K i → Set U := fun i k =>
      match k with
      | .inl n => F n.val
      | .inr j => P i ∩ P j.val
    have hBudget (i : Q) : Fintype.card (K i) ≤ q := by
      have hh := contact_ownerFiber_card_add_degree_le owner hsurj T.tree i
      have hK : Fintype.card (K i) =
          Fintype.card {n : N // owner n = i} + T.tree.degree i := by
        change Fintype.card ({n : N // owner n = i} ⊕ T.tree.neighborSet i) = _
        rw [Fintype.card_sum,T.tree.card_neighborSet_eq_degree]
      rw [hK]
      exact hh.trans hcard
    have hH (i : Q) : ∀ k : K i, (H i k).Subsingleton ∨
        ∃ a : J i, H i k = G i a := by
      intro k
      cases k with
      | inl n =>
        right
        have hn := hLocalSel n.val
        have he := n.property
        change ∃ a : J i, F n.val = G i a
        rw [← he]
        exact hn
      | inr j =>
        by_cases hs : (P i ∩ P j.val).Subsingleton
        · exact Or.inl hs
        · exact Or.inr (hLocalSep i j.val j.property.ne hs)
    have hTrees : ∀ i, Nonempty (ContactJoinTree (H i)) :=
      fun i => contact_localCompletion (H i) (G i) q (hBudget i) (hlocal i) (hH i)
    let localTree : ∀ i, ContactJoinTree (H i) := fun i => Classical.choice (hTrees i)
    have hcontains : ∀ i (k : K i), H i k ⊆ P i := by
      intro i k
      cases k with
      | inl n =>
        change F n.val ⊆ P i
        rw [← n.property]
        exact hContain n.val
      | inr j => exact Set.inter_subset_left
    let connector : (i j : Q) → K i := fun i j =>
      if h : T.tree.Adj i j then Sum.inr ⟨j,h⟩
      else Classical.choice (inferInstance : Nonempty (K i))
    have hc : ∀ ⦃i j : Q⦄, T.tree.Adj i j →
        P i ∩ P j ⊆ H i (connector i j) := by
      intro i j h
      simp only [connector,dif_pos h,H]
      exact Set.Subset.rfl
    obtain ⟨JT⟩ := contact_joinTree_lift_local T localTree hcontains connector hc
    let selected : N → Sigma K := fun n => ⟨owner n,Sum.inl ⟨n,rfl⟩⟩
    let keep : Set (Sigma K) := Set.range selected
    let A : Sigma K → Set U := fun k => H k.1 k.2
    have hkeep : keep.Nonempty := by
      let n : N := Classical.choice inferInstance
      exact ⟨selected n,⟨n,rfl⟩⟩
    have haux : ∀ a : Sigma K, a ∉ keep →
        (A a).Subsingleton ∨ ∃ e, A a = edge e := by
      rintro ⟨i,k⟩ hk
      cases k with
      | inl n =>
        apply False.elim
        apply hk
        refine ⟨n.val,?_⟩
        have he := n.property
        cases he
        rfl
      | inr j => exact hSep i j.val j.property.ne
    have hAstr : ∀ a : Sigma K, ∀ e, (edge e ∩ A a).Nontrivial → edge e ⊆ A a := by
      rintro ⟨i,k⟩ e hn
      cases k with
      | inl n => exact hStrong n.val e hn
      | inr j => exact contact_edgeTrace_strong edge hlin _ (hSep i j.val j.property.ne) e hn
    have hshort : ∀ a ∉ keep, ∀ b : Sigma K, b ≠ a →
        (A a ∩ A b).Subsingleton ∨ A a ∩ A b = A a :=
      fun a ha b _ => contact_auxiliary_intersection edge hlin _ _ (haux a ha) (hAstr b)
    obtain ⟨Utree⟩ := JT.restrictOfShort keep hkeep hshort
    let f : N → keep := fun n => ⟨selected n,⟨n,rfl⟩⟩
    have hfinj : Function.Injective f := by
      intro n m he
      have hval := congrArg (fun a : keep => a.val) he
      have hh : (selected n) = selected m := hval
      let recover : Sigma K → Option N := fun k =>
        match k.2 with
        | .inl n => some n.val
        | .inr _ => none
      exact Option.some.inj (congrArg recover hh)
    have hfsurj : Function.Surjective f := by
      rintro ⟨k,hk⟩
      obtain ⟨n,rfl⟩ := hk
      exact ⟨n,rfl⟩
    let e := Equiv.ofBijective f ⟨hfinj,hfsurj⟩
    exact ⟨Utree.reindex e⟩


/-- For cutoff one, every nonempty selected family has exactly
one member. In particular no pairwise condition is needed. -/
theorem OrderOneData.zeroSmallMixedForests_one {I : Type v}
    (D : OrderOneData U E I E) : D.ZeroSmallMixedForestsThrough 1 := by
  classical
  refine ⟨fun h => (by omega : False).elim,?_⟩
  intro s hs hc
  let J := {a // a ∈ s}
  letI : Nonempty J := by obtain ⟨a,ha⟩ := hs; exact ⟨⟨a,ha⟩⟩
  letI : Subsingleton J := ⟨by
    intro a b
    apply Subtype.ext
    by_contra hne
    have hsub : ({a.val,b.val} : Finset (I ⊕ E)) ⊆ s := by
      intro z hz
      simp only [Finset.mem_insert,Finset.mem_singleton] at hz
      rcases hz with rfl | rfl
      · exact a.property
      · exact b.property
    have hl := Finset.card_le_card hsub
    rw [Finset.card_pair hne] at hl
    omega⟩
  exact ⟨ContactJoinTree.of_subsingleton (fun a : J => D.carrier a.val)⟩

/-- Distinct owners can share only a core trace. If two actual
selected carriers meet in at least two vertices, the two traces are
the same full core edge, by core linearity. This proof needs no
pairwise assumption on the core designated copies at cutoff one. -/
theorem contact_distinct_owner_intersection (edge : E → Set U)
    (F : N → Set U) (P : Q → Set U) (C : Set U) (owner : N → Q)
    (hlin : ∀ e f : E, e ≠ f → (edge e ∩ edge f).Subsingleton)
    (hContain : ∀ n, F n ⊆ P (owner n))
    (hCross : ∀ i j, i ≠ j → P i ∩ P j ⊆ C)
    (hTrace : ContactEdgeTraces edge (fun n => F n ∩ C))
    (n m : N) (hne : owner n ≠ owner m) :
    (F n ∩ F m).Subsingleton ∨
      ∃ e, F n ∩ C = edge e ∧ F m ∩ C = edge e ∧ F n ∩ F m = edge e := by
  classical
  by_cases hs : (F n ∩ F m).Subsingleton
  · exact Or.inl hs
  have hc : F n ∩ F m ⊆ C :=
    fun x hx => hCross _ _ hne ⟨hContain n hx.1,hContain m hx.2⟩
  obtain ⟨x,hx,y,hy,hxy⟩ := Set.not_subsingleton_iff.mp hs
  have hnx : x ∈ F n ∩ C := ⟨hx.1,hc hx⟩
  have hny : y ∈ F n ∩ C := ⟨hy.1,hc hy⟩
  have hmx : x ∈ F m ∩ C := ⟨hx.2,hc hx⟩
  have hmy : y ∈ F m ∩ C := ⟨hy.2,hc hy⟩
  obtain ⟨e,he⟩ : ∃ e, F n ∩ C = edge e := by
    rcases hTrace n with hh | hh
    · exact (hxy (hh hnx hny)).elim
    · exact hh
  obtain ⟨f,hf⟩ : ∃ f, F m ∩ C = edge f := by
    rcases hTrace m with hh | hh
    · exact (hxy (hh hmx hmy)).elim
    · exact hh
  have hef : e = f := by
    by_contra hn
    apply hxy
    apply hlin e f hn
    · exact ⟨he ▸ hnx,hf ▸ hmx⟩
    · exact ⟨he ▸ hny,hf ▸ hmy⟩
  subst f
  refine Or.inr ⟨e,he,hf,?_⟩
  ext z
  constructor
  · intro hz
    exact he ▸ (show z ∈ F n ∩ C from ⟨hz.1,hc hz⟩)
  · intro hz
    have hn : z ∈ F n ∩ C := he.symm ▸ hz
    have hm : z ∈ F m ∩ C := hf.symm ▸ hz
    exact ⟨hn.1,hm.1⟩

end StructuralRamsey.Girth
