import Girth.ContactMarkedEdges
import Girth.ContactUniformLocalRamsey
import Girth.ContactTreeAmalgamChordal
import Girth.ForestAttach
import Girth.ForestReindex

/-! Sharpness of adding one copy at the first possible family size.
The cycle below is an actual finite linear graph, with distinct two-element
edge carriers. Its edge family has no join tree, while adjoining the containing
graph gives a star join tree. The final relational obstruction records separately
the ternary-relation argument used in the manuscript. -/

namespace StructuralRamsey.Girth
open StructuralRamsey.RelStructure
universe u v
variable {V E : Type v}

/-- A linear family carrying a Berge cycle has no running-intersection tree.
This is the one-marked-edge-per-bag obstruction with the actual edge labels. -/
theorem contact_linear_cycle_no_joinTree [Fintype E]
    (edge : E → Set V)
    (hlin : ∀ i j, i ≠ j → (edge i ∩ edge j).Subsingleton)
    (C : LabelledBergeCycle edge) : ¬ Nonempty (ContactJoinTree edge) := by
  rintro ⟨J⟩
  let D : LabelledBergeCycle (fun e : {e : E // True} => edge e.val) := {
    length := C.length
    hlength := C.hlength
    label := fun i => ⟨C.label i,True.intro⟩
    vertex := C.vertex
    label_injective := fun i j h => C.label_injective (congrArg Subtype.val h)
    vertex_injective := C.vertex_injective
    left_mem := C.left_mem
    right_mem := C.right_mem }
  exact contact_marked_cycle_impossible edge edge (fun i => {i}) (fun _ => True) J
    (fun i e he => by
      have heq : e = i := Set.mem_singleton_iff.mp he
      subst e
      exact Set.Subset.rfl)
    (fun i e f he hf _ _ => (Set.mem_singleton_iff.mp he).trans
      (Set.mem_singleton_iff.mp hf).symm)
    hlin (fun i j hij => Or.inl (hlin i j hij)) D
    (fun k => ⟨C.label k,Set.mem_singleton _⟩)

/-- Include one full carrier alongside a family of edge carriers. -/
def contactCompletionStar (H : Set (Set V)) (edge : E → Set V) :
    Option E → HypergraphPiece V := fun i =>
  contactInducedHypergraphPiece H (match i with | none => Set.univ | some e => edge e)

/-- The full member is the centre of an actual star join tree.
All edge separators are common induced edges. -/
theorem contact_completion_star_forest
    (H : Set (Set V)) (edge : E → Set V) (hmem : ∀ e, edge e ∈ H)
    (hlin : ∀ i j, i ≠ j → (edge i ∩ edge j).Subsingleton) :
    ForestOfCopies (contactCompletionStar H edge) := by
  classical
  constructor
  · intro i j hij
    cases i with
    | none =>
      cases j with
      | none => exact (hij rfl).elim
      | some j =>
        exact Or.inr ⟨edge j,⟨hmem j,Set.subset_univ _⟩,
          ⟨hmem j,Set.Subset.rfl⟩,Set.univ_inter _⟩
    | some i =>
      cases j with
      | none =>
        exact Or.inr ⟨edge i,⟨hmem i,Set.Subset.rfl⟩,
          ⟨hmem i,Set.subset_univ _⟩,Set.inter_univ _⟩
      | some j => exact Or.inl (hlin i j (fun h => hij (congrArg some h)))
  · right
    exact ⟨{
      tree := SimpleGraph.starGraph (none : Option E)
      isTree := SimpleGraph.isTree_starGraph none
      running := fun x => starGraph_induce_preconnected_of_mem_center none
        (show x ∈ (contactCompletionStar H edge none).carrier from Set.mem_univ _) }⟩

/-- The n edges of the simple cycle on Fin n. -/
def contactCycleEdge (n : ℕ) (i : Fin n) : Set (Fin n) := {i,cyclicSucc i}

theorem contactCycleEdge_injective {n : ℕ} (hn : 3 ≤ n) :
    Function.Injective (contactCycleEdge n) := by
  intro i j h
  rcases Set.pair_eq_pair_iff.mp h with h | h
  · exact h.1
  · have hbad : cyclicSucc (cyclicSucc j) = j := by rw [← h.1,h.2]
    exact (contactSucc_sq_ne hn j hbad).elim

theorem contact_pair_eq_of_two_distinct {W : Type*} {x y a b : W}
    (hne : x ≠ y) (hx : x ∈ ({a,b} : Set W)) (hy : y ∈ ({a,b} : Set W)) :
    ({x,y} : Set W) = {a,b} := by
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hx hy
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;>
    simp_all only [ne_eq,not_true_eq_false,Set.pair_comm]

theorem contactCycleEdge_linear {n : ℕ} (hn : 3 ≤ n) :
    ∀ i j : Fin n, i ≠ j →
      (contactCycleEdge n i ∩ contactCycleEdge n j).Subsingleton := by
  intro i j hij x hx y hy
  by_contra hxy
  have he : contactCycleEdge n i = contactCycleEdge n j :=
    (contact_pair_eq_of_two_distinct hxy hx.1 hy.1).symm.trans
      (contact_pair_eq_of_two_distinct hxy hx.2 hy.2)
  exact hij (contactCycleEdge_injective hn he)

theorem contactCycleEdge_card {n : ℕ} (hn : 3 ≤ n) (i : Fin n) :
    Nat.card (contactCycleEdge n i) = 2 :=
  Set.ncard_pair (contactSucc_ne (by omega) i).symm

/-- The cyclic order of the actual graph edges is a Berge cycle. -/
def contactCycleBerge (n : ℕ) (hn : 3 ≤ n) :
    LabelledBergeCycle (contactCycleEdge n) where
  length := n
  hlength := by omega
  label := id
  vertex := cyclicSucc
  label_injective := Function.injective_id
  vertex_injective := Finite.injective_iff_surjective.mpr contactSucc_surjective
  left_mem := fun i => Set.mem_insert_of_mem _ (Set.mem_singleton _)
  right_mem := fun i => Set.mem_insert _ _

private theorem contactSharp_cycle_shift {n : ℕ} (s i : Fin n) :
    finCycle s (cyclicSucc i) = cyclicSucc (finCycle s i) := by
  have hrot (j : Fin n) : cyclicSucc j = finRotate n j := by
    let := j.neZero
    apply Fin.ext
    simp [cyclicSucc,finRotate_apply,Fin.add_def]
  rw [hrot,hrot]
  simp only [finRotate_apply,finCycle_apply]
  ac_rfl

private theorem contactSharp_cycle_all_of_point {n : ℕ} (hn : 0 < n)
    (Q : Fin n → Prop) (s : Fin n) (hs : Q s)
    (hnext : ∀ i, Q i → Q (cyclicSucc i)) : ∀ i, Q i := by
  let : NeZero n := ⟨by omega⟩
  have hall : ∀ i, Q (finCycle s i) := contactCycle_all_of_zero hn
    (fun i => Q (finCycle s i)) (by simpa [finCycle_apply] using hs)
    (fun i hi => by rw [contactSharp_cycle_shift]; exact hnext _ hi)
  intro i
  obtain ⟨j,rfl⟩ := (finCycle s).surjective i
  exact hall j

/-- Every Berge cycle in the graph cycle uses every edge. In
particular the source really has girth exactly n, not only a
displayed cycle of length n. -/
theorem contactCycleEdge_cycle_length {n : ℕ} (hn : 3 ≤ n)
    (C : LabelledBergeCycle (contactCycleEdge n)) : C.length = n := by
  let Q (e : Fin n) : Prop := ∃ i, C.label i = e
  have hsucc : Function.Injective (@cyclicSucc n) :=
    Finite.injective_iff_surjective.mpr contactSucc_surjective
  have hnext (e : Fin n) (he : Q e) : Q (cyclicSucc e) := by
    obtain ⟨k,rfl⟩ := he
    obtain ⟨p,hp⟩ := contactSucc_surjective k
    have hpk : p ≠ k := by
      intro heq
      subst p
      exact contactSucc_ne C.hlength k hp
    have hxy : C.vertex p ≠ C.vertex k := fun heq => hpk (C.vertex_injective heq)
    have hk : C.vertex k ∈ contactCycleEdge n (C.label k) := C.left_mem k
    have hprev : C.vertex p ∈ contactCycleEdge n (C.label k) := hp ▸ C.right_mem p
    have hit : C.vertex k = cyclicSucc (C.label k) ∨
        C.vertex p = cyclicSucc (C.label k) := by
      simp only [contactCycleEdge,Set.mem_insert_iff,Set.mem_singleton_iff] at hk hprev
      rcases hk with hk | hk
      · rcases hprev with hprev | hprev
        · exact (hxy (hprev.trans hk.symm)).elim
        · exact Or.inr hprev
      · exact Or.inl hk
    have unique (j : Fin n) (hj : j ≠ C.label k)
        (hx : cyclicSucc (C.label k) ∈ contactCycleEdge n j) :
        j = cyclicSucc (C.label k) := by
      rcases hx with hx | hx
      · exact hx.symm
      · exact (hj (hsucc hx.symm)).elim
    rcases hit with hit | hit
    · refine ⟨cyclicSucc k,unique _ ?_ ?_⟩
      · exact fun heq => contactSucc_ne C.hlength k (C.label_injective heq)
      · exact hit ▸ C.right_mem k
    · refine ⟨p,unique _ ?_ ?_⟩
      · exact fun heq => hpk (C.label_injective heq)
      · exact hit ▸ C.left_mem p
  let i₀ : Fin C.length := ⟨0,by have := C.hlength; omega⟩
  have hall : ∀ e, Q e := contactSharp_cycle_all_of_point (by omega)
    Q (C.label i₀) ⟨i₀,rfl⟩ hnext
  have hsurj : Function.Surjective C.label := hall
  have hc := Fintype.card_congr (Equiv.ofBijective C.label ⟨C.label_injective,hsurj⟩)
  simpa using hc

theorem contactCycleEdge_girth {n : ℕ} (hn : 3 ≤ n) :
    LabelledGirthGT (contactCycleEdge n) (n-1) := by
  rintro ⟨C,hC⟩
  have hlen := contactCycleEdge_cycle_length hn C
  omega

theorem contactCycleEdge_not_univ {n : ℕ} (hn : 3 ≤ n) (i : Fin n) :
    contactCycleEdge n i ≠ Set.univ := by
  intro he
  have h := contactCycleEdge_card hn i
  rw [he,Nat.card_univ,Nat.card_fin] at h
  omega

theorem contactCycleStar_carrier_injective {n : ℕ} (hn : 3 ≤ n) :
    Function.Injective (fun i =>
      (contactCompletionStar (Set.range (contactCycleEdge n)) (contactCycleEdge n) i).carrier) := by
  intro i j he
  cases i with
  | none =>
    cases j with
    | none => rfl
    | some j => exact (contactCycleEdge_not_univ hn j he.symm).elim
  | some i =>
    cases j with
    | none => exact (contactCycleEdge_not_univ hn i he).elim
    | some j => exact congrArg some (contactCycleEdge_injective hn he)

/-- At precisely g+1 requested edges a new member is necessary,
and one distinct containing member suffices, attaining the bound.
The injectivity assertion makes the count a count of actual carriers. -/
theorem contact_cycle_completion_sharp (g : ℕ) (hg : 2 ≤ g) :
    LabelledGirthGT (contactCycleEdge (g+1)) g ∧
    (∀ i : Fin (g+1), Nat.card (contactCycleEdge (g+1) i) = 2) ∧
    (¬ ForestOfCopies (fun i : Fin (g+1) =>
      contactInducedHypergraphPiece (Set.range (contactCycleEdge (g+1)))
        (contactCycleEdge (g+1) i))) ∧
    ForestOfCopies (contactCompletionStar (Set.range (contactCycleEdge (g+1)))
      (contactCycleEdge (g+1))) ∧
    Function.Injective (fun i =>
      (contactCompletionStar (Set.range (contactCycleEdge (g+1)))
        (contactCycleEdge (g+1)) i).carrier) ∧
    Fintype.card (Fin (g+1)) = g+1 ∧
    Fintype.card (Option (Fin (g+1))) = g+2 ∧
    (g-1)*1 = (g+1)-2 := by
  have hn : 3 ≤ g+1 := by omega
  refine ⟨by simpa using contactCycleEdge_girth hn,contactCycleEdge_card hn,
    ?_,contact_completion_star_forest _ _ (fun i => ⟨i,rfl⟩)
    (contactCycleEdge_linear hn),contactCycleStar_carrier_injective hn,by simp,by simp,by omega⟩
  intro h
  let : Nonempty (Fin (g+1)) := ⟨⟨0,by omega⟩⟩
  obtain ⟨J⟩ := h.joinTree_of_nonempty
  exact contact_linear_cycle_no_joinTree _ (contactCycleEdge_linear hn) (contactCycleBerge _ hn)
    ⟨{tree := J.tree,isTree := J.isTree,running := J.running}⟩

/-- The relational obstruction behind the sharpness example. Long
chordless comparison cycles are excluded by tree chordality. A triangle
is excluded by the complete ternary relation in B and its absence in C. -/
theorem contact_ternary_cycle_no_supported_embedding
    {L : RelLanguage.{u}} {U V W X : Type v}
    (A : RelStructure L U) (B : RelStructure L V)
    [LinearOrder U] [LinearOrder V]
    (C : RelStructure L.withOrder W) (R : L.Symbol) (hR : L.arity R = 3)
    (hfull : ∀ y : Fin (L.arity R) → V, Function.Injective y → B.rel R y)
    (hempty : ∀ x : Fin (L.arity R) → W, ¬ C.rel (.inl R) x)
    {n : ℕ} (hn : 3 ≤ n) (z : Fin n → W) (hz : Function.Injective z)
    (hcycle : ∀ i j, (contactComparisonGraph C).Adj (z i) (z j) ↔
      cyclicSucc i = j ∨ cyclicSucc j = i)
    (T : RelStructure L.withOrder X)
    (hT : ASupportedTreeAmalgam A.ordered B.ordered X T) :
    ¬ Nonempty (Embedding C T) := by
  rintro ⟨e⟩
  by_cases hthree : n = 3
  · subst n
    let Z := Set.range z
    have hIrred : (C.induce Z).Irreducible := by
      intro x y hxy
      obtain ⟨i,hi⟩ := x.property
      obtain ⟨j,hj⟩ := y.property
      have hij : i ≠ j := by
        intro he
        exact hxy (Subtype.ext (hi.symm.trans ((congrArg z he).trans hj)))
      have hnext : cyclicSucc i = j ∨ cyclicSucc j = i := by
        fin_cases i <;> fin_cases j <;> simp_all [cyclicSucc]
      have hadj : (contactComparisonGraph C).Adj x.val y.val := by
        rw [← hi,← hj]
        exact (hcycle i j).mpr hnext
      have hlocal := (contactComparisonGraph_embedding (C.inclusion Z) x y).mp hadj
      rcases hlocal.2 with h | h
      · exact ⟨.inr (),![x,y],(0 : Fin 2),(1 : Fin 2),h,rfl,rfl⟩
      · exact ⟨.inr (),![y,x],(1 : Fin 2),(0 : Fin 2),h,rfl,rfl⟩
    obtain ⟨b,hb⟩ := hT.irreducible_contained_in_copy
      (contact_ordered_irreducible A) hIrred (e.comp (C.inclusion Z))
    have hex (i : Fin 3) : ∃ y : V, e (z i) = b y := hb ⟨z i,⟨i,rfl⟩⟩
    choose y hy using hex
    have hyi : Function.Injective y := by
      intro i j hij
      apply hz
      apply e.injective
      exact (hy i).trans ((congrArg b hij).trans (hy j).symm)
    let q : Fin (L.arity R) ≃ Fin 3 := finCongr hR
    let x' := z ∘ q
    let y' := y ∘ q
    have hB : B.ordered.rel (.inl R) y' := hfull y' (hyi.comp q.injective)
    have heq : b.toFun ∘ y' = e.toFun ∘ x' := funext (fun k => (hy (q k)).symm)
    have hpositive : T.rel (.inl R) (e.toFun ∘ x') :=
      heq ▸ (b.map_rel_iff (.inl R) y').mpr hB
    exact hempty x' ((e.map_rel_iff (.inl R) x').mp hpositive)
  · have hn4 : 4 ≤ n := by omega
    have hc := contactComparisonGraph_chordal_of_supportedTree_embedding e hT
    obtain ⟨i,j,hij,hi,hj,hadj⟩ := hc n z hn4 hz
      (fun i => (hcycle i (cyclicSucc i)).mpr (Or.inl rfl))
    rcases (hcycle i j).mp hadj with he | he
    · exact hi he
    · exact hj he

/-- Binary graph adjacency together with the extra ternary relation. -/
def contactSharpLanguage : RelLanguage.{0} where
  Symbol := Bool
  arity := fun R => if R then 3 else 2

/-- The cycle graph with a ternary relation on all distinct triples. -/
def contactSharpCycle (n : ℕ) : RelStructure contactSharpLanguage (Fin n) where
  rel R := by
    cases R with
    | false => exact fun x : Fin 2 → Fin n =>
        cyclicSucc (x 0) = x 1 ∨ cyclicSucc (x 1) = x 0
    | true => exact fun x : Fin 3 → Fin n => Function.Injective x

/-- The actual relation union of the ordered edge pieces of the cycle.
The graph and incident order pairs remain; no ternary tuple remains. -/
def contactSharpEdgeUnion (n : ℕ) : RelStructure contactSharpLanguage.withOrder (Fin n) where
  rel R := by
    cases R with
    | inl R =>
      cases R with
      | false => exact fun x : Fin 2 → Fin n =>
          cyclicSucc (x 0) = x 1 ∨ cyclicSucc (x 1) = x 0
      | true => exact fun _ : Fin 3 → Fin n => False
    | inr _ => exact fun x : Fin 2 → Fin n => x 0 < x 1 ∧
        (cyclicSucc (x 0) = x 1 ∨ cyclicSucc (x 1) = x 0)

theorem contact_no_injective_triple_in_pair {W : Type*} (a b : W)
    (x : Fin 3 → W) (hm : ∀ i, x i ∈ ({a,b} : Set W)) :
    ¬ Function.Injective x := by
  intro hi
  have h01 : x 0 ≠ x 1 := fun he => by have := hi he; omega
  have he := contact_pair_eq_of_two_distinct h01 (hm 0) (hm 1)
  have h2 : x 2 ∈ ({x 0,x 1} : Set W) := he.symm ▸ hm 2
  rcases h2 with h | h
  · have := hi h; omega
  · have := hi h; omega

theorem contactCycleEdge_pair_iff {n : ℕ} {i j : Fin n} (hne : i ≠ j) :
    (∃ e, i ∈ contactCycleEdge n e ∧ j ∈ contactCycleEdge n e) ↔
      cyclicSucc i = j ∨ cyclicSucc j = i := by
  constructor
  · rintro ⟨e,hi,hj⟩
    rcases hi with hi | hi <;> rcases hj with hj | hj
    · exact (hne (hi.trans hj.symm)).elim
    · exact Or.inl (by rw [hi,hj])
    · exact Or.inr (by rw [hi,hj])
    · exact (hne (hi.trans hj.symm)).elim
  · rintro (h | h)
    · exact ⟨i,Set.mem_insert _ _,h ▸ Set.mem_insert_of_mem _ (Set.mem_singleton _)⟩
    · exact ⟨j,h ▸ Set.mem_insert_of_mem _ (Set.mem_singleton _),Set.mem_insert _ _⟩

/-- The source is exactly the relation union of the induced ordered
edge pieces. This includes the restricted order relation and the
absence of ternary tuples, rather than only identifying carriers. -/
theorem contactSharpEdgeUnion_relation_union {n : ℕ} (hn : 3 ≤ n)
    (R : contactSharpLanguage.withOrder.Symbol)
    (x : Fin (contactSharpLanguage.withOrder.arity R) → Fin n) :
    (contactSharpEdgeUnion n).rel R x ↔
      ∃ e, (contactSharpCycle n).ordered.rel R x ∧
        ∀ k, x k ∈ contactCycleEdge n e := by
  have hpair (x : Fin 2 → Fin n)
      (h : cyclicSucc (x 0) = x 1 ∨ cyclicSucc (x 1) = x 0) :
      ∃ e, ∀ k, x k ∈ contactCycleEdge n e := by
    have hne : x 0 ≠ x 1 := by
      intro he
      rcases h with h | h
      · exact contactSucc_ne (by omega) (x 0) (h.trans he.symm)
      · exact contactSucc_ne (by omega) (x 1) (h.trans he)
    obtain ⟨e,h0,h1⟩ := (contactCycleEdge_pair_iff hne).mpr h
    exact ⟨e,fun k => by fin_cases k <;> assumption⟩
  cases R with
  | inl R =>
    cases R with
    | false =>
      change Fin 2 → Fin n at x
      change (cyclicSucc (x 0) = x 1 ∨ cyclicSucc (x 1) = x 0) ↔ _
      constructor
      · intro h
        obtain ⟨e,he⟩ := hpair x h
        exact ⟨e,h,he⟩
      · rintro ⟨_,h,_⟩
        exact h
    | true =>
      change Fin 3 → Fin n at x
      change False ↔ ∃ e, Function.Injective x ∧ ∀ k, x k ∈ contactCycleEdge n e
      constructor
      · exact False.elim
      · rintro ⟨e,hi,hm⟩
        exact contact_no_injective_triple_in_pair e (cyclicSucc e) x hm hi
  | inr _ =>
    change Fin 2 → Fin n at x
    change (x 0 < x 1 ∧ (cyclicSucc (x 0) = x 1 ∨ cyclicSucc (x 1) = x 0)) ↔
      ∃ e, x 0 < x 1 ∧ ∀ k, x k ∈ contactCycleEdge n e
    constructor
    · rintro ⟨hlt,h⟩
      obtain ⟨e,he⟩ := hpair x h
      exact ⟨e,hlt,he⟩
    · rintro ⟨e,hlt,he⟩
      exact ⟨hlt,(contactCycleEdge_pair_iff (ne_of_lt hlt)).mp ⟨e,he 0,he 1⟩⟩

theorem contactSharpCycle_two_binary (x : Fin 2 → Fin 2) :
    (contactSharpCycle 2).rel false x ↔ x 0 ≠ x 1 := by
  have h (i j : Fin 2) :
      (cyclicSucc i = j ∨ cyclicSucc j = i) ↔ i ≠ j := by
    fin_cases i <;> fin_cases j <;> decide
  exact h (x 0) (x 1)

/-- An actual embedding of the fixed ordered edge, using the increasing
enumeration of any adjacent pair. -/
def contactSharpEdgeEmbedding {n : ℕ} (hn : 3 ≤ n) (i j : Fin n)
    (hlt : i < j) (hadj : cyclicSucc i = j ∨ cyclicSucc j = i) :
    Embedding (contactSharpCycle 2).ordered (contactSharpCycle n).ordered := by
  let f : Fin 2 → Fin n := ![i,j]
  have hf : Function.Injective f := by
    intro a b he
    fin_cases a <;> fin_cases b <;> simp_all [f]
  have hmap (a b : Fin 2) :
      (cyclicSucc (f a) = f b ∨ cyclicSucc (f b) = f a) ↔ a ≠ b := by
    fin_cases a <;> fin_cases b <;>
      simp [f,contactSucc_ne (by omega) i,contactSucc_ne (by omega) j,hadj,hadj.symm]
  have horder (a b : Fin 2) : f a < f b ↔ a < b := by
    fin_cases a <;> fin_cases b <;> simp [f,hlt,lt_asymm hlt]
  refine ⟨f,hf,?_⟩
  intro R x
  cases R with
  | inl R =>
    cases R with
    | false =>
      change Fin 2 → Fin 2 at x
      exact (hmap (x 0) (x 1)).trans (contactSharpCycle_two_binary x).symm
    | true =>
      change Function.Injective (f ∘ x) ↔ Function.Injective x
      exact ⟨Function.Injective.of_comp,fun hi => hf.comp hi⟩
  | inr _ =>
    change Fin 2 → Fin 2 at x
    exact horder (x 0) (x 1)

theorem contactSharpEdgeEmbedding_carrier {n : ℕ} (hn : 3 ≤ n) (i j : Fin n)
    (hlt : i < j) (hadj : cyclicSucc i = j ∨ cyclicSucc j = i) :
    copyCarrier (contactSharpEdgeEmbedding hn i j hlt hadj) = {i,j} := by
  ext x
  change (∃ k : Fin 2, ![i,j] k = x) ↔ x ∈ ({i,j} : Set (Fin n))
  constructor
  · rintro ⟨k,rfl⟩
    fin_cases k <;> simp
  · rintro (h | h)
    · exact ⟨0,h.symm⟩
    · exact ⟨1,h.symm⟩

/-- Every displayed cycle edge is an actual ordered A-copy. -/
theorem contactSharpCycle_edge_copy {n : ℕ} (hn : 3 ≤ n) (e : Fin n) :
    ∃ a : Embedding (contactSharpCycle 2).ordered (contactSharpCycle n).ordered,
      copyCarrier a = contactCycleEdge n e := by
  rcases lt_or_gt_of_ne (contactSucc_ne (by omega) e).symm with hlt | hgt
  · exact ⟨contactSharpEdgeEmbedding hn e (cyclicSucc e) hlt (Or.inl rfl),
      contactSharpEdgeEmbedding_carrier hn e (cyclicSucc e) hlt (Or.inl rfl)⟩
  · refine ⟨contactSharpEdgeEmbedding hn (cyclicSucc e) e hgt (Or.inr rfl),?_⟩
    rw [contactSharpEdgeEmbedding_carrier]
    exact Set.pair_comm _ _

/-- Conversely the actual ordered A-copies are precisely the displayed
cycle edges; there are no additional supports hidden by the encoding. -/
theorem contactSharpCycle_supportCopies {n : ℕ} (hn : 3 ≤ n) :
    supportCopies (contactSharpCycle 2).ordered (contactSharpCycle n).ordered =
      Set.range (contactCycleEdge n) := by
  ext S
  constructor
  · rintro ⟨a,rfl⟩
    have hrel : (contactSharpCycle 2).ordered.rel (.inl false) ![0,1] :=
      (contactSharpCycle_two_binary ![0,1]).mpr (by decide)
    have hadj : cyclicSucc (a 0) = a 1 ∨ cyclicSucc (a 1) = a 0 :=
      (a.map_rel_iff (.inl false) ![0,1]).mpr hrel
    have hne : a 0 ≠ a 1 := fun he => by have := a.injective he; omega
    obtain ⟨e,h0,h1⟩ := (contactCycleEdge_pair_iff hne).mpr hadj
    refine ⟨e,?_⟩
    have he := contact_pair_eq_of_two_distinct hne h0 h1
    change ({e,cyclicSucc e} : Set (Fin n)) = copyCarrier a
    rw [← he]
    ext x
    change x ∈ ({a 0,a 1} : Set (Fin n)) ↔ ∃ k, a k = x
    constructor
    · rintro (h | h)
      · exact ⟨0,h.symm⟩
      · exact ⟨1,h.symm⟩
    · rintro ⟨k,rfl⟩
      fin_cases k <;> simp
  · rintro ⟨e,rfl⟩
    obtain ⟨a,ha⟩ := contactSharpCycle_edge_copy hn e
    exact ⟨a,ha.symm⟩

/-- The girth assumption of the manuscript holds for the actual
ordered-copy support hypergraph, at the sharp parameter. -/
theorem contactSharpCycle_support_girth {n : ℕ} (hn : 3 ≤ n) :
    GirthGT (supportCopies (contactSharpCycle 2).ordered
      (contactSharpCycle n).ordered) (n-1) := by
  classical
  rw [contactSharpCycle_supportCopies hn]
  rintro ⟨C,hC⟩
  choose e he using C.edge_mem
  let D : LabelledBergeCycle (contactCycleEdge n) := {
    length := C.length
    hlength := C.hlength
    label := e
    vertex := C.vertex
    label_injective := by
      intro i j hij
      apply C.edge_injective
      rw [← he i,← he j,hij]
    vertex_injective := C.vertex_injective
    left_mem := fun i => (he i).symm ▸ C.left_mem i
    right_mem := fun i => (he (cyclicSucc i)).symm ▸ C.right_mem i }
  exact contactCycleEdge_girth hn ⟨D,hC⟩

/-- The actual A-members selected in the example, with one label for
each edge of the cycle. -/
noncomputable def contactSharpCycleEdgeMembers {n : ℕ} (hn : 3 ≤ n) :
    Fin n → ABMember (contactSharpCycle 2).ordered
      (contactSharpCycle n).ordered (contactSharpCycle n).ordered := fun i =>
  .a (Classical.choose (contactSharpCycle_edge_copy hn i))

@[simp]
theorem contactSharpCycleEdgeMembers_carrier {n : ℕ} (hn : 3 ≤ n) (i : Fin n) :
    (contactSharpCycleEdgeMembers hn i).carrier = contactCycleEdge n i :=
  Classical.choose_spec (contactSharpCycle_edge_copy hn i)

/-- The explicit edge-union is isomorphic to the formal generated union
of the actual A-members. The equivalence covers every cycle vertex. -/
noncomputable def contactSharpEdgeUnion_iso {n : ℕ} (hn : 3 ≤ n) :
    Iso (contactSharpEdgeUnion n)
      (mixedFamilyUnionStructure (contactSharpCycle n).ordered
        (contactSharpCycleEdgeMembers hn)) where
  toEquiv := {
    toFun := fun x => ⟨x,Set.mem_iUnion.mpr ⟨x,by
      rw [contactSharpCycleEdgeMembers_carrier]
      exact Set.mem_insert _ _⟩⟩
    invFun := Subtype.val
    left_inv := fun _ => rfl
    right_inv := fun _ => Subtype.ext rfl }
  map_rel_iff := by
    intro R x
    change ((contactSharpCycle n).ordered.rel R x ∧
      ∃ i, ∀ k, x k ∈ (contactSharpCycleEdgeMembers hn i).carrier) ↔ _
    simp only [contactSharpCycleEdgeMembers_carrier]
    rw [contactSharpEdgeUnion_relation_union hn]
    constructor
    · rintro ⟨h,⟨i,hi⟩⟩
      exact ⟨i,h,hi⟩
    · rintro ⟨i,h,hi⟩
      exact ⟨h,⟨i,hi⟩⟩

theorem contactSharpEdgeUnion_comparison {n : ℕ} (hn : 3 ≤ n) (i j : Fin n) :
    (contactComparisonGraph (contactSharpEdgeUnion n)).Adj i j ↔
      cyclicSucc i = j ∨ cyclicSucc j = i := by
  change (i ≠ j ∧ ((i < j ∧ _) ∨ (j < i ∧ _))) ↔ _
  constructor
  · rintro ⟨_,h | h⟩
    · exact h.2
    · exact h.2.symm
  · intro h
    have hne : i ≠ j := by
      intro he
      subst j
      rcases h with h | h <;> exact contactSucc_ne (by omega) i h
    refine ⟨hne,?_⟩
    rcases lt_or_gt_of_ne hne with hij | hji
    · exact Or.inl ⟨hij,h⟩
    · exact Or.inr ⟨hji,h.symm⟩

/-- The explicit edge-union in the manuscript cannot already embed
into a supported tree of the ternary-augmented cycle copies. This is
stronger than the failure of the displayed family itself to be a forest. -/
theorem contactSharpEdgeUnion_no_embedding (g : ℕ) (hg : 2 ≤ g)
    {W : Type} (T : RelStructure contactSharpLanguage.withOrder W)
    (hT : ASupportedTreeAmalgam (contactSharpCycle 2).ordered
      (contactSharpCycle (g+1)).ordered W T) :
    ¬ Nonempty (Embedding (contactSharpEdgeUnion (g+1)) T) :=
  contact_ternary_cycle_no_supported_embedding (contactSharpCycle 2) (contactSharpCycle (g+1))
    (contactSharpEdgeUnion (g+1)) true rfl (fun _ hi => hi) (fun _ h => h)
    (by omega) id Function.injective_id (contactSharpEdgeUnion_comparison (by omega)) T hT

theorem contactSharpCycle_mixedUnion_no_embedding (g : ℕ) (hg : 2 ≤ g)
    {W : Type} (T : RelStructure contactSharpLanguage.withOrder W)
    (hT : ASupportedTreeAmalgam (contactSharpCycle 2).ordered
      (contactSharpCycle (g+1)).ordered W T) :
    ¬ Nonempty (Embedding
      (mixedFamilyUnionStructure (contactSharpCycle (g+1)).ordered
        (contactSharpCycleEdgeMembers (by omega))) T) := by
  rintro ⟨e⟩
  exact contactSharpEdgeUnion_no_embedding g hg T hT
    ⟨e.comp (contactSharpEdgeUnion_iso (by omega)).toEmbedding⟩

/-- Adjoin the one ambient B-copy to the actual selected A-members. -/
noncomputable def contactSharpCycleStarMembers {n : ℕ} (hn : 3 ≤ n) :
    Option (Fin n) → ABMember (contactSharpCycle 2).ordered
      (contactSharpCycle n).ordered (contactSharpCycle n).ordered
  | none => .b (Iso.refl _).toEmbedding
  | some i => contactSharpCycleEdgeMembers hn i

theorem contactSharpCycleStarMembers_forest {n : ℕ} (hn : 3 ≤ n) :
    ForestOfCopies (fun i =>
      (contactSharpCycleStarMembers hn i).supportPiece (contactSharpCycle 2).ordered) := by
  constructor
  · intro i j hij
    cases i with
    | none =>
      cases j with
      | none => exact (hij rfl).elim
      | some j =>
        let a := Classical.choose (contactSharpCycle_edge_copy hn j)
        right
        refine ⟨copyCarrier a,?_,Set.mem_singleton _,?_⟩
        · exact ⟨a,rfl,fun x _ => ⟨x,rfl⟩⟩
        · ext x
          exact ⟨And.right,fun hx => ⟨⟨x,rfl⟩,hx⟩⟩
    | some i =>
      cases j with
      | none =>
        let a := Classical.choose (contactSharpCycle_edge_copy hn i)
        right
        refine ⟨copyCarrier a,Set.mem_singleton _,?_,?_⟩
        · exact ⟨a,rfl,fun x _ => ⟨x,rfl⟩⟩
        · ext x
          exact ⟨And.left,fun hx => ⟨hx,⟨x,rfl⟩⟩⟩
      | some j =>
        left
        change ((contactSharpCycleEdgeMembers hn i).carrier ∩
          (contactSharpCycleEdgeMembers hn j).carrier).Subsingleton
        rw [contactSharpCycleEdgeMembers_carrier,contactSharpCycleEdgeMembers_carrier]
        exact contactCycleEdge_linear hn i j (fun he => hij (congrArg some he))
  · right
    exact ⟨{
      tree := SimpleGraph.starGraph (none : Option (Fin n))
      isTree := SimpleGraph.isTree_starGraph none
      running := fun x => starGraph_induce_preconnected_of_mem_center none
        (show x ∈ ((contactSharpCycleStarMembers hn none).supportPiece
          (contactSharpCycle 2).ordered).carrier from ⟨x,rfl⟩) }⟩

/-- With the ambient B-member added, the generated union is B itself,
so the one-member completion also has the required supported-tree
embedding, independently of the forest-to-tree theorem. -/
noncomputable def contactSharpCycleStar_union_iso {n : ℕ} (hn : 3 ≤ n) :
    Iso (mixedFamilyUnionStructure (contactSharpCycle n).ordered
      (contactSharpCycleStarMembers hn)) (contactSharpCycle n).ordered where
  toEquiv := {
    toFun := Subtype.val
    invFun := fun x => ⟨x,Set.mem_iUnion.mpr ⟨none,⟨x,rfl⟩⟩⟩
    left_inv := fun _ => Subtype.ext rfl
    right_inv := fun _ => rfl }
  map_rel_iff := by
    intro R x
    change (contactSharpCycle n).ordered.rel R (Subtype.val ∘ x) ↔
      (contactSharpCycle n).ordered.rel R (Subtype.val ∘ x) ∧
        ∃ i, ∀ k, (x k).val ∈ (contactSharpCycleStarMembers hn i).carrier
    exact ⟨fun h => ⟨h,none,fun k => ⟨(x k).val,rfl⟩⟩,fun h => h.1⟩

theorem contactSharpCycleEdgeMembers_injective {n : ℕ} (hn : 3 ≤ n) :
    Function.Injective (contactSharpCycleEdgeMembers hn) := by
  intro i j he
  apply contactCycleEdge_injective hn
  simpa using congrArg ABMember.carrier he

theorem contactSharpCycleStarMembers_carrier_injective {n : ℕ} (hn : 3 ≤ n) :
    Function.Injective (fun i => (contactSharpCycleStarMembers hn i).carrier) := by
  have heq : (fun i => (contactSharpCycleStarMembers hn i).carrier) =
      (fun i => (contactCompletionStar (Set.range (contactCycleEdge n))
        (contactCycleEdge n) i).carrier) := by
    funext i
    cases i with
    | none =>
      ext x
      exact ⟨fun _ => Set.mem_univ _,fun _ => ⟨x,rfl⟩⟩
    | some i => exact contactSharpCycleEdgeMembers_carrier hn i
  rw [heq]
  exact contactCycleStar_carrier_injective hn

/-- The quantitative example on actual relational members: the source
has the required support girth; its g+1 distinct A-members need a new
member even to embed their union in a supported B-tree; and the single
ambient B-member suffices for the forest. -/
theorem contactSharp_actual_completion (g : ℕ) (hg : 2 ≤ g) :
    GirthGT (supportCopies (contactSharpCycle 2).ordered
      (contactSharpCycle (g+1)).ordered) g ∧
    Function.Injective (contactSharpCycleEdgeMembers (show 3 ≤ g+1 by omega)) ∧
    (∀ (W : Type) (T : RelStructure contactSharpLanguage.withOrder W),
      ASupportedTreeAmalgam (contactSharpCycle 2).ordered
        (contactSharpCycle (g+1)).ordered W T →
      ¬ Nonempty (Embedding
        (mixedFamilyUnionStructure (contactSharpCycle (g+1)).ordered
          (contactSharpCycleEdgeMembers (by omega))) T)) ∧
    ForestOfCopies (fun i =>
      (contactSharpCycleStarMembers (show 3 ≤ g+1 by omega) i).supportPiece
        (contactSharpCycle 2).ordered) ∧
    Nonempty (Embedding
      (mixedFamilyUnionStructure (contactSharpCycle (g+1)).ordered
        (contactSharpCycleStarMembers (by omega))) (contactSharpCycle (g+1)).ordered) ∧
    Function.Injective (fun i =>
      (contactSharpCycleStarMembers (show 3 ≤ g+1 by omega) i).carrier) ∧
    Fintype.card (Fin (g+1)) = g+1 ∧
    Fintype.card (Option (Fin (g+1))) = g+2 ∧
    (g-1)*1 = (g+1)-2 := by
  exact ⟨by simpa using contactSharpCycle_support_girth (show 3 ≤ g+1 by omega),
    contactSharpCycleEdgeMembers_injective (by omega),
    fun _ T hT => contactSharpCycle_mixedUnion_no_embedding g hg T hT,
    contactSharpCycleStarMembers_forest (by omega),
    ⟨(contactSharpCycleStar_union_iso (by omega)).toEmbedding⟩,
    contactSharpCycleStarMembers_carrier_injective (by omega),by simp,by simp,by omega⟩

/-- Every proper subfamily of the displayed cycle edges is an actual
forest. This is the geometric local-completion fact used by the
separate vertex-size sharpness example. -/
theorem contactCycleEdge_small_family_forest {n : ℕ} (hn : 3 ≤ n)
    (S : Finset (Fin n)) (hS : S.card < n) :
    ForestOfCopies (fun i : {i // i ∈ S} =>
      contactInducedHypergraphPiece (Set.range (contactCycleEdge n))
        (contactCycleEdge n i.val)) := by
  classical
  constructor
  · intro i j hij
    left
    exact contactCycleEdge_linear hn i.val j.val (fun h => hij (Subtype.ext h))
  · cases isEmpty_or_nonempty {i // i ∈ S} with
    | inl h => exact Or.inl h
    | inr h =>
      let := h
      obtain ⟨J⟩ := contact_trace_joinTree (contactCycleEdge n)
        (fun i : {i // i ∈ S} => contactCycleEdge n i.val)
        (fun i => Or.inr ⟨i.val,rfl⟩) (contactCycleEdge_linear hn)
        (q := n-1) (by simpa using (show S.card ≤ n-1 by omega))
        (contactCycleEdge_girth hn)
      exact Or.inr ⟨{tree := J.tree,isTree := J.isTree,running := J.running}⟩

/-- Empty base signature for the pure-order cutoff example. -/
def contactSharpPureLanguage : RelLanguage.{0} where
  Symbol := Empty
  arity := Empty.elim

def contactSharpPureBase (W : Type) : RelStructure contactSharpPureLanguage W where
  rel R := Empty.elim R

/-- The cycle oriented by the increasing ambient Fin order. This is
an acyclic directed relation, without completing its comparisons. -/
def contactSharpPureCycle (n : ℕ) :
    RelStructure contactSharpPureLanguage.withOrder (Fin n) where
  rel R := by
    cases R with
    | inl R => exact Empty.elim R
    | inr _ => exact fun x : Fin 2 → Fin n => x 0 < x 1 ∧
        (cyclicSucc (x 0) = x 1 ∨ cyclicSucc (x 1) = x 0)

theorem contactSharpPureCycle_extends (n : ℕ) :
    (contactSharpPureCycle n).ExtendsOrder := fun _ _ h => h.1

theorem contactSharpPureCycle_comparison {n : ℕ} (hn : 3 ≤ n) (i j : Fin n) :
    (contactComparisonGraph (contactSharpPureCycle n)).Adj i j ↔
      cyclicSucc i = j ∨ cyclicSucc j = i :=
  contactSharpEdgeUnion_comparison hn i j

theorem contactSharpPureCycle_not_chordal {n : ℕ} (hn : 4 ≤ n) :
    ¬ ContactChordal (contactComparisonGraph (contactSharpPureCycle n)) := by
  intro hc
  obtain ⟨i,j,_,hi,hj,hadj⟩ := hc n id hn Function.injective_id
    (fun i => (contactSharpPureCycle_comparison (by omega) i (cyclicSucc i)).mpr (Or.inl rfl))
  rcases (contactSharpPureCycle_comparison (by omega) i j).mp hadj with h | h
  · exact hi h
  · exact hj h

theorem contactSharpPureCycle_no_embedding {n : ℕ} (hn : 4 ≤ n)
    {W : Type} (T : RelStructure contactSharpPureLanguage.withOrder W)
    (hT : ASupportedTreeAmalgam (contactSharpPureBase (Fin 2)).ordered
      (contactSharpPureBase (Fin 2)).ordered W T) :
    ¬ Nonempty (Embedding (contactSharpPureCycle n) T) := by
  rintro ⟨e⟩
  exact contactSharpPureCycle_not_chordal hn
    (contactComparisonGraph_chordal_of_supportedTree_embedding e hT)

/-- The geometric obstruction for the vertex cutoff: all edge families
of size at most s-1 are forests, whereas the full s-vertex pure-order
cycle cannot embed in a tree of pure two-point orders. This wrapper
does not assert the other Ramsey-witness clauses for this example. -/
theorem contact_vertex_cutoff_cycle_obstruction (s : ℕ) (hs : 4 ≤ s) :
    (contactSharpPureCycle s).ExtendsOrder ∧
    (∀ S : Finset (Fin s), S.card ≤ s-1 →
      ForestOfCopies (fun i : {i // i ∈ S} =>
        contactInducedHypergraphPiece (Set.range (contactCycleEdge s))
          (contactCycleEdge s i.val))) ∧
    (∀ (W : Type) (T : RelStructure contactSharpPureLanguage.withOrder W),
      ASupportedTreeAmalgam (contactSharpPureBase (Fin 2)).ordered
        (contactSharpPureBase (Fin 2)).ordered W T →
      ¬ Nonempty (Embedding (contactSharpPureCycle s) T)) := by
  exact ⟨contactSharpPureCycle_extends s,
    fun S hS => contactCycleEdge_small_family_forest (by omega) S (by omega),
    fun _ T hT => contactSharpPureCycle_no_embedding hs T hT⟩

end StructuralRamsey.Girth
