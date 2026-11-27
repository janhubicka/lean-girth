import Girth.ContactCompletionSharpness
import Girth.ContactCarrierCompletion
import Girth.ContactPureCycleCover

/-!
# Sharpness of the small-vertex cutoff

For every `s ≥ 4`, the pure order obtained by orienting the edges of
the chordless `s`-cycle by the ambient `Fin s` order satisfies every
clause of the relational theorem at `A = B =` the two-point order,
`g = 2`, and `n = s - 1`.  The literal set-family completion uses no
additional members.  The whole `s`-vertex structure cannot embed in
an `A`-supported tree amalgam of copies of `B`.
-/

namespace StructuralRamsey.Girth
open StructuralRamsey.RelStructure

/-- The fixed pure two-point ordered structure in the sharpness example. -/
abbrev contactSharpTwoPoint := (contactSharpPureBase (Fin 2)).ordered

/-- Increasing enumeration of an actual cycle edge as a pure ordered copy. -/
def contactSharpPureEdgeEmbedding {n : ℕ} (i j : Fin n)
    (hlt : i < j) (hadj : cyclicSucc i = j ∨ cyclicSucc j = i) :
    Embedding contactSharpTwoPoint (contactSharpPureCycle n) := by
  let f : Fin 2 → Fin n := ![i,j]
  have hf : Function.Injective f := by
    intro a b he
    fin_cases a <;> fin_cases b <;> simp_all [f]
  have horder (a b : Fin 2) :
      (f a < f b ∧ (cyclicSucc (f a) = f b ∨ cyclicSucc (f b) = f a)) ↔ a < b := by
    fin_cases a <;> fin_cases b <;> simp [f,hlt,lt_asymm hlt,hadj]
  refine ⟨f,hf,?_⟩
  intro R x
  cases R with
  | inl R => exact Empty.elim R
  | inr _ =>
    change Fin 2 → Fin 2 at x
    exact horder (x 0) (x 1)

theorem contactSharpPureEdgeEmbedding_carrier {n : ℕ} (i j : Fin n)
    (hlt : i < j) (hadj : cyclicSucc i = j ∨ cyclicSucc j = i) :
    copyCarrier (contactSharpPureEdgeEmbedding i j hlt hadj) = {i,j} := by
  ext x
  change (∃ k : Fin 2, ![i,j] k = x) ↔ x ∈ ({i,j} : Set (Fin n))
  constructor
  · rintro ⟨k,rfl⟩
    fin_cases k <;> simp
  · rintro (h | h)
    · exact ⟨0,h.symm⟩
    · exact ⟨1,h.symm⟩

theorem contactSharpPureCycle_edge_copy {n : ℕ} (hn : 3 ≤ n) (e : Fin n) :
    ∃ a : Embedding contactSharpTwoPoint (contactSharpPureCycle n),
      copyCarrier a = contactCycleEdge n e := by
  rcases lt_or_gt_of_ne (contactSucc_ne (by omega) e).symm with hlt | hgt
  · exact ⟨contactSharpPureEdgeEmbedding e (cyclicSucc e) hlt (Or.inl rfl),
      contactSharpPureEdgeEmbedding_carrier e (cyclicSucc e) hlt (Or.inl rfl)⟩
  · refine ⟨contactSharpPureEdgeEmbedding (cyclicSucc e) e hgt (Or.inr rfl),?_⟩
    rw [contactSharpPureEdgeEmbedding_carrier]
    exact Set.pair_comm _ _

/-- There are no additional two-point copies besides the cycle edges. -/
theorem contactSharpPureCycle_embedding_edge {n : ℕ}
    (a : Embedding contactSharpTwoPoint (contactSharpPureCycle n)) :
    ∃ e, copyCarrier a = contactCycleEdge n e := by
  have hrel : (contactSharpPureCycle n).rel (.inr ()) (a.toFun ∘ ![0,1]) :=
    (a.map_rel_iff (.inr ()) ![0,1]).mpr (by change (0 : Fin 2) < 1; decide)
  have hadj : cyclicSucc (a 0) = a 1 ∨ cyclicSucc (a 1) = a 0 := hrel.2
  have hne : a 0 ≠ a 1 := fun he => by have := a.injective he; omega
  obtain ⟨e,h0,h1⟩ := (contactCycleEdge_pair_iff hne).mpr hadj
  refine ⟨e,?_⟩
  have he := contact_pair_eq_of_two_distinct hne h0 h1
  change copyCarrier a = ({e,cyclicSucc e} : Set (Fin n))
  rw [← he]
  ext x
  change (∃ k, a k = x) ↔ x ∈ ({a 0,a 1} : Set (Fin n))
  constructor
  · rintro ⟨k,rfl⟩
    fin_cases k <;> simp
  · rintro (h | h)
    · exact ⟨0,h.symm⟩
    · exact ⟨1,h.symm⟩

theorem contactSharpPureCycle_supportCopies {n : ℕ} (hn : 3 ≤ n) :
    supportCopies contactSharpTwoPoint (contactSharpPureCycle n) =
      Set.range (contactCycleEdge n) := by
  ext S
  constructor
  · rintro ⟨a,rfl⟩
    obtain ⟨e,he⟩ := contactSharpPureCycle_embedding_edge a
    exact ⟨e,he.symm⟩
  · rintro ⟨e,rfl⟩
    obtain ⟨a,ha⟩ := contactSharpPureCycle_edge_copy hn e
    exact ⟨a,ha.symm⟩

/-- The union of the A- and B-copy sets is the same edge family, with
each carrier counted once even though A and B coincide. -/
theorem contactSharpPureCycle_actual_carriers {n : ℕ} (hn : 3 ≤ n) :
    Set.range (ContactActualCarrier.carrier (A := contactSharpTwoPoint)
      (B := contactSharpTwoPoint) (C := contactSharpPureCycle n)) =
        Set.range (contactCycleEdge n) := by
  ext S
  constructor
  · rintro ⟨a,rfl⟩
    cases a with
    | inl a =>
      obtain ⟨e,he⟩ := contactSharpPureCycle_embedding_edge a
      exact ⟨e,he.symm⟩
    | inr a =>
      obtain ⟨e,he⟩ := contactSharpPureCycle_embedding_edge a
      exact ⟨e,he.symm⟩
  · rintro ⟨e,rfl⟩
    obtain ⟨a,ha⟩ := contactSharpPureCycle_edge_copy hn e
    exact ⟨Sum.inl a,ha⟩

theorem contactSharpPureCycle_support_girth {n : ℕ} (hn : 3 ≤ n) :
    GirthGT (supportCopies contactSharpTwoPoint (contactSharpPureCycle n)) (n-1) := by
  classical
  rw [contactSharpPureCycle_supportCopies hn]
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

theorem contactSharpTwoPoint_support_girth (g : ℕ) :
    GirthGT (supportCopies contactSharpTwoPoint contactSharpTwoPoint) g := by
  apply girthGT_of_edgeFamily_subsingleton ?_ g
  rintro S ⟨a,rfl⟩ T ⟨b,rfl⟩
  have ha : copyCarrier a = Set.univ :=
    Set.range_eq_univ.mpr (Finite.surjective_of_injective a.injective)
  have hb : copyCarrier b = Set.univ :=
    Set.range_eq_univ.mpr (Finite.surjective_of_injective b.injective)
  exact ha.trans hb.symm

/-- The arrow is valid for every colour type, since a two-point order
has exactly one self-embedding. -/
theorem contactSharpPureCycle_arrow {n : ℕ} (hn : 3 ≤ n) (Color : Type*) :
    StructuralRamsey.Arrow contactSharpTwoPoint contactSharpTwoPoint
      (contactSharpPureCycle n) Color := by
  obtain ⟨b,_⟩ := contactSharpPureCycle_edge_copy hn ⟨0,by omega⟩
  intro χ
  refine ⟨b,?_⟩
  intro e₁ e₂
  have he : e₁ = e₂ := Embedding.ext (congrFun
    ((StrictMono.eq_id (Embedding.strictMono e₁)).trans
      (StrictMono.eq_id (Embedding.strictMono e₂)).symm))
  rw [he]

theorem contactSharpPureCycle_linear {n : ℕ} (hn : 3 ≤ n) :
    ALinear contactSharpTwoPoint (contactSharpPureCycle n) := by
  intro a b hne
  obtain ⟨i,hi⟩ := contactSharpPureCycle_embedding_edge a
  obtain ⟨j,hj⟩ := contactSharpPureCycle_embedding_edge b
  have hij : i ≠ j := fun he => hne (hi.trans ((congrArg (contactCycleEdge n) he).trans hj.symm))
  rw [hi,hj]
  exact contactCycleEdge_linear hn i j hij

theorem contactSharpPureCycle_strong {n : ℕ} (hn : 3 ≤ n)
    (b : Embedding contactSharpTwoPoint (contactSharpPureCycle n)) :
    AStrong contactSharpTwoPoint (contactSharpPureCycle n) (copyCarrier b) := by
  intro a hlarge
  by_cases he : SameCopy a b
  · exact he ▸ Set.Subset.rfl
  · exact (hlarge (contactSharpPureCycle_linear hn a b he)).elim

theorem contactSharpPureCycle_intersections {n : ℕ} (hn : 3 ≤ n) :
    BIntersectionsControlled contactSharpTwoPoint contactSharpTwoPoint
      (contactSharpPureCycle n) :=
  fun a b hne => Or.inl (contactSharpPureCycle_linear hn a b hne)

theorem contactSharpPureCycle_shared_support (n : ℕ) :
    BSingletonIntersectionsSupported contactSharpTwoPoint contactSharpTwoPoint
      (contactSharpPureCycle n) := by
  intro a b _ _ x hx
  exact ⟨⟨a,hx.1,Set.Subset.rfl⟩,⟨b,hx.2,Set.Subset.rfl⟩⟩

/-- A- and B-members have the same one-edge support hypergraph when
both sources are the two-point order. -/
theorem contactSharpTwoPoint_member_support_edges
    {W : Type} {C : RelStructure contactSharpPureLanguage.withOrder W}
    (m : ABMember contactSharpTwoPoint contactSharpTwoPoint C) :
    (m.supportPiece contactSharpTwoPoint).edges = {m.carrier} := by
  cases m with
  | a a => rfl
  | b b =>
    ext S
    change (∃ a : Embedding contactSharpTwoPoint C,
      copyCarrier a = S ∧ copyCarrier a ⊆ copyCarrier b) ↔ S ∈ {copyCarrier b}
    constructor
    · rintro ⟨a,ha,hsub⟩
      have he : SameCopy a b := sameCopy_of_range_subset a b (fun x => by
        obtain ⟨y,hy⟩ := hsub ⟨x,rfl⟩
        exact ⟨y,hy.symm⟩)
      exact Set.mem_singleton_iff.mpr (ha.symm.trans he)
    · intro hS
      exact ⟨b,(Set.mem_singleton_iff.mp hS).symm,Set.Subset.rfl⟩

/-- Every nonempty proper selected family of actual carrier sets is
already a forest and its generated relational union has the required
supported-tree embedding.  No completion member is added. -/
theorem contactSharpPureCycle_small_family {n : ℕ} (hn : 3 ≤ n)
    (s : Finset (Set (Fin n))) (hs : s.Nonempty) (hsc : s.card ≤ n-1)
    (hsrc : ∀ X ∈ s, X ∈ Set.range (ContactActualCarrier.carrier
      (A := contactSharpTwoPoint) (B := contactSharpTwoPoint)
      (C := contactSharpPureCycle n))) :
    ∃ m : {X // X ∈ s} → ABMember contactSharpTwoPoint contactSharpTwoPoint
        (contactSharpPureCycle n),
      (∀ X, (m X).carrier = X.val) ∧
      ForestOfCopies (fun X => (m X).supportPiece contactSharpTwoPoint) ∧
      ∃ (W : Type) (T : RelStructure contactSharpPureLanguage.withOrder W)
        (_e : Embedding (mixedFamilyUnionStructure (contactSharpPureCycle n) m) T),
        ASupportedTreeAmalgam contactSharpTwoPoint contactSharpTwoPoint W T := by
  classical
  let I := {X : Set (Fin n) // X ∈ s}
  have : Nonempty I := by
    obtain ⟨X,hX⟩ := hs
    exact ⟨⟨X,hX⟩⟩
  have hex (X : I) : ∃ b : Embedding contactSharpTwoPoint (contactSharpPureCycle n),
      copyCarrier b = X.val := by
    obtain ⟨a,ha⟩ := hsrc X.val X.property
    cases a with
    | inl a => exact ⟨a,ha⟩
    | inr a => exact ⟨a,ha⟩
  choose b hb using hex
  let m : I → ABMember contactSharpTwoPoint contactSharpTwoPoint
      (contactSharpPureCycle n) := fun X => .a (b X)
  have hm (X : I) : (m X).carrier = X.val := hb X
  have ht : ContactEdgeTraces (contactCycleEdge n) (fun X : I => X.val) := by
    intro X
    obtain ⟨i,hi⟩ := contactSharpPureCycle_embedding_edge (b X)
    exact Or.inr ⟨i,(hb X).symm.trans hi⟩
  obtain ⟨J⟩ := contact_trace_joinTree (contactCycleEdge n) (fun X : I => X.val)
    ht (contactCycleEdge_linear hn) (q := n-1)
    (by simpa [I] using hsc) (contactCycleEdge_girth hn)
  have hforest : ForestOfCopies (fun X => (m X).supportPiece contactSharpTwoPoint) := by
    constructor
    · intro X Y hne
      left
      apply contactSharpPureCycle_linear hn (b X) (b Y)
      intro he
      apply hne
      apply Subtype.ext
      exact (hb X).symm.trans (he.trans (hb Y))
    · right
      refine ⟨{tree := J.tree, isTree := J.isTree, running := ?_}⟩
      intro x
      change (J.tree.induce {X : I | x ∈ copyCarrier (b X)}).Preconnected
      have hsets : {X : I | x ∈ copyCarrier (b X)} = {X : I | x ∈ X.val} := by
        ext X
        change x ∈ copyCarrier (b X) ↔ x ∈ X.val
        rw [hb X]
      rw [hsets]
      exact J.running x
  have hshared : PairwiseMixedSharedVerticesSupported contactSharpTwoPoint m := by
    intro X Y _ x hx hy
    exact ⟨⟨b X,hx,Set.Subset.rfl⟩,⟨b Y,hy,Set.Subset.rfl⟩⟩
  refine ⟨m,hm,hforest,?_⟩
  exact mixedForest_embeds_supportedTree hforest hshared
    (Embedding.id contactSharpTwoPoint) (0 : Fin 2) 1 (by decide)

/-- Literal clause (iv) at g=2 and n=s-1, with the completion family
equal to the requested carrier-set family. -/
theorem contactSharpPureCycle_completion {n : ℕ} (hn : 3 ≤ n) :
    ContactCarrierMixedCompletion contactSharpTwoPoint contactSharpTwoPoint
      (contactSharpPureCycle n) 2 (n-1) := by
  classical
  intro s hs hsc hsrc
  obtain ⟨m,hm,hforest,hunion⟩ := contactSharpPureCycle_small_family hn s hs hsc hsrc
  exact ⟨s,Finset.Subset.rfl,fun _ hX hnot => (hnot hX).elim,
    fun _ => rfl,by simp,m,hm,hforest,hunion⟩

theorem contactSharpPureCycle_irreducible_cover {n : ℕ} (hn : 4 ≤ n)
    (S : Set (Fin n)) (hS : ((contactSharpPureCycle n).induce S).Irreducible) :
    ∃ b : Embedding contactSharpTwoPoint (contactSharpPureCycle n),
      S ⊆ copyCarrier b := by
  obtain ⟨i,hi⟩ := contactSharpPureCycle_irreducible_edge hn S hS
  obtain ⟨b,hb⟩ := contactSharpPureCycle_edge_copy (by omega) i
  exact ⟨b,hb.symm ▸ hi⟩

/-- The source structures satisfy all input requirements, including
support girth at every finite cutoff. -/
theorem contactSharpTwoPoint_input (g : ℕ) :
    2 ≤ Fintype.card (Fin 2) ∧
    Nonempty (Embedding contactSharpTwoPoint contactSharpTwoPoint) ∧
    GirthGT (supportCopies contactSharpTwoPoint contactSharpTwoPoint) g :=
  ⟨by simp,⟨Embedding.id _⟩,contactSharpTwoPoint_support_girth g⟩

/-- The exact vertex-bound sharpness paragraph: the explicit s-cycle
satisfies all five clauses of the relational theorem at g=2 and n=s-1,
for every colour type, while its full s-vertex induced structure does
not embed in any supported tree of the prescribed two-point copies. -/
theorem contact_vertex_cutoff_sharp (s : ℕ) (hs : 4 ≤ s) (Color : Type*) :
    Finite (Fin s) ∧
    (contactSharpPureCycle s).ExtendsOrder ∧
    StructuralRamsey.Arrow contactSharpTwoPoint contactSharpTwoPoint
      (contactSharpPureCycle s) Color ∧
    (∀ S : Set (Fin s), ((contactSharpPureCycle s).induce S).Irreducible →
      ∃ b : Embedding contactSharpTwoPoint (contactSharpPureCycle s),
        S ⊆ copyCarrier b) ∧
    ContactCarrierMixedCompletion contactSharpTwoPoint contactSharpTwoPoint
      (contactSharpPureCycle s) 2 (s-1) ∧
    GirthGT (supportCopies contactSharpTwoPoint (contactSharpPureCycle s)) 2 ∧
    (∀ b : Embedding contactSharpTwoPoint (contactSharpPureCycle s),
      AStrong contactSharpTwoPoint (contactSharpPureCycle s) (copyCarrier b)) ∧
    BIntersectionsControlled contactSharpTwoPoint contactSharpTwoPoint (contactSharpPureCycle s) ∧
    BSingletonIntersectionsSupported contactSharpTwoPoint contactSharpTwoPoint
      (contactSharpPureCycle s) ∧
    Fintype.card (Fin s) = s ∧
    ¬ ContactChordal (contactComparisonGraph (contactSharpPureCycle s)) ∧
    (∀ (W : Type) (T : RelStructure contactSharpPureLanguage.withOrder W),
      ASupportedTreeAmalgam contactSharpTwoPoint contactSharpTwoPoint W T →
      ¬ Nonempty (Embedding (contactSharpPureCycle s) T)) := by
  have hs3 : 3 ≤ s := by omega
  exact ⟨inferInstance,contactSharpPureCycle_extends s,
    contactSharpPureCycle_arrow hs3 Color,contactSharpPureCycle_irreducible_cover hs,
    contactSharpPureCycle_completion hs3,
    girthGT_mono (contactSharpPureCycle_support_girth hs3) (by omega),
    contactSharpPureCycle_strong hs3,contactSharpPureCycle_intersections hs3,
    contactSharpPureCycle_shared_support s,by simp,
    contactSharpPureCycle_not_chordal hs,fun _ T hT => contactSharpPureCycle_no_embedding hs T hT⟩

end StructuralRamsey.Girth
