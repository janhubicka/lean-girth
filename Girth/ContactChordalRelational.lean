import Girth.ContactSmallRelational
import Girth.SupportedCopyForest
import Girth.ContactChordalTreeEmbedding
import Girth.ContactTreeAmalgamChordal
import Mathlib.Order.Preorder.Finite

/-! Select actual B-copies above the distinct maximal comparison cliques.
Their traces, rather than their full carriers, have a join tree. This is
the input for the separate supported tree-unfolding construction. -/

namespace StructuralRamsey.Girth
open StructuralRamsey.RelStructure
universe u v
variable {L : RelLanguage.{u}} {U V W : Type v}

theorem contactComparisonGraph_induce
    (C : RelStructure L.withOrder W) (Z : Set W) :
    contactComparisonGraph (C.induce Z) = (contactComparisonGraph C).induce Z := by
  ext x y
  exact (contactComparisonGraph_embedding (C.inclusion Z) x y).symm

theorem contact_clique_pair {G : SimpleGraph W} {x y : W} (h : G.Adj x y) :
    ContactClique G {x,y} := by
  intro z hz w hw hn
  rcases Set.mem_insert_iff.mp hz with rfl | hz
  · rcases Set.mem_insert_iff.mp hw with rfl | hw
    · exact (hn rfl).elim
    · have he := Set.mem_singleton_iff.mp hw
      subst w
      exact h
  · have he := Set.mem_singleton_iff.mp hz
    subst z
    rcases Set.mem_insert_iff.mp hw with rfl | hw
    · exact h.symm
    · have he := Set.mem_singleton_iff.mp hw
      subst w
      exact (hn rfl).elim

structure ContactChordalCopyWitness
    (A : RelStructure L U) (B : RelStructure L V)
    [LinearOrder U] [LinearOrder V]
    (C : RelStructure L.withOrder W) (Z : Set W) where
  Index : Type v
  finite : Finite Index
  nonempty : Nonempty Index
  copy : Index → Embedding B.ordered C
  tree : ContactJoinTree (fun i => Z ∩ copyCarrier (copy i))
  covered : ∀ x ∈ Z, ∃ i, x ∈ copyCarrier (copy i)
  tuple_covered : ∀ (r : L.withOrder.Symbol) (x : Fin (L.withOrder.arity r) → W),
    (∀ k, x k ∈ Z) → C.rel r x → ∃ i, ∀ k, x k ∈ copyCarrier (copy i)
  overlap : PairwiseSupportedBCopyOverlap A.ordered copy

/-- Maximal cliques have exact traces in their chosen B-copies.
This is valid for arbitrary Z, with no bound on its cardinality. -/
theorem contact_chordal_copyWitness
    {A : RelStructure L U} {B : RelStructure L V}
    [LinearOrder U] [LinearOrder V] [Finite W]
    {C : RelStructure L.withOrder W}
    (hcover : ∀ S : Set W, (C.induce S).Irreducible →
      ∃ b : Embedding B.ordered C, S ⊆ copyCarrier b)
    (hInter : BIntersectionsControlled A.ordered B.ordered C)
    (hShared : BSingletonIntersectionsSupported A.ordered B.ordered C)
    (Z : Set W) (hch : ContactChordal ((contactComparisonGraph C).induce Z)) :
    Nonempty (ContactChordalCopyWitness A B C Z) := by
  classical
  letI : Fintype W := Fintype.ofFinite _
  letI : Fintype Z := Fintype.ofFinite _
  let G := (contactComparisonGraph C).induce Z
  let I := {K : Set Z // Maximal (ContactClique G) K}
  letI : Fintype I := Fintype.ofFinite _
  have hmax (K : Set Z) (hK : ContactClique G K) : ∃ i : I, K ⊆ i.val := by
    obtain ⟨T,hKT,hT⟩ := Finite.exists_le_maximal hK
    exact ⟨⟨T,hT⟩,hKT⟩
  letI : Nonempty I := by
    obtain ⟨i,_⟩ := hmax ∅ (by intro x hx; exact hx.elim)
    exact ⟨i⟩
  have hbag (i : I) : ∃ b : Embedding B.ordered C,
      Subtype.val '' i.val ⊆ copyCarrier b := by
    apply hcover
    apply contact_comparison_clique_irreducible
    rintro _ ⟨x,hx,rfl⟩ _ ⟨y,hy,rfl⟩ hxy
    exact i.property.1 x hx y hy (fun he => hxy (congrArg Subtype.val he))
  choose b hb using hbag
  have htrace (i : I) : Z ∩ copyCarrier (b i) = Subtype.val '' i.val := by
    let K : Set Z := {z | z.val ∈ copyCarrier (b i)}
    have hK : ContactClique G K := by
      intro x hx y hy hxy
      exact contactComparisonGraph_embedding_ordered (b i) _ hx _ hy
        (fun he => hxy (Subtype.ext he))
    have hiK : i.val ⊆ K := by
      intro x hx
      exact hb i ⟨x,hx,rfl⟩
    have hKi : K ⊆ i.val := i.property.2 hK hiK
    ext x
    constructor
    · intro hx
      exact ⟨⟨x,hx.1⟩,hKi hx.2,rfl⟩
    · rintro ⟨z,hz,rfl⟩
      exact ⟨z.property,hb i ⟨z,hz,rfl⟩⟩
  have hDistinct : Function.Injective (fun i => copyCarrier (b i)) := by
    intro i j he
    change copyCarrier (b i) = copyCarrier (b j) at he
    apply Subtype.ext
    have ht : Subtype.val '' i.val = Subtype.val '' j.val := by
      rw [← htrace i,← htrace j,he]
    ext z
    constructor
    · intro hz
      have hz' : z.val ∈ Subtype.val '' j.val := ht ▸ (show z.val ∈ Subtype.val '' i.val from ⟨z,hz,rfl⟩)
      obtain ⟨y,hy,hye⟩ := hz'
      have he : y = z := Subtype.ext hye
      exact he ▸ hy
    · intro hz
      have hz' : z.val ∈ Subtype.val '' i.val := ht.symm ▸ (show z.val ∈ Subtype.val '' j.val from ⟨z,hz,rfl⟩)
      obtain ⟨y,hy,hye⟩ := hz'
      have he : y = z := Subtype.ext hye
      exact he ▸ hy
  have hgraph : contactFamilyGraph (fun i : I => i.val) = G := by
    ext x y
    constructor
    · rintro ⟨hne,i,hx,hy⟩
      exact i.property.1 x hx y hy hne
    · intro h
      obtain ⟨i,hi⟩ := hmax {x,y} (contact_clique_pair h)
      exact ⟨h.ne,i,hi (Set.mem_insert x _),hi (Set.mem_insert_of_mem _ (Set.mem_singleton y))⟩
  have hconf : ContactConformal (fun i : I => i.val) := by
    intro s _ _ hp
    have hK : ContactClique G (s : Set Z) := by
      intro x hx y hy hxy
      obtain ⟨i,hix,hiy⟩ := hp x hx y hy hxy
      exact i.property.1 x hix y hiy hxy
    exact hmax (s : Set Z) hK
  obtain ⟨J⟩ := contact_joinTree_of_chordal_conformal (fun i : I => i.val)
    (hgraph.symm ▸ hch) hconf
  let J' : ContactJoinTree (fun i : I => Z ∩ copyCarrier (b i)) := {
    tree := J.tree
    isTree := J.isTree
    running := by
      intro x
      by_cases hx : x ∈ Z
      · let z : Z := ⟨x,hx⟩
        have he : {i : I | x ∈ Z ∩ copyCarrier (b i)} = {i : I | z ∈ i.val} := by
          ext i
          change x ∈ Z ∩ copyCarrier (b i) ↔ z ∈ i.val
          rw [htrace i]
          constructor
          · rintro ⟨y,hy,hye⟩
            have he : y = z := Subtype.ext hye
            exact he ▸ hy
          · intro hz
            exact ⟨z,hz,rfl⟩
        exact Eq.mpr (congrArg (fun K : Set I => (J.tree.induce K).Preconnected) he) (J.running z)
      · intro i _
        exact (hx i.property.1).elim }
  have hCov : ∀ x ∈ Z, ∃ i : I, x ∈ copyCarrier (b i) := by
    intro x hx
    let z : Z := ⟨x,hx⟩
    have hsingle : ContactClique G {z} := by
      intro y hy w hw hn
      exact (hn ((Set.mem_singleton_iff.mp hy).trans (Set.mem_singleton_iff.mp hw).symm)).elim
    obtain ⟨i,hi⟩ := hmax {z} hsingle
    exact ⟨i,hb i ⟨z,hi (Set.mem_singleton z),rfl⟩⟩
  have hTuple : ∀ (r : L.withOrder.Symbol) (x : Fin (L.withOrder.arity r) → W),
      (∀ k, x k ∈ Z) → C.rel r x → ∃ i : I, ∀ k, x k ∈ copyCarrier (b i) := by
    intro r x hxZ hx
    let y (k : Fin (L.withOrder.arity r)) : Z := ⟨x k,hxZ k⟩
    obtain ⟨d,hd⟩ := hcover (Set.range x) (contact_relation_range_irreducible r x hx)
    have hK : ContactClique G (Set.range y) := by
      rintro z ⟨i,rfl⟩ w ⟨j,rfl⟩ hij
      exact contactComparisonGraph_embedding_ordered d _ (hd ⟨i,rfl⟩) _ (hd ⟨j,rfl⟩)
        (fun he => hij (Subtype.ext he))
    obtain ⟨i,hi⟩ := hmax (Set.range y) hK
    exact ⟨i,fun k => hb i ⟨y k,hi ⟨k,rfl⟩,rfl⟩⟩
  have hOver : PairwiseSupportedBCopyOverlap A.ordered b := by
    intro i j hij
    have hn : ¬ SameCopy (b i) (b j) := fun he => hij (hDistinct he)
    rcases hInter (b i) (b j) hn with hs | ⟨a,ha⟩
    · by_cases he : (copyCarrier (b i) ∩ copyCarrier (b j)).Nonempty
      · obtain ⟨x,hx⟩ := he
        have hEq : copyCarrier (b i) ∩ copyCarrier (b j) = {x} := by
          ext y
          constructor
          · intro hy
            exact Set.mem_singleton_iff.mpr (hs hy hx)
          · intro hy
            exact (Set.mem_singleton_iff.mp hy).symm ▸ hx
        obtain ⟨hi,hj⟩ := hShared (b i) (b j) hn hs x hx
        exact Or.inr (Or.inr ⟨x,hEq,hi,hj⟩)
      · exact Or.inl (Set.not_nonempty_iff_eq_empty.mp he)
    · exact Or.inr (Or.inl ⟨a,ha⟩)
  exact ⟨{
    Index := I
    finite := inferInstance
    nonempty := inferInstance
    copy := b
    tree := J'
    covered := hCov
    tuple_covered := hTuple
    overlap := hOver }⟩

/-- Sufficiency of chordality for arbitrary induced vertex sets.
Unlike the small-size consequence, this uses only irreducible cover
and supported pair intersections; no completion cutoff is assumed. -/
theorem contact_induced_supported_of_chordal
    {A : RelStructure L U} {B : RelStructure L V}
    [LinearOrder U] [LinearOrder V] [Nontrivial U] [Finite W]
    {C : RelStructure L.withOrder W}
    (α : Embedding A.ordered B.ordered)
    (hcover : ∀ S : Set W, (C.induce S).Irreducible →
      ∃ b : Embedding B.ordered C, S ⊆ copyCarrier b)
    (hInter : BIntersectionsControlled A.ordered B.ordered C)
    (hShared : BSingletonIntersectionsSupported A.ordered B.ordered C)
    (Z : Set W) (hch : ContactChordal ((contactComparisonGraph C).induce Z)) :
    ∃ (X : Type v) (T : RelStructure L.withOrder X)
      (e : Embedding (C.induce Z) T),
      ASupportedTreeAmalgam A.ordered B.ordered X T := by
  classical
  obtain ⟨K⟩ := contact_chordal_copyWitness hcover hInter hShared Z hch
  letI : Finite K.Index := K.finite
  letI : Fintype K.Index := Fintype.ofFinite _
  letI : Nonempty K.Index := K.nonempty
  obtain ⟨a₀,a₁,hne⟩ := exists_pair_ne U
  exact contact_trace_tree_embeds_supported K.copy Z K.tree K.overlap K.covered
    (fun r x hx hZ => K.tuple_covered r x hZ hx) α a₀ a₁ hne

/-- The full chordality criterion from the manuscript, for arbitrary
Z rather than only sets below the completion cutoff. -/
theorem contact_induced_supported_iff_chordal
    {A : RelStructure L U} {B : RelStructure L V}
    [LinearOrder U] [LinearOrder V] [Nontrivial U] [Finite W]
    {C : RelStructure L.withOrder W}
    (α : Embedding A.ordered B.ordered)
    (hcover : ∀ S : Set W, (C.induce S).Irreducible →
      ∃ b : Embedding B.ordered C, S ⊆ copyCarrier b)
    (hInter : BIntersectionsControlled A.ordered B.ordered C)
    (hShared : BSingletonIntersectionsSupported A.ordered B.ordered C)
    (Z : Set W) :
    (∃ (X : Type v) (T : RelStructure L.withOrder X)
      (e : Embedding (C.induce Z) T), ASupportedTreeAmalgam A.ordered B.ordered X T) ↔
      ContactChordal ((contactComparisonGraph C).induce Z) := by
  constructor
  · rintro ⟨X,T,e,hT⟩
    have h := contactComparisonGraph_chordal_of_supportedTree_embedding e hT
    rw [contactComparisonGraph_induce] at h
    exact h
  · exact contact_induced_supported_of_chordal α hcover hInter hShared Z

end StructuralRamsey.Girth
