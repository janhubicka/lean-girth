import Girth.ContactWordStrip
import Girth.ContactTrainBottom
import Girth.ContactTrainEmbedding
import Girth.ContactZeroJoinTrees
import Girth.ContactJoinTreeCharacterization
import Girth.Berge
import PartiteConstruction.Iterated.Ordered

/-! Relational realization of the actual support picture.
The ambient order is deliberately NOT completed: the relational
union is taken on the original B-copies, including their orders.
Only a compatible external order is used to show acyclicity and
uniqueness of order-preserving enumerations. -/

namespace StructuralRamsey.Girth
open StructuralRamsey.RelStructure
universe u v
variable {L : RelLanguage.{u}} {U V W F J : Type v}

/-- The source support has one label per A-embedding. In ordered
sources this is precisely one label per actual A-image. -/
def contactRelationalTarget (A : RelStructure L U) (B : RelStructure L V) :
    ContactHypergraphData V (Embedding A B) PEmpty.{v+1} where
  edgeCarrier := fun e => copyCarrier e
  copyCarrier := PEmpty.elim
  copyEdges := PEmpty.elim

theorem contactRelationalTarget_girth
    {A : RelStructure L U} {B : RelStructure L V}
    [LinearOrder U] [LinearOrder V] [Finite U]
    {g : ℕ} (h : GirthGT (supportCopies A.ordered B.ordered) g) :
    LabelledGirthGT (contactRelationalTarget A.ordered B.ordered).edgeCarrier g := by
  rintro ⟨C,hC⟩
  let D : BergeCycle (supportCopies A.ordered B.ordered) := {
    length := C.length
    hlength := C.hlength
    edge := fun i => copyCarrier (C.label i)
    vertex := C.vertex
    edge_mem := fun i => ⟨C.label i,rfl⟩
    edge_injective := fun i j he =>
      C.label_injective (ordered_embedding_eq_of_sameCopy _ _ he)
    vertex_injective := C.vertex_injective
    left_mem := C.left_mem
    right_mem := C.right_mem }
  exact h ⟨D,hC⟩

/-- Equal ranges of two increasing injections from a finite ordered
source determine the same map, irrespective of the extra language. -/
theorem contact_strictMono_eq_of_range_eq [Finite U] [LinearOrder U] [LinearOrder W]
    (f g : U → W) (hf : StrictMono f) (hg : StrictMono g)
    (hr : Set.range f = Set.range g) : f = g := by
  classical
  have hex (x : U) : ∃ y, g y = f x := by
    have hx : f x ∈ Set.range g := hr ▸ (show f x ∈ Set.range f from ⟨x,rfl⟩)
    exact hx
  choose k hk using hex
  have hm : StrictMono k := by
    intro x y hxy
    apply hg.lt_iff_lt.mp
    rw [hk x,hk y]
    exact hf hxy
  have he : k = id := StrictMono.eq_id hm
  funext x
  have hx := hk x
  rw [he] at hx
  exact hx.symm

/-- Equal one-point relational types include every repeated-entry
relation tuple. Nullary relations are automatically equal. -/
def ContactDiagonalEq (B : RelStructure L V) (x y : V) : Prop :=
  ∀ R : L.Symbol, B.rel R (fun _ => x) ↔ B.rel R (fun _ => y)

def contactDiagonalSetoid (B : RelStructure L V) : Setoid V where
  r := ContactDiagonalEq B
  iseqv := ⟨fun _ _ => Iff.rfl,fun h R => (h R).symm,
    fun h h' R => (h R).trans (h' R)⟩

/-- Agreement of the actual B-copies on all overlapping tuples.
Singleton overlaps use one-point types. Larger overlaps are a common
A-edge, and the two order-preserving A-enumerations coincide. -/
theorem contact_relational_overlap_agrees
    {A : RelStructure L U} {B : RelStructure L V}
    [LinearOrder U] [Finite U] [LinearOrder V] [LinearOrder W]
    {H : ContactHypergraphData W F J} {S : ContactTrainData F 1}
    (M : ContactDesignatedEmbeddings (contactRelationalTarget A.ordered B.ordered)
      (contactHeightOne (Embedding A.ordered B.ordered)) H S)
    (horder : ∀ j, StrictMono (M.emb j).vertex)
    (hdiag : ∀ i j x y, (M.emb i).vertex x = (M.emb j).vertex y →
      ContactDiagonalEq B.ordered x y)
    (hpair : H.bottomCut.ZeroPairwise) :
    ∀ (i j : J) (R : L.withOrder.Symbol)
      (x y : Fin (L.withOrder.arity R) → V),
      (∀ k, (M.emb i).vertex (x k) = (M.emb j).vertex (y k)) →
        (B.ordered.rel R x ↔ B.ordered.rel R y) := by
  classical
  intro i j R x y hxy
  by_cases hij : i = j
  · subst j
    have he : x = y := funext (fun k => (M.emb i).vertex.injective (hxy k))
    rw [he]
  by_cases hzero : L.withOrder.arity R = 0
  · have he : x = y := by
      funext k
      have hk := k.isLt
      omega
    rw [he]
  let k₀ : Fin (L.withOrder.arity R) := ⟨0,by omega⟩
  by_cases hconst : ∀ k, x k = x k₀
  · have hx : x = fun _ => x k₀ := funext hconst
    have hy : y = fun _ => y k₀ := by
      funext k
      apply (M.emb j).vertex.injective
      rw [← hxy k,← hxy k₀,hconst k]
    have h := hdiag i j (x k₀) (y k₀) (hxy k₀) R
    rwa [← hx,← hy] at h
  push_neg at hconst
  obtain ⟨k,hk⟩ := hconst
  have hmem (l : Fin (L.withOrder.arity R)) :
      (M.emb i).vertex (x l) ∈ H.copyCarrier i ∩ H.copyCarrier j := by
    rw [M.vertex_eq i,M.vertex_eq j]
    exact ⟨⟨x l,rfl⟩,⟨y l,(hxy l).symm⟩⟩
  rcases hpair (Sum.inl i) (Sum.inl j) (fun h => hij (Sum.inl.inj h)) with hs | ⟨e,hei,hej,he⟩
  · exact (hk ((M.emb i).vertex.injective (hs (hmem k) (hmem k₀)))).elim
  change e ∈ H.copyEdges i at hei
  change e ∈ H.copyEdges j at hej
  change H.copyCarrier i ∩ H.copyCarrier j = H.edgeCarrier e at he
  rw [M.edge_eq i] at hei
  rw [M.edge_eq j] at hej
  obtain ⟨a,ha⟩ := hei
  obtain ⟨b,hb⟩ := hej
  let f : U → W := (M.emb i).vertex ∘ a
  let g : U → W := (M.emb j).vertex ∘ b
  have hf : StrictMono f := (horder i).comp (Embedding.strictMono a)
  have hg : StrictMono g := (horder j).comp (Embedding.strictMono b)
  have hfr : Set.range f = H.edgeCarrier e := by
    rw [← ha,(M.emb i).carrier_eq]
    change Set.range f = (M.emb i).vertex '' Set.range a
    ext w
    constructor
    · rintro ⟨z,rfl⟩
      exact ⟨a z,⟨z,rfl⟩,rfl⟩
    · rintro ⟨_,⟨z,rfl⟩,rfl⟩
      exact ⟨z,rfl⟩
  have hgr : Set.range g = H.edgeCarrier e := by
    rw [← hb,(M.emb j).carrier_eq]
    change Set.range g = (M.emb j).vertex '' Set.range b
    ext w
    constructor
    · rintro ⟨z,rfl⟩
      exact ⟨b z,⟨z,rfl⟩,rfl⟩
    · rintro ⟨_,⟨z,rfl⟩,rfl⟩
      exact ⟨z,rfl⟩
  have hfg := contact_strictMono_eq_of_range_eq f g hf hg (hfr.trans hgr.symm)
  have hpre (l : Fin (L.withOrder.arity R)) : ∃ z : U, f z = (M.emb i).vertex (x l) := by
    have h := hmem l
    rw [he,← hfr] at h
    exact h
  choose z hz using hpre
  have hzx : a ∘ z = x := by
    funext l
    exact (M.emb i).vertex.injective (hz l)
  have hzy : b ∘ z = y := by
    funext l
    apply (M.emb j).vertex.injective
    change g (z l) = _
    rw [← hfg,hz l,hxy l]
  rw [← hzx,← hzy]
  exact (a.map_rel_iff R z).trans (b.map_rel_iff R z).symm

/-- Relational union generated by the actual embeddings of the
target. No additional tuples are added, including order tuples. -/
def contactRelationalUnion (B : RelStructure L V) (f : J → V ↪ W) :
    RelStructure L W where
  rel R x := ∃ j : J, ∃ y : Fin (L.arity R) → V, B.rel R y ∧ f j ∘ y = x

/-- The overlap compatibility proved above suffices for every
standard to be induced in the relational union. -/
def contactRelationalUnion_embedding (B : RelStructure L V) (f : J → V ↪ W)
    (h : ∀ (i j : J) (R : L.Symbol) (x y : Fin (L.arity R) → V),
      (∀ k, f i (x k) = f j (y k)) → (B.rel R x ↔ B.rel R y))
    (j : J) : Embedding B (contactRelationalUnion B f) where
  toFun := f j
  injective := (f j).injective
  map_rel_iff := by
    intro R x
    constructor
    · rintro ⟨i,y,hy,he⟩
      exact (h i j R y x (congrFun he)).mp hy
    · intro hx
      exact ⟨j,x,hx,rfl⟩

theorem contactRelationalUnion_extendsOrder
    (B : RelStructure L V) [LinearOrder V] [LinearOrder W]
    (f : J → V ↪ W) (horder : ∀ j, StrictMono (f j)) :
    (contactRelationalUnion B.ordered f).ExtendsOrder := by
  intro x y h
  obtain ⟨j,z,hz,he⟩ := h
  let i₀ : Fin (L.withOrder.arity (.inr ())) := ⟨0,by change 0 < 2; omega⟩
  let i₁ : Fin (L.withOrder.arity (.inr ())) := ⟨1,by change 1 < 2; omega⟩
  have hx : f j (z i₀) = x := congrFun he i₀
  have hy : f j (z i₁) = y := congrFun he i₁
  rw [← hx,← hy]
  exact horder j (show z i₀ < z i₁ from hz)

/-- Conformality rules out irreducible substructures spread across
several copies. The empty-set case just uses a nonempty family. -/
theorem contactRelationalUnion_irreducible_covered [Finite W] [Nonempty J]
    (B : RelStructure L V) (f : J → V ↪ W)
    (hcover : ∀ w, ∃ j, w ∈ Set.range (f j))
    (hconf : ContactConformal (fun j => Set.range (f j)))
    (S : Set W) (hS : ((contactRelationalUnion B f).induce S).Irreducible) :
    ∃ j, S ⊆ Set.range (f j) := by
  classical
  letI : Fintype W := Fintype.ofFinite _
  let t : Finset W := Finset.univ.filter (fun w => w ∈ S)
  have ht (w : W) : w ∈ t ↔ w ∈ S := by simp [t]
  by_cases hn : t.Nonempty
  · obtain ⟨j,hj⟩ := hconf t hn (fun w _ => hcover w) (by
      intro w hw z hz hne
      let x : S := ⟨w,(ht w).mp hw⟩
      let y : S := ⟨z,(ht z).mp hz⟩
      obtain ⟨R,p,i,k,hp,hi,hk⟩ := hS (show x ≠ y from fun h => hne (congrArg Subtype.val h))
      obtain ⟨j,q,_,hq⟩ := hp
      have hwi : f j (q i) = w := (congrFun hq i).trans (congrArg Subtype.val hi)
      have hzk : f j (q k) = z := (congrFun hq k).trans (congrArg Subtype.val hk)
      exact ⟨j,⟨q i,hwi⟩,⟨q k,hzk⟩⟩)
    exact ⟨j,fun w hw => hj ((ht w).mpr hw)⟩
  · refine ⟨Classical.choice inferInstance,?_⟩
    intro w hw
    exact (hn ⟨w,(ht w).mpr hw⟩).elim

/-- A copy of an irreducible source in a conformal relational union
factors through one actual designated relational embedding. -/
theorem contactRelationalUnion_factor
    {A : RelStructure L U} {B : RelStructure L V}
    [Finite W] [Nonempty J] (f : J → V ↪ W)
    (h : ∀ (i j : J) (R : L.Symbol) (x y : Fin (L.arity R) → V),
      (∀ k, f i (x k) = f j (y k)) → (B.rel R x ↔ B.rel R y))
    (hcover : ∀ w, ∃ j, w ∈ Set.range (f j))
    (hconf : ContactConformal (fun j => Set.range (f j)))
    (hA : A.Irreducible) (a : Embedding A (contactRelationalUnion B f)) :
    ∃ (j : J) (b : Embedding A B), (contactRelationalUnion_embedding B f h j).comp b = a := by
  obtain ⟨j,hj⟩ := contactRelationalUnion_irreducible_covered B f hcover hconf
    (Set.range a) (hA.range_embedding a)
  let e := contactRelationalUnion_embedding B f h j
  have hex (x : U) : ∃ y : V, a x = e y := by
    obtain ⟨y,hy⟩ := hj ⟨x,rfl⟩
    exact ⟨y,hy.symm⟩
  let b := a.factorThroughRange e hex
  refine ⟨j,b,?_⟩
  apply Embedding.ext
  intro x
  exact (Classical.choose_spec (hex x)).symm

end StructuralRamsey.Girth
