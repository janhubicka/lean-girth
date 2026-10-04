import Girth.HypergraphClique

/-! # Decorating a partite support hypergraph by A

This is the relational translation used in the structural local-forest
corollary.  Every support edge has exactly one vertex in each A-part, and
relations on an edge are copied from A through the part map.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {U W : Type v}

/-- Every support edge contains exactly one vertex in each part. -/
def EdgeTransversal
    (H : Set (Set W)) (part : W → U) : Prop :=
  ∀ e : Set W, e ∈ H → ∀ p : U,
    ∃! w : W, w ∈ e ∧ part w = p

namespace EdgeTransversal

variable {H : Set (Set W)} {part : W → U}

/-- The unique vertex of an edge in a prescribed part. -/
noncomputable def vertex
    (h : EdgeTransversal H part)
    {e : Set W} (he : e ∈ H) (p : U) : W :=
  Classical.choose (h e he p)

theorem vertex_mem
    (h : EdgeTransversal H part)
    {e : Set W} (he : e ∈ H) (p : U) :
    h.vertex he p ∈ e :=
  (Classical.choose_spec (h e he p)).1.1

theorem part_vertex
    (h : EdgeTransversal H part)
    {e : Set W} (he : e ∈ H) (p : U) :
    part (h.vertex he p) = p :=
  (Classical.choose_spec (h e he p)).1.2

theorem vertex_unique
    (h : EdgeTransversal H part)
    {e : Set W} (he : e ∈ H) {p : U}
    {w : W} (hw : w ∈ e) (hp : part w = p) :
    w = h.vertex he p := by
  exact (Classical.choose_spec (h e he p)).2 w ⟨hw, hp⟩

theorem vertex_injective
    (h : EdgeTransversal H part)
    {e : Set W} (he : e ∈ H) :
    Function.Injective (h.vertex he) := by
  intro p q hpq
  have := congrArg part hpq
  simpa [h.part_vertex he p, h.part_vertex he q] using this

theorem edge_eq_range_vertex
    (h : EdgeTransversal H part)
    {e : Set W} (he : e ∈ H) :
    e = Set.range (h.vertex he) := by
  apply Set.Subset.antisymm
  · intro w hw
    refine ⟨part w, ?_⟩
    exact (h.vertex_unique he hw rfl).symm
  · rintro w ⟨p, rfl⟩
    exact h.vertex_mem he p

end EdgeTransversal

/-- Decorate every support edge by a copy of A according to the part map.
A relation tuple is present exactly when it lies in one support edge and its
part tuple is a relation tuple of A. -/
def decorateSupport
    (A : RelStructure L U)
    (H : Set (Set W)) (part : W → U) :
    RelStructure L W where
  rel R x :=
    ∃ e : Set W, e ∈ H ∧
      (∀ i, x i ∈ e) ∧
      A.rel R (part ∘ x)

/-- Relation tuples in the decorated structure are edge-supported. -/
theorem decorateSupport_relationsCovered
    (A : RelStructure L U)
    (H : Set (Set W)) (part : W → U) :
    RelationsCoveredBy H (decorateSupport A H part) := by
  intro R x hx
  rcases hx with ⟨e, he, hxe, _⟩
  exact ⟨e, he, hxe⟩

/-- Every transversal support edge canonically carries an embedded copy of A. -/
noncomputable def decorateSupport_edgeEmbedding
    (A : RelStructure L U)
    {H : Set (Set W)} {part : W → U}
    (hTrans : EdgeTransversal H part)
    {e : Set W} (he : e ∈ H) :
    Embedding A (decorateSupport A H part) where
  toFun := hTrans.vertex he
  injective := hTrans.vertex_injective he
  map_rel_iff := by
    intro R x
    constructor
    · rintro ⟨f, hf, _hvals, hA⟩
      have hp :
          part ∘ (hTrans.vertex he ∘ x) = x := by
        funext i
        exact hTrans.part_vertex he (x i)
      rw [hp] at hA
      exact hA
    · intro hA
      refine ⟨e, he, ?_, ?_⟩
      · intro i
        exact hTrans.vertex_mem he (x i)
      · have hp :
            part ∘ (hTrans.vertex he ∘ x) = x := by
          funext i
          exact hTrans.part_vertex he (x i)
        simpa [Function.comp_assoc, hp] using hA

/-- The canonical A-copy on an edge has exactly that edge as its carrier. -/
theorem decorateSupport_edgeCarrier
    (A : RelStructure L U)
    {H : Set (Set W)} {part : W → U}
    (hTrans : EdgeTransversal H part)
    {e : Set W} (he : e ∈ H) :
    copyCarrier (decorateSupport_edgeEmbedding A hTrans he) = e := by
  change Set.range (hTrans.vertex he) = e
  exact (hTrans.edge_eq_range_vertex he).symm


/-- Strong embedding data for support hypergraphs: source edges map to target
edges, and every target edge meeting the image in at least two vertices comes
from a source edge. -/
structure StrongSupportEmbedding
    {X Y : Type v}
    (H : Set (Set X)) (K : Set (Set Y)) where
  toFun : X → Y
  injective : Function.Injective toFun
  map_edge :
    ∀ e : Set X, e ∈ H →
      ∃ E : Set Y, E ∈ K ∧ E = toFun '' e
  reflect_edge :
    ∀ E : Set Y, E ∈ K →
      ¬ (E ∩ Set.range toFun).Subsingleton →
      ∃ e : Set X, e ∈ H ∧ E = toFun '' e

instance {X Y : Type v} {H : Set (Set X)} {K : Set (Set Y)} :
    CoeFun (StrongSupportEmbedding H K) (fun _ => X → Y) :=
  ⟨StrongSupportEmbedding.toFun⟩

/-- A strongly induced, part-preserving support embedding lifts to an induced
embedding of the corresponding decorated relational structures. -/
def decorateSupportEmbedding
    {X Y : Type v}
    (A : RelStructure L U)
    {H : Set (Set X)} {K : Set (Set Y)}
    {partX : X → U} {partY : Y → U}
    (f : StrongSupportEmbedding H K)
    (hpart : ∀ x : X, partY (f x) = partX x)
    (hH : H.Nonempty)
    (hCover : ∀ x : X, ∃ e : Set X, e ∈ H ∧ x ∈ e) :
    Embedding
      (decorateSupport A H partX)
      (decorateSupport A K partY) where
  toFun := f
  injective := f.injective
  map_rel_iff := by
    classical
    intro R x
    constructor
    · rintro ⟨E, hE, hxE, hArel⟩
      have hArelX : A.rel R (partX ∘ x) := by
        convert hArel using 1
        funext i
        exact (hpart (x i)).symm
      have hSourceEdge :
          ∃ e : Set X, e ∈ H ∧ ∀ i, x i ∈ e := by
        by_cases hRange : (Set.range x).Subsingleton
        · by_cases hzero : L.arity R = 0
          · obtain ⟨e, he⟩ := hH
            refine ⟨e, he, ?_⟩
            intro i
            exact Fin.elim0 (Fin.cast hzero i)
          · have hpos : 0 < L.arity R := Nat.pos_of_ne_zero hzero
            let i0 : Fin (L.arity R) := ⟨0, hpos⟩
            obtain ⟨e, he, hxe⟩ := hCover (x i0)
            refine ⟨e, he, ?_⟩
            intro i
            have hEq : x i = x i0 :=
              hRange ⟨i, rfl⟩ ⟨i0, rfl⟩
            simpa [hEq] using hxe
        · have hMeet :
              ¬ (E ∩ Set.range f).Subsingleton := by
            rw [Set.not_subsingleton_iff] at hRange
            rcases hRange with ⟨u, hu, v, hv, huv⟩
            rcases hu with ⟨i, rfl⟩
            rcases hv with ⟨j, rfl⟩
            rw [Set.not_subsingleton_iff]
            refine ⟨f (x i), ?_, f (x j), ?_, ?_⟩
            · exact ⟨hxE i, ⟨x i, rfl⟩⟩
            · exact ⟨hxE j, ⟨x j, rfl⟩⟩
            · intro heq
              exact huv (f.injective heq)
          obtain ⟨e, he, hEeq⟩ := f.reflect_edge E hE hMeet
          refine ⟨e, he, ?_⟩
          intro i
          have hmem : f (x i) ∈ f '' e := by
            rw [← hEeq]
            exact hxE i
          rcases hmem with ⟨z, hz, hzi⟩
          have hzxi : z = x i := f.injective hzi
          simpa [hzxi] using hz
      rcases hSourceEdge with ⟨e, he, hxe⟩
      exact ⟨e, he, hxe, hArelX⟩
    · rintro ⟨e, he, hxe, hArel⟩
      obtain ⟨E, hE, hEeq⟩ := f.map_edge e he
      refine ⟨E, hE, ?_, ?_⟩
      · intro i
        rw [hEeq]
        exact ⟨x i, hxe i, rfl⟩
      · convert hArel using 1
        funext i
        exact hpart (x i)


/-- The decoration together with its part map is an A-partite system whenever
each support edge contains exactly one vertex in every part. -/
def decorateSupportSystem
    (A : RelStructure L U)
    (H : Set (Set W)) (part : W → U)
    (hTrans : EdgeTransversal H part) :
    StructuralRamsey.Partite.System L U W where
  toRelStructure := decorateSupport A H part
  part := part
  transversal := by
    intro R x hx i j hij
    rcases hx with ⟨e, he, hxe, _⟩
    have hi :
        x i = hTrans.vertex he (part (x i)) :=
      hTrans.vertex_unique he (hxe i) rfl
    have hj :
        x j = hTrans.vertex he (part (x i)) :=
      hTrans.vertex_unique he (hxe j) hij.symm
    exact hi.trans hj.symm

/-- A support edge is canonically a part-preserving copy of the transversal A
inside the decorated A-partite system. -/
noncomputable def decorateSupportSystem_edgeEmbedding
    (A : RelStructure L U)
    {H : Set (Set W)} {part : W → U}
    (hTrans : EdgeTransversal H part)
    {e : Set W} (he : e ∈ H) :
    StructuralRamsey.Partite.Embedding
      (StructuralRamsey.Partite.transversal A)
      (decorateSupportSystem A H part hTrans) where
  toEmbedding := decorateSupport_edgeEmbedding A hTrans he
  map_part x := by
    exact hTrans.part_vertex he x

/-- A strong support embedding that preserves parts lifts to a partite
embedding between decorated systems. -/
def decorateSupportSystemEmbedding
    {X Y : Type v}
    (A : RelStructure L U)
    {H : Set (Set X)} {K : Set (Set Y)}
    {partX : X → U} {partY : Y → U}
    (hTransH : EdgeTransversal H partX)
    (hTransK : EdgeTransversal K partY)
    (f : StrongSupportEmbedding H K)
    (hpart : ∀ x : X, partY (f x) = partX x)
    (hH : H.Nonempty)
    (hCover : ∀ x : X, ∃ e : Set X, e ∈ H ∧ x ∈ e) :
    StructuralRamsey.Partite.Embedding
      (decorateSupportSystem A H partX hTransH)
      (decorateSupportSystem A K partY hTransK) where
  toEmbedding := decorateSupportEmbedding A f hpart hH hCover
  map_part x := hpart x

/-- In an exact transversal decoration, part-preserving copies of transversal
A are canonically equivalent to support edges.  Unlike the purely relational
version below, no external order is needed: the part map rigidifies the copy. -/
noncomputable def decorateSupportSystem_embeddingEquivEdge
    (A : RelStructure L U)
    {H : Set (Set W)} {part : W → U}
    (hTrans : EdgeTransversal H part)
    (hSupport :
      supportCopies A (decorateSupport A H part) = H) :
    StructuralRamsey.Partite.Embedding
        (StructuralRamsey.Partite.transversal A)
        (decorateSupportSystem A H part hTrans) ≃
      {e : Set W // e ∈ H} where
  toFun a := ⟨copyCarrier a.toEmbedding, by
    rw [← hSupport]
    exact ⟨a.toEmbedding, rfl⟩⟩
  invFun e :=
    decorateSupportSystem_edgeEmbedding A hTrans e.2
  left_inv a := by
    apply StructuralRamsey.Partite.Embedding.ext
    intro x
    have hx :
        a x ∈ copyCarrier a.toEmbedding :=
      ⟨x, rfl⟩
    have hp : part (a x) = x := by
      simpa [StructuralRamsey.Partite.transversal] using a.map_part x
    exact
      (hTrans.vertex_unique
        (show copyCarrier a.toEmbedding ∈ H by
          rw [← hSupport]
          exact ⟨a.toEmbedding, rfl⟩)
        hx hp).symm
  right_inv e := by
    apply Subtype.ext
    change
      copyCarrier
          (decorateSupport_edgeEmbedding A hTrans e.2) =
        e.1
    exact decorateSupport_edgeCarrier A hTrans e.2



/-- The image of a source support edge under a strong support embedding,
packaged as a target support edge. -/
def StrongSupportEmbedding.mapEdge
    {X Y : Type v}
    {H : Set (Set X)} {K : Set (Set Y)}
    (f : StrongSupportEmbedding H K)
    (e : {e : Set X // e ∈ H}) :
    {E : Set Y // E ∈ K} := by
  refine ⟨f '' e.1, ?_⟩
  obtain ⟨E, hE, hEq⟩ := f.map_edge e.1 e.2
  rw [← hEq]
  exact hE

/-- A designated family of strong support embeddings is Ramsey when every
edge-colouring of the target is constant on all source edges inside one
designated member. -/
def StrongSupportRamseyFamily
    {X Y : Type v}
    (H : Set (Set X)) (K : Set (Set Y))
    (𝓗 : Set (StrongSupportEmbedding H K))
    (κ : Type*) : Prop :=
  ∀ χ : {E : Set Y // E ∈ K} → κ,
    ∃ f : StrongSupportEmbedding H K, f ∈ 𝓗 ∧
      ∀ e₁ e₂ : {e : Set X // e ∈ H},
        χ (f.mapEdge e₁) = χ (f.mapEdge e₂)

/-- Carrier of a composite through a lifted strong support embedding is the
set-theoretic image of the original carrier. -/
theorem copyCarrier_comp_decorateSupportSystemEmbedding
    {X Y : Type v}
    (A : RelStructure L U)
    {H : Set (Set X)} {K : Set (Set Y)}
    {partX : X → U} {partY : Y → U}
    (hTransH : EdgeTransversal H partX)
    (hTransK : EdgeTransversal K partY)
    (f : StrongSupportEmbedding H K)
    (hpart : ∀ x : X, partY (f x) = partX x)
    (hH : H.Nonempty)
    (hCover : ∀ x : X, ∃ e : Set X, e ∈ H ∧ x ∈ e)
    (a : StructuralRamsey.Partite.Embedding
      (StructuralRamsey.Partite.transversal A)
      (decorateSupportSystem A H partX hTransH)) :
    copyCarrier
        ((decorateSupportSystemEmbedding A hTransH hTransK
          f hpart hH hCover).comp a).toEmbedding =
      f '' copyCarrier a.toEmbedding := by
  apply Set.Subset.antisymm
  · intro y hy
    rcases hy with ⟨x, rfl⟩
    exact ⟨a x, ⟨x, rfl⟩, rfl⟩
  · intro y hy
    rcases hy with ⟨z, ⟨x, hx⟩, rfl⟩
    refine ⟨x, ?_⟩
    change f (a x) = f z
    exact congrArg f hx.symm

/-- A designated Ramsey family of strong, part-preserving support copies gives
exactly the partite Ramsey arrow needed by the induced Picture step. -/
theorem strongSupportRamseyFamily_partiteArrow
    {X Y : Type v}
    (A : RelStructure L U)
    {H : Set (Set X)} {K : Set (Set Y)}
    {partX : X → U} {partY : Y → U}
    (hTransH : EdgeTransversal H partX)
    (hTransK : EdgeTransversal K partY)
    (hSupportH : supportCopies A (decorateSupport A H partX) = H)
    (hSupportK : supportCopies A (decorateSupport A K partY) = K)
    (hH : H.Nonempty)
    (hCoverX : ∀ x : X, ∃ e : Set X, e ∈ H ∧ x ∈ e)
    (𝓗 : Set (StrongSupportEmbedding H K))
    (hParts :
      ∀ f : StrongSupportEmbedding H K, f ∈ 𝓗 →
        ∀ x : X, partY (f x) = partX x)
    {κ : Type*}
    (hRamsey : StrongSupportRamseyFamily H K 𝓗 κ) :
    StructuralRamsey.Partite.Arrow
      (StructuralRamsey.Partite.transversal A)
      (decorateSupportSystem A H partX hTransH)
      (decorateSupportSystem A K partY hTransK) κ := by
  intro χ
  let srcEq :=
    decorateSupportSystem_embeddingEquivEdge
      A hTransH hSupportH
  let dstEq :=
    decorateSupportSystem_embeddingEquivEdge
      A hTransK hSupportK
  let χEdge : {E : Set Y // E ∈ K} → κ :=
    fun E => χ (dstEq.symm E)
  obtain ⟨f, hf, hmono⟩ := hRamsey χEdge
  have hpart := hParts f hf
  let g :=
    decorateSupportSystemEmbedding
      A hTransH hTransK f hpart hH hCoverX
  refine ⟨g, ?_⟩
  intro a₁ a₂
  have hmap (a : StructuralRamsey.Partite.Embedding
      (StructuralRamsey.Partite.transversal A)
      (decorateSupportSystem A H partX hTransH)) :
      dstEq (g.comp a) = f.mapEdge (srcEq a) := by
    apply Subtype.ext
    change
      copyCarrier (g.comp a).toEmbedding =
        f '' copyCarrier a.toEmbedding
    exact copyCarrier_comp_decorateSupportSystemEmbedding
      A hTransH hTransK f hpart hH hCoverX a
  have hback (a : StructuralRamsey.Partite.Embedding
      (StructuralRamsey.Partite.transversal A)
      (decorateSupportSystem A H partX hTransH)) :
      g.comp a = dstEq.symm (f.mapEdge (srcEq a)) := by
    apply dstEq.injective
    rw [Equiv.apply_symm_apply]
    exact hmap a
  rw [hback a₁, hback a₂]
  exact hmono (srcEq a₁) (srcEq a₂)


/-- Complete structural translation used in the manuscript: in a transversal
high-girth support hypergraph, decorating edges by A introduces no unintended
A-copies or irreducible substructures. -/
theorem decorateSupport_exact
    (A : RelStructure L U)
    [Finite U]
    {H : Set (Set W)} {part : W → U}
    (hA : A.Irreducible)
    (hTrans : EdgeTransversal H part)
    (hgt : GirthGT H 3)
    (hH : H.Nonempty)
    (hVert : ∀ x : W, ∃ e : Set W, e ∈ H ∧ x ∈ e) :
    supportCopies A (decorateSupport A H part) = H ∧
      ∀ S : Set W,
        ((decorateSupport A H part).induce S).Irreducible →
          ∃ e : Set W, e ∈ H ∧ ∀ z : S, z.1 ∈ e := by
  apply decorated_highGirth_support_exact
    hA hgt
    (decorateSupport_relationsCovered A H part)
    hH hVert
  intro e he
  exact ⟨decorateSupport_edgeEmbedding A hTrans he,
    decorateSupport_edgeCarrier A hTrans he⟩



/-- For ordered A, every embedding into an exact transversal decoration is the
canonical embedding carried by its unique support edge. -/
theorem decorateSupport_ordered_copy_eq_edgeEmbedding
    (A₀ : RelStructure L U)
    [LinearOrder U] [Finite U]
    {H : Set (Set W)} {part : W → U}
    (hTrans : EdgeTransversal H part)
    (hSupport :
      supportCopies A₀.ordered (decorateSupport A₀.ordered H part) = H)
    (a : Embedding A₀.ordered (decorateSupport A₀.ordered H part)) :
    ∃ (e : Set W) (he : e ∈ H),
      a = decorateSupport_edgeEmbedding A₀.ordered hTrans he := by
  let e : Set W := copyCarrier a
  have he : e ∈ H := by
    rw [← hSupport]
    exact ⟨a, rfl⟩
  let b : Embedding A₀.ordered (decorateSupport A₀.ordered H part) :=
    decorateSupport_edgeEmbedding A₀.ordered hTrans he
  have hb : copyCarrier b = e := by
    exact decorateSupport_edgeCarrier A₀.ordered hTrans he
  have hs : SameCopy a b := by
    change copyCarrier a = copyCarrier b
    rw [hb]
    rfl
  exact ⟨e, he, ordered_embedding_eq_of_sameCopy a b hs⟩



/-- In an exact transversal decoration of an ordered structure, A-embeddings
are canonically equivalent to support edges. -/
noncomputable def decorateSupport_ordered_embeddingEquivEdge
    (A₀ : RelStructure L U)
    [LinearOrder U] [Finite U]
    {H : Set (Set W)} {part : W → U}
    (hTrans : EdgeTransversal H part)
    (hSupport :
      supportCopies A₀.ordered (decorateSupport A₀.ordered H part) = H) :
    RelStructure.Embedding A₀.ordered
        (decorateSupport A₀.ordered H part) ≃
      {e : Set W // e ∈ H} where
  toFun a := ⟨copyCarrier a, by
    rw [← hSupport]
    exact ⟨a, rfl⟩⟩
  invFun e :=
    decorateSupport_edgeEmbedding A₀.ordered hTrans e.2
  left_inv a := by
    apply ordered_embedding_eq_of_sameCopy
    change
      copyCarrier
          (decorateSupport_edgeEmbedding A₀.ordered hTrans
            (show copyCarrier a ∈ H by
              rw [← hSupport]
              exact ⟨a, rfl⟩)) =
        copyCarrier a
    rw [decorateSupport_edgeCarrier]
  right_inv e := by
    apply Subtype.ext
    change
      copyCarrier
          (decorateSupport_edgeEmbedding A₀.ordered hTrans e.2) =
        e.1
    exact decorateSupport_edgeCarrier A₀.ordered hTrans e.2


/-- A strong support embedding has A-strong image once the target decoration
has exactly the prescribed support hypergraph.  This is the strong-inducedness
bridge used in the structural local-forest corollary. -/
theorem decorateSupportEmbedding_range_aStrong
    {X Y : Type v}
    (A : RelStructure L U)
    {H : Set (Set X)} {K : Set (Set Y)}
    {partY : Y → U}
    (f : StrongSupportEmbedding H K)
    (hSupport : supportCopies A (decorateSupport A K partY) = K) :
    AStrong A (decorateSupport A K partY) (Set.range f) := by
  intro a hMeet
  have hEdge : copyCarrier a ∈ K := by
    rw [← hSupport]
    exact ⟨a, rfl⟩
  obtain ⟨e, he, hEq⟩ :=
    f.reflect_edge (copyCarrier a) hEdge hMeet
  intro y hy
  rw [hEq] at hy
  rcases hy with ⟨x, hx, rfl⟩
  exact ⟨x, rfl⟩

/-- Convenient high-girth specialization of
`decorateSupportEmbedding_range_aStrong`. -/
theorem decorateSupportEmbedding_range_aStrong_of_highGirth
    {X Y : Type v}
    (A : RelStructure L U)
    [Finite U]
    {H : Set (Set X)} {K : Set (Set Y)}
    {partY : Y → U}
    (f : StrongSupportEmbedding H K)
    (hA : A.Irreducible)
    (hTrans : EdgeTransversal K partY)
    (hgt : GirthGT K 3)
    (hK : K.Nonempty)
    (hVert : ∀ y : Y, ∃ e : Set Y, e ∈ K ∧ y ∈ e) :
    AStrong A (decorateSupport A K partY) (Set.range f) := by
  have hSupport :
      supportCopies A (decorateSupport A K partY) = K :=
    (decorateSupport_exact A hA hTrans hgt hK hVert).1
  exact decorateSupportEmbedding_range_aStrong A f hSupport

/-- Complete copy-lifting package for the structural local-forest lemma:
a strongly induced, part-preserving support copy lifts to an induced relational
copy whose image is A-strong in the high-girth target decoration. -/
theorem decorateStrongSupportCopy_of_highGirth
    {X Y : Type v}
    (A : RelStructure L U)
    [Finite U]
    {H : Set (Set X)} {K : Set (Set Y)}
    {partX : X → U} {partY : Y → U}
    (f : StrongSupportEmbedding H K)
    (hpart : ∀ x : X, partY (f x) = partX x)
    (hH : H.Nonempty)
    (hCoverX : ∀ x : X, ∃ e : Set X, e ∈ H ∧ x ∈ e)
    (hA : A.Irreducible)
    (hTransK : EdgeTransversal K partY)
    (hgtK : GirthGT K 3)
    (hK : K.Nonempty)
    (hCoverY : ∀ y : Y, ∃ e : Set Y, e ∈ K ∧ y ∈ e) :
    let e : RelStructure.Embedding
        (decorateSupport A H partX)
        (decorateSupport A K partY) :=
      decorateSupportEmbedding A f hpart hH hCoverX
    AStrong A (decorateSupport A K partY) (copyCarrier e) := by
  let e : RelStructure.Embedding
      (decorateSupport A H partX)
      (decorateSupport A K partY) :=
    decorateSupportEmbedding A f hpart hH hCoverX
  have hs :=
    decorateSupportEmbedding_range_aStrong_of_highGirth
      A f hA hTransK hgtK hK hCoverY
  change
    AStrong A (decorateSupport A K partY)
      (Set.range (fun x => e x))
  exact hs


/-- Structural form of a high-girth support Ramsey witness.

This packages the whole support-to-structure translation used in the proof of
the structural local-forest partite lemma.  What remains external here is only
the genuinely hypergraph-theoretic production of the strong Ramsey family and
its forest property. -/
theorem structuralPartiteWitness_of_strongSupportRamsey
    {X Y : Type v}
    (A : RelStructure L U)
    [Finite U]
    {H : Set (Set X)} {K : Set (Set Y)}
    {partX : X → U} {partY : Y → U}
    (hA : A.Irreducible)
    (hTransH : EdgeTransversal H partX)
    (hTransK : EdgeTransversal K partY)
    (hgtH : GirthGT H 3)
    (hgtK : GirthGT K 3)
    (hH : H.Nonempty)
    (hK : K.Nonempty)
    (hCoverX : ∀ x : X, ∃ e : Set X, e ∈ H ∧ x ∈ e)
    (hCoverY : ∀ y : Y, ∃ e : Set Y, e ∈ K ∧ y ∈ e)
    (𝓗 : Set (StrongSupportEmbedding H K))
    (hParts :
      ∀ f : StrongSupportEmbedding H K, f ∈ 𝓗 →
        ∀ x : X, partY (f x) = partX x)
    {κ : Type*}
    (hRamsey : StrongSupportRamseyFamily H K 𝓗 κ) :
    let P := decorateSupportSystem A H partX hTransH
    let R := decorateSupportSystem A K partY hTransK
    supportCopies A P.toRelStructure = H ∧
      supportCopies A R.toRelStructure = K ∧
      StructuralRamsey.Partite.Arrow
        (StructuralRamsey.Partite.transversal A) P R κ ∧
      (∀ S : Set Y,
        (R.toRelStructure.induce S).Irreducible →
          ∃ e : Set Y, e ∈ K ∧ ∀ z : S, z.1 ∈ e) ∧
      ∀ (f : StrongSupportEmbedding H K) (hf : f ∈ 𝓗),
        let g : RelStructure.Embedding P.toRelStructure R.toRelStructure :=
          decorateSupportEmbedding A f (hParts f hf) hH hCoverX
        AStrong A R.toRelStructure (copyCarrier g) := by
  let P := decorateSupportSystem A H partX hTransH
  let R := decorateSupportSystem A K partY hTransK
  have hExactH :=
    decorateSupport_exact A hA hTransH hgtH hH hCoverX
  have hExactK :=
    decorateSupport_exact A hA hTransK hgtK hK hCoverY
  have hArrow :
      StructuralRamsey.Partite.Arrow
        (StructuralRamsey.Partite.transversal A) P R κ := by
    exact strongSupportRamseyFamily_partiteArrow
      A hTransH hTransK hExactH.1 hExactK.1
      hH hCoverX 𝓗 hParts hRamsey
  refine ⟨hExactH.1, hExactK.1, hArrow, hExactK.2, ?_⟩
  intro f hf
  exact decorateStrongSupportCopy_of_highGirth
    A f (hParts f hf) hH hCoverX hA hTransK hgtK hK hCoverY


end StructuralRamsey.Girth
