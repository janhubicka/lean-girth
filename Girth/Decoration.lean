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

end StructuralRamsey.Girth
