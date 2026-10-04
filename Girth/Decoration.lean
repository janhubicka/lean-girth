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

end StructuralRamsey.Girth
