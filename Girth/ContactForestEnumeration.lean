import Girth.ContactForestInterfaces
import Girth.ContactRootedEnumeration

/-! # Exact admissible enumerations of forests of copies

Each new member meets the whole preceding union in its intersection with one
earlier member, and that separator is empty, a singleton, or an edge common to
the two pieces. In a linear ambient hypergraph these local attachments imply
all pairwise allowed intersections; no pairwise certificate is an input.
-/

namespace StructuralRamsey.Girth

universe v
variable {W I : Type v}

/-- An injective ranking whose attachments have exactly the permitted forest
separators, measured against the whole preceding union. -/
def ContactForestAdmissibleRank (F : I → HypergraphPiece W) (rank : I → ℕ) : Prop :=
  Function.Injective rank ∧ ∀ i, (∃ j, rank j < rank i) →
    ∃ p, rank p < rank i ∧
      (F i).carrier ∩ (⋃ j : {j // rank j < rank i}, (F j.val).carrier) =
        (F i).carrier ∩ (F p).carrier ∧
      AllowedIntersection (F i) (F p)

theorem ContactForestAdmissibleRank.toAdmissibleRank
    {F : I → HypergraphPiece W} {rank : I → ℕ}
    (h : ContactForestAdmissibleRank F rank) :
    ContactAdmissibleRank (fun i => (F i).carrier) rank := by
  refine ⟨h.1,?_⟩
  intro i hi
  obtain ⟨p,hp,he,_⟩ := h.2 i hi
  exact ⟨p,hp,he⟩

/-- The literal manuscript attachment condition yields an earlier parent
with the exact separator. Empty and singleton separators require no edge. -/
theorem contact_forestAdmissibleRank_of_attachments
    (F : I → HypergraphPiece W) (rank : I → ℕ)
    (hinj : Function.Injective rank)
    (hattach : ∀ i, (∃ j, rank j < rank i) →
      ((F i).carrier ∩
        (⋃ j : {j // rank j < rank i}, (F j.val).carrier)).Subsingleton ∨
      ∃ p, rank p < rank i ∧ ∃ e, e ∈ (F i).edges ∧ e ∈ (F p).edges ∧
        (F i).carrier ∩ (⋃ j : {j // rank j < rank i}, (F j.val).carrier) = e) :
    ContactForestAdmissibleRank F rank := by
  classical
  refine ⟨hinj,?_⟩
  intro i hi
  let S := (F i).carrier ∩ (⋃ j : {j // rank j < rank i}, (F j.val).carrier)
  have separator (p : I) (hp : rank p < rank i) (hsub : S ⊆ (F p).carrier) :
      S = (F i).carrier ∩ (F p).carrier := by
    apply Set.Subset.antisymm
    · exact fun _ hx => ⟨hx.1,hsub hx⟩
    · exact fun _ hx => ⟨hx.1,Set.mem_iUnion.mpr ⟨⟨p,hp⟩,hx.2⟩⟩
  rcases hattach i hi with hsmall | ⟨p,hp,e,hei,hep,he⟩
  · have aux (p : I) (hp : rank p < rank i) (hsub : S ⊆ (F p).carrier) :
        ∃ p, rank p < rank i ∧ S = (F i).carrier ∩ (F p).carrier ∧
          AllowedIntersection (F i) (F p) := by
      have he := separator p hp hsub
      exact ⟨p,hp,he,Or.inl (he ▸ hsmall)⟩
    by_cases hS : S.Nonempty
    · obtain ⟨x,hx⟩ := hS
      obtain ⟨p,hxp⟩ := Set.mem_iUnion.mp hx.2
      apply aux p.val p.property
      intro y hy
      exact (hsmall hx hy) ▸ hxp
    · obtain ⟨p,hp⟩ := hi
      exact aux p hp (fun _ hx => (hS ⟨_,hx⟩).elim)
  · have hsub : S ⊆ (F p).carrier := by
      rw [show S = e from he]
      exact (F p).edge_subset hep
    have hsep := separator p hp hsub
    exact ⟨p,hp,hsep,Or.inr ⟨e,hei,hep,hsep.symm.trans he⟩⟩

/-- The permitted preceding-union separators imply the global pairwise
intersection condition, by induction on the later of the two ranks. -/
theorem ContactForestAdmissibleRank.pairwiseAllowed
    {F : I → HypergraphPiece W} {rank : I → ℕ}
    (h : ContactForestAdmissibleRank F rank)
    (H : Set (Set W)) (hLinear : LinearEdgeSet H)
    (hEdges : ∀ i, (F i).edges ⊆ H) : PairwiseAllowed F := by
  have aux : ∀ n : ℕ, ∀ i, rank i = n → ∀ j, rank j < rank i →
      AllowedIntersection (F i) (F j) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro i hin j hji
      obtain ⟨p,hp,hsep,hallowed⟩ := h.2 i ⟨j,hji⟩
      by_cases hpj : p = j
      · simpa only [hpj] using hallowed
      have hprior : AllowedIntersection (F p) (F j) := by
        rcases lt_trichotomy (rank p) (rank j) with hlt | he | hgt
        · exact allowedIntersection_symm
            (ih (rank j) (by omega) j rfl p hlt)
        · exact (hpj (h.1 he)).elim
        · exact ih (rank p) (by omega) p rfl j hgt
      by_cases hsmall : ((F i).carrier ∩ (F j).carrier).Subsingleton
      · exact Or.inl hsmall
      have hmiddle : (F i).carrier ∩ (F j).carrier ⊆ (F p).carrier := by
        intro x hx
        have hx' : x ∈ (F i).carrier ∩
            (⋃ k : {k // rank k < rank i}, (F k.val).carrier) :=
          ⟨hx.1,Set.mem_iUnion.mpr ⟨⟨j,hji⟩,hx.2⟩⟩
        rw [hsep] at hx'
        exact hx'.2
      have hleft : (F i).carrier ∩ (F j).carrier ⊆
          (F i).carrier ∩ (F p).carrier := fun _ hx => ⟨hx.1,hmiddle hx⟩
      have hright : (F i).carrier ∩ (F j).carrier ⊆
          (F p).carrier ∩ (F j).carrier := fun _ hx => ⟨hmiddle hx,hx.2⟩
      rcases hallowed with hs | ⟨e,hei,hep,he⟩
      · exact (hsmall (fun x hx y hy => hs (hleft hx) (hleft hy))).elim
      rcases hprior with hs | ⟨f,hfp,hfj,hf⟩
      · exact (hsmall (fun x hx y hy => hs (hright hx) (hright hy))).elim
      have hsube : (F i).carrier ∩ (F j).carrier ⊆ e := he ▸ hleft
      have hsubf : (F i).carrier ∩ (F j).carrier ⊆ f := hf ▸ hright
      have hef : e = f := by
        by_contra hne
        have hs := hLinear (hEdges i hei) (hEdges p hfp) hne
        exact hsmall (fun x hx y hy => hs ⟨hsube hx,hsubf hx⟩ ⟨hsube hy,hsubf hy⟩)
      refine Or.inr ⟨e,hei,hef.symm ▸ hfj,Set.Subset.antisymm hsube ?_⟩
      intro x hx
      exact ⟨(F i).edge_subset hei hx,(F j).edge_subset hfj (hef ▸ hx)⟩
  intro i j hne
  rcases lt_trichotomy (rank i) (rank j) with hlt | he | hgt
  · exact allowedIntersection_symm (aux (rank j) j rfl i hlt)
  · exact (hne (h.1 he)).elim
  · exact aux (rank i) i rfl j hgt

/-- The manuscript's admissible-enumeration characterization of a finite
forest, including the empty family and singleton family. -/
theorem contact_forestOfCopies_iff_admissibleRank [Fintype I]
    (F : I → HypergraphPiece W) (H : Set (Set W))
    (hLinear : LinearEdgeSet H) (hEdges : ∀ i, (F i).edges ⊆ H) :
    ForestOfCopies F ↔ ∃ rank : I → ℕ, ContactForestAdmissibleRank F rank := by
  classical
  constructor
  · intro hF
    rcases hF.2 with hEmpty | hJ
    · exact ⟨fun _ => 0,⟨fun {i} => (hEmpty.false i).elim,
        fun i => (hEmpty.false i).elim⟩⟩
    · obtain ⟨J⟩ := hJ
      let T : ContactJoinTree (fun i => (F i).carrier) :=
        ⟨J.tree,J.isTree,J.running⟩
      let root : I := Classical.choice J.isTree.connected.nonempty
      refine ⟨T.parentFirstRank root,(T.parentFirstRank_admissible root).1,?_⟩
      intro i hi
      obtain ⟨p,hp,he⟩ := (T.parentFirstRank_admissible root).2 i hi
      exact ⟨p,hp,he,hF.1 (fun heq => by subst p; exact (Nat.lt_irrefl _ hp))⟩
  · rintro ⟨rank,hrank⟩
    refine ⟨hrank.pairwiseAllowed H hLinear hEdges,?_⟩
    cases isEmpty_or_nonempty I with
    | inl hEmpty => exact Or.inl hEmpty
    | inr hNonempty =>
      let := hNonempty
      obtain ⟨T⟩ := contact_joinTree_of_admissibleRank
        (fun i => (F i).carrier) rank hrank.toAdmissibleRank
      exact Or.inr ⟨⟨T.tree,T.isTree,T.running⟩⟩

/-- Exact forest characterization by the literal preceding-union
attachments: at most one vertex, or one common edge with an earlier member. -/
theorem contact_forestOfCopies_iff_admissibleAttachments [Fintype I]
    (F : I → HypergraphPiece W) (H : Set (Set W))
    (hLinear : LinearEdgeSet H) (hEdges : ∀ i, (F i).edges ⊆ H) :
    ForestOfCopies F ↔ ∃ rank : I → ℕ, Function.Injective rank ∧
      ∀ i, (∃ j, rank j < rank i) →
        ((F i).carrier ∩
          (⋃ j : {j // rank j < rank i}, (F j.val).carrier)).Subsingleton ∨
        ∃ p, rank p < rank i ∧ ∃ e, e ∈ (F i).edges ∧ e ∈ (F p).edges ∧
          (F i).carrier ∩ (⋃ j : {j // rank j < rank i}, (F j.val).carrier) = e := by
  rw [contact_forestOfCopies_iff_admissibleRank F H hLinear hEdges]
  constructor
  · rintro ⟨rank,hinj,hattach⟩
    refine ⟨rank,hinj,?_⟩
    intro i hi
    obtain ⟨p,hp,he,hallowed⟩ := hattach i hi
    rcases hallowed with hs | ⟨e,hei,hep,he'⟩
    · exact Or.inl (he.symm ▸ hs)
    · exact Or.inr ⟨p,hp,e,hei,hep,he.trans he'⟩
  · rintro ⟨rank,hinj,hattach⟩
    exact ⟨rank,contact_forestAdmissibleRank_of_attachments F rank hinj hattach⟩

end StructuralRamsey.Girth
