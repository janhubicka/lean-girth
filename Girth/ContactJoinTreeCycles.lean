import Girth.ContactJoinTree
import Girth.ContactLevelZero

/-! Join-tree families of cliques have no bad polygons.  We use leaf
deletion directly, so this argument needs neither a chordal graph
characterization nor a separate Helly theorem. The clique indexed by
a piece may consist of all contact points whose support is contained
in the piece's vertex carrier. This includes bottom-cut wagon labels. -/

namespace StructuralRamsey.Girth

universe v
variable {W V P I : Type v}

namespace ContactJoinTree

/-- Every point common to a leaf clique and any other clique is
in the parent clique, for any family defined by containment of
fixed supports in the original vertex carriers. -/
theorem support_parent {F : I → Set W} (J : ContactJoinTree F)
    (support : V ⊕ P → Set W)
    {leaf parent other : I} (hadj : J.tree.Adj leaf parent)
    (huniq : ∀ j, J.tree.Adj leaf j → j = parent)
    (hne : other ≠ leaf) (z : V ⊕ P)
    (hl : support z ⊆ F leaf) (ho : support z ⊆ F other) :
    support z ⊆ F parent := by
  intro x hx
  exact J.mem_parent_of_mem_leaf_and_other hadj huniq hne (hl hx) (ho hx)

/-- A bad polygon survives deleting a leaf. Indeed, each polygon
vertex is contained in a nonleaf clique: otherwise its two incident
sides are both in the leaf. If a side is in the leaf, both endpoints
are therefore in the parent. -/
theorem bad_after_eraseLeaf {F : I → Set W} (J : ContactJoinTree F)
    (support : V ⊕ P → Set W)
    {leaf parent : I} (hadj : J.tree.Adj leaf parent)
    (huniq : ∀ j, J.tree.Adj leaf j → j = parent)
    (B : ContactPolygon V P)
    (hb : B.Bad (fun i => {z | support z ⊆ F i})) :
    B.Bad (fun (i : {i : I // i ∈ ({leaf} : Set I)ᶜ}) =>
      {z | support z ⊆ F i.1}) := by
  classical
  have hother : ∀ k : Fin B.length, ∃ j : I, j ≠ leaf ∧ support (B.vertex k) ⊆ F j := by
    intro k
    by_contra hn
    obtain ⟨_,a,ha,hak⟩ := hb.1 k
    have ha' : a = leaf := by
      by_contra he
      exact hn ⟨a,he,ha⟩
    obtain ⟨t,ht⟩ := (contactSucc_surjective (n := B.length)) k
    obtain ⟨_,b,hb₁,hb₂⟩ := hb.1 t
    have hb' : b = leaf := by
      by_contra he
      apply hn
      refine ⟨b,he,?_⟩
      rw [← ht]
      exact hb₂
    apply B.bad_no_three_successive hb leaf t
    · simpa only [hb'] using hb₁
    · simpa only [hb'] using hb₂
    · rw [ht]
      simpa only [ha'] using hak
  refine ⟨?_,?_,?_⟩
  · intro k
    obtain ⟨hne,a,h1,h2⟩ := hb.1 k
    by_cases he : a = leaf
    · subst a
      obtain ⟨j,hj,hj₁⟩ := hother k
      obtain ⟨l,hl,hl₁⟩ := hother (cyclicSucc k)
      exact ⟨hne,⟨parent,by simpa using hadj.ne.symm⟩,
        J.support_parent support hadj huniq hj _ h1 hj₁,
        J.support_parent support hadj huniq hl _ h2 hl₁⟩
    · exact ⟨hne,⟨a,by simpa using he⟩,h1,h2⟩
  · rintro ⟨a,ha⟩
    exact hb.2.1 ⟨a.val,ha⟩
  · rintro ⟨i,j,hnc,hne,a,ha,ha'⟩
    exact hb.2.2 ⟨i,j,hnc,hne,a.val,ha,ha'⟩

/-- All simple polygons in the clique family defined by a finite
join tree satisfy G4, with no restriction on their weights. -/
theorem g4_of_support {F : I → Set W} [Fintype I]
    (J : ContactJoinTree F) (support : V ⊕ P → Set W) (q : ℕ) :
    ContactG4 (fun i => {z | support z ⊆ F i}) q := by
  classical
  apply contactG4_of_no_bad
  intro B _
  have aux : ∀ n : ℕ, ∀ (L : Type v) [Fintype L], Fintype.card L = n →
      ∀ (K : L → Set W), ContactJoinTree K →
        ¬ B.Bad (fun i => {z | support z ⊆ K i}) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro L inst hn K T hb
      by_cases hsub : Subsingleton L
      · letI : Subsingleton L := hsub
        let k₀ : Fin B.length := ⟨0,by have := B.hlength; omega⟩
        obtain ⟨_,a,_,_⟩ := hb.1 k₀
        apply hb.2.1
        refine ⟨a,?_⟩
        intro k
        obtain ⟨_,b,hb',_⟩ := hb.1 k
        simpa only [Subsingleton.elim b a] using hb'
      · letI : Nontrivial L := not_subsingleton_iff_nontrivial.mp hsub
        obtain ⟨leaf,parent,hadj,huniq,_⟩ := T.exists_leaf_attachment
        let L' := {i : L // i ∈ ({leaf} : Set L)ᶜ}
        letI : Fintype L' := Fintype.ofFinite L'
        have hlt : Fintype.card L' < n := by
          rw [← hn]
          apply Fintype.card_lt_of_injective_not_surjective (fun i : L' => i.val)
            Subtype.val_injective
          intro hsur
          obtain ⟨x,hx⟩ := hsur leaf
          have hne : x.val ≠ leaf := by simpa using x.property
          exact hne hx
        exact ih (Fintype.card L') hlt L' rfl
          (contactEraseSet K leaf) (T.eraseLeaf hadj huniq)
          (T.bad_after_eraseLeaf support hadj huniq B hb)
  exact aux (Fintype.card I) I rfl F J

end ContactJoinTree

namespace OrderOneData

variable {E : Type v} (D : OrderOneData V E I E)

/-- The support of a bottom contact point is its singleton vertex
or its entire ambient edge. -/
def zeroContactSupport : V ⊕ E → Set V
  | .inl x => {x}
  | .inr e => D.edgeCarrier e

/-- Bottom constituent cliques are exactly the support containment
cliques of the corresponding real-vertex pieces. For a wagon,
this uses the nontriviality of the ambient edge and strongness. -/
theorem zero_clique_support_iff (h0 : ∀ e, D.parent e = e)
    (h1 : D.ContactG1) (hlin : D.ContactLinear)
    (hsize : ∀ e, (D.edgeCarrier e).Nontrivial)
    (a : I ⊕ E) (z : V ⊕ E) :
    z ∈ D.contactClique a ↔ D.zeroContactSupport z ⊆ D.carrier a := by
  cases z with
  | inl x =>
    rw [D.zero_piece_contact h0 a x]
    change x ∈ D.carrier a ↔ ({x} : Set V) ⊆ D.carrier a
    exact ⟨fun hx y hy => by have he : y = x := hy; subst y; exact hx,
      fun h => h rfl⟩
  | inr e =>
    cases a with
    | inl i =>
      change D.contactMeets i e ↔ D.edgeCarrier e ⊆ D.copyCarrier i
      constructor
      · rintro ⟨f,hf,hp⟩
        have he : f = e := (h0 f).symm.trans hp
        subst f
        exact h1.edge_subset i e hf
      · intro h
        obtain ⟨x,hx,y,hy,hxy⟩ := hsize e
        exact ⟨e,h1.strong i e ⟨x,⟨hx,h hx⟩,y,⟨hy,h hy⟩,hxy⟩,h0 e⟩
    | inr f =>
      change e = f ↔ D.edgeCarrier e ⊆ D.edgeCarrier f
      constructor
      · rintro rfl
        exact Set.Subset.rfl
      · intro h
        by_contra hn
        obtain ⟨x,hx,y,hy,hxy⟩ := hsize e
        exact hxy (hlin.1 e f hn ⟨hx,h hx⟩ ⟨hy,h hy⟩)

/-- A selected bottom family with a join tree of its real carriers
has G4 on its enlarged contact cliques. -/
theorem zero_selected_g4 {J : Type v} [Fintype J] (sel : J → I ⊕ E)
    (h0 : ∀ e, D.parent e = e) (h1 : D.ContactG1) (hlin : D.ContactLinear)
    (hsize : ∀ e, (D.edgeCarrier e).Nontrivial)
    (T : ContactJoinTree (fun j => D.carrier (sel j))) (q : ℕ) :
    ContactG4 (fun j => D.contactClique (sel j)) q := by
  have he : (fun j => D.contactClique (sel j)) =
      fun j => {z | D.zeroContactSupport z ⊆ D.carrier (sel j)} := by
    funext j
    ext z
    exact D.zero_clique_support_iff h0 h1 hlin hsize (sel j) z
  rw [he]
  exact T.g4_of_support D.zeroContactSupport q

end OrderOneData
end StructuralRamsey.Girth
