import Girth.ContactGraph

/-!
# Invariance under edge substitution

This is Lemma thm:derivation of the new manuscript.  The same vertex,
wagon and copy labels are used before and after filling, and the edge
type may change.  Coverage and the unique cover map are the concrete
data required of the canonical filling.  Unlike the old proof this
argument never constructs or transports an acceptable cycle word.

Construction of the ordered filling and of its selected subcopies is
separate.  This theorem proves all four clauses of the new invariant
for the actual carrier and incidence data, not just graph isomorphism.
-/

namespace StructuralRamsey.Girth

universe v
variable {V E F I P : Type v}
variable {old : OrderOneData V E I P} {new : OrderOneData V F I P}

/-- The hypotheses of edge substitution, with inherited labels already
identified via the corresponding quotient equivalences. -/
structure ContactSubstitution (old : OrderOneData V E I P)
    (new : OrderOneData V F I P) where
  cover : F → E
  contained : ∀ f, new.edgeCarrier f ⊆ old.edgeCarrier (cover f)
  covering : ∀ e x, x ∈ old.edgeCarrier e →
    ∃ f, cover f = e ∧ x ∈ new.edgeCarrier f
  old_nonempty : ∀ e, (old.edgeCarrier e).Nonempty
  parent_eq : ∀ f, new.parent f = old.parent (cover f)
  copyCarrier_eq : ∀ i, new.copyCarrier i = old.copyCarrier i
  copyEdges_iff : ∀ i f, f ∈ new.copyEdges i ↔ cover f ∈ old.copyEdges i
  newEdgeLinear : ∀ e f : F, e ≠ f →
    (new.edgeCarrier e ∩ new.edgeCarrier f).Subsingleton

namespace ContactSubstitution

variable (S : ContactSubstitution old new)
include S

theorem cover_surjective : Function.Surjective S.cover := by
  intro e
  obtain ⟨x, hx⟩ := S.old_nonempty e
  obtain ⟨f, hf, _⟩ := S.covering e x hx
  exact ⟨f, hf⟩

theorem wagonCarrier_eq :
    new.contactWagonCarrier = old.contactWagonCarrier := by
  funext p
  ext x
  change (∃ f, new.parent f = p ∧ x ∈ new.edgeCarrier f) ↔
    (∃ e, old.parent e = p ∧ x ∈ old.edgeCarrier e)
  constructor
  · rintro ⟨f, hf, hx⟩
    exact ⟨S.cover f, (S.parent_eq f).symm.trans hf, S.contained f hx⟩
  · rintro ⟨e, he, hx⟩
    obtain ⟨f, hf, hxf⟩ := S.covering e x hx
    exact ⟨f, (S.parent_eq f).trans (by rw [hf]; exact he), hxf⟩

theorem meets_iff (i : I) (p : P) :
    new.contactMeets i p ↔ old.contactMeets i p := by
  constructor
  · rintro ⟨f, hf, hp⟩
    exact ⟨S.cover f, (S.copyEdges_iff i f).mp hf,
      (S.parent_eq f).symm.trans hp⟩
  · rintro ⟨e, he, hp⟩
    obtain ⟨f, hf⟩ := S.cover_surjective e
    refine ⟨f, (S.copyEdges_iff i f).mpr ?_, ?_⟩
    · simpa only [hf] using he
    · exact (S.parent_eq f).trans (by simpa only [hf] using hp)

theorem wagonClique_eq :
    new.contactWagonClique = old.contactWagonClique := by
  funext p
  ext z
  cases z with
  | inl x =>
    change x ∈ new.contactWagonCarrier p ↔ x ∈ old.contactWagonCarrier p
    rw [S.wagonCarrier_eq]
  | inr q => rfl

theorem copyClique_eq :
    new.contactCopyClique = old.contactCopyClique := by
  funext i
  ext z
  cases z with
  | inl x =>
    change x ∈ new.copyCarrier i ↔ x ∈ old.copyCarrier i
    rw [S.copyCarrier_eq i]
  | inr p => exact S.meets_iff i p

theorem clique_eq : new.contactClique = old.contactClique := by
  funext a
  cases a with
  | inl i => exact congrFun S.copyClique_eq i
  | inr p => exact congrFun S.wagonClique_eq p

/-- The inherited generating cliques and their two-section are equal,
including all wagon vertices and all copy labels. -/
theorem adjacent_iff (x y : V ⊕ P) :
    contactAdjacent new.contactClique x y ↔
      contactAdjacent old.contactClique x y := by
  rw [S.clique_eq]

/-- Strong inducedness and incidence survive pointwise coverage. -/
theorem preserves_g1 (h : old.ContactG1) : new.ContactG1 := by
  refine ⟨?_, ?_, ?_⟩
  · intro i f hf x hx
    rw [S.copyCarrier_eq i]
    exact h.edge_subset i (S.cover f) ((S.copyEdges_iff i f).mp hf)
      (S.contained f hx)
  · intro i f hf
    obtain ⟨x, hx, y, hy, hxy⟩ := hf
    apply (S.copyEdges_iff i f).mpr
    apply h.strong i (S.cover f)
    exact ⟨x, ⟨S.contained f hx.1, by simpa only [S.copyCarrier_eq i] using hx.2⟩,
      y, ⟨S.contained f hy.1, by simpa only [S.copyCarrier_eq i] using hy.2⟩, hxy⟩
  · intro i p hTrigger x hxF hxW
    rw [S.copyCarrier_eq i] at hxF
    rw [S.wagonCarrier_eq] at hxW
    have hOldTrigger :
        old.contactMeets i p ∨
          (old.copyCarrier i ∩ old.contactWagonCarrier p).Nontrivial := by
      rcases hTrigger with hm | hn
      · exact Or.inl ((S.meets_iff i p).mp hm)
      · right
        simpa only [S.copyCarrier_eq i, S.wagonCarrier_eq] using hn
    obtain ⟨e, he, hp, hxe⟩ := h.bridge i p hOldTrigger x hxF hxW
    obtain ⟨f, hf, hxf⟩ := S.covering e x hxe
    refine ⟨f, (S.copyEdges_iff i f).mpr ?_, ?_, hxf⟩
    · simpa only [hf] using he
    · exact (S.parent_eq f).trans (by simpa only [hf] using hp)

/-- Full G1--G4 substitution lemma, with no old cycle-word assumptions. -/
theorem preserves_systemGirth {q : ℕ} (h : old.ContactSystemGirthGT q) :
    new.ContactSystemGirthGT q := by
  refine ⟨⟨S.newEdgeLinear, ?_⟩, S.preserves_g1 h.g1, ?_, ?_, ?_⟩
  · rw [S.wagonCarrier_eq]
    exact h.linear.2
  · unfold OrderOneData.ContactG2
    rw [S.copyClique_eq, S.wagonClique_eq]
    exact h.g2
  · rw [S.wagonCarrier_eq]
    exact h.g3
  · rw [S.clique_eq]
    exact h.g4

end ContactSubstitution
end StructuralRamsey.Girth
