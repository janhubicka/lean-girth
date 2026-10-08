import Girth.ForestCoherentCycleCore
import Girth.ForestMarkedCarrierHistory
import Mathlib.Tactic

/-!
# Coherent owner-labelled witnesses for bounded girth

A coherent first-bad-cycle core retains finitely many actual old support edges.
In the circulation proof we also need to retain a designated old B-copy
owning each of those edges. This module chooses such an owner at the
FIRST stage at which the edge has a designated owner, and reuses that owner
at every later stage. Under support-edge coverage and monotonicity, the
resulting B-copy family is monotone, contained in the real old designated
family, and has no more members than the edge core.

Moreover, if every designated B-piece contributes only old ambient support
edges, replacing the old support by the UNION OF THE RETAINED FULL B-PIECES'
SUPPORTS preserves all girth tests for subsets of a fixed candidate batch.
This preserves actual edge ownership, rather than retaining abstract
support-edge witnesses without any designated B-parent.

Nothing here preserves running intersections of the retained B-family:
subfamilies of a forest need not be forests. Nor does it recode arbitrarily
long predecessor-parameter chains as legal free-successor histories.
-/

namespace StructuralRamsey.Girth

universe v

/-- A support edge has a designated physical B-piece at some stage. -/
def EverDesignatedOwner {W : Type v}
    (P : ℕ → Set (HypergraphPiece W)) (e : Set W) : Prop :=
  ∃ s : ℕ, ∃ D : HypergraphPiece W, D ∈ P s ∧ e ∈ D.edges

/-- Choose one physical designated B-piece at the first stage at which it
owns this support edge. The fallback empty piece is never used for a
support edge with an old owner. -/
noncomputable def firstDesignatedEdgeOwner {W : Type v}
    (P : ℕ → Set (HypergraphPiece W)) (e : Set W) :
    HypergraphPiece W := by
  classical
  exact if h : EverDesignatedOwner P e then
    Classical.choose (Nat.find_spec h)
  else
    { carrier := ∅
      edges := ∅
      edge_subset_carrier := by simp }

/-- The chosen physical B-owner already belongs to the old family at a
stage no later than any stage at which the edge has an owner. -/
theorem firstDesignatedEdgeOwner_spec {W : Type v}
    (P : ℕ → Set (HypergraphPiece W)) (e : Set W) (n : ℕ)
    (hOwned : ∃ D : HypergraphPiece W, D ∈ P n ∧ e ∈ D.edges) :
    ∃ s ≤ n, firstDesignatedEdgeOwner P e ∈ P s ∧
      e ∈ (firstDesignatedEdgeOwner P e).edges := by
  classical
  have hEver : EverDesignatedOwner P e := ⟨n, hOwned⟩
  have hFirst : Nat.find hEver ≤ n := Nat.find_le hOwned
  refine ⟨Nat.find hEver, hFirst, ?_⟩
  simp only [firstDesignatedEdgeOwner, dif_pos hEver]
  exact Classical.choose_spec (Nat.find_spec hEver)

/-- The labelled old B-owners of the edges in one coherent finite
first-bad-cycle core. The selection depends only on an old edge's
earliest designated owner, not on the current history stage. -/
noncomputable def coherentCycleOwnerCore {W : Type v}
    (H : ℕ → Set (Set W))
    (P : ℕ → Set (HypergraphPiece W))
    (K : Finset (Set W)) (g N n : ℕ) :
    Finset (HypergraphPiece W) := by
  classical
  exact (coherentBatchCycleCore H K g N n).image
    (firstDesignatedEdgeOwner P)

/-- Every selected owner really belongs to the old designated family
at the stage where it is retained. -/
theorem coherentCycleOwnerCore_subset {W : Type v}
    (H : ℕ → Set (Set W))
    (P : ℕ → Set (HypergraphPiece W))
    (K : Finset (Set W)) (g N n : ℕ)
    (hHMono : Monotone H) (hPMono : Monotone P)
    (hCover : ∀ t e, e ∈ H t →
      ∃ D : HypergraphPiece W, D ∈ P t ∧ e ∈ D.edges) :
    ∀ D ∈ coherentCycleOwnerCore H P K g N n, D ∈ P n := by
  classical
  intro D hD
  obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hD
  have heOld : e ∈ H n :=
    coherentBatchCycleCore_subset H K g N n hHMono he
  obtain ⟨s, hsn, hsMember, _⟩ :=
    firstDesignatedEdgeOwner_spec P e n (hCover n e heOld)
  exact hPMono hsn hsMember

/-- Every selected old support edge keeps an actual designated B-owner,
and the owner is one of the finitely retained B-pieces. -/
theorem coherentCycleOwnerCore_covers {W : Type v}
    (H : ℕ → Set (Set W))
    (P : ℕ → Set (HypergraphPiece W))
    (K : Finset (Set W)) (g N n : ℕ)
    (hHMono : Monotone H)
    (hCover : ∀ t e, e ∈ H t →
      ∃ D : HypergraphPiece W, D ∈ P t ∧ e ∈ D.edges)
    (e : Set W) (he : e ∈ coherentBatchCycleCore H K g N n) :
    ∃ D ∈ coherentCycleOwnerCore H P K g N n, e ∈ D.edges := by
  classical
  have heOld : e ∈ H n :=
    coherentBatchCycleCore_subset H K g N n hHMono he
  obtain ⟨s, hsn, hsMember, hsEdge⟩ :=
    firstDesignatedEdgeOwner_spec P e n (hCover n e heOld)
  refine ⟨firstDesignatedEdgeOwner P e, ?_, hsEdge⟩
  exact Finset.mem_image.mpr ⟨e, he, rfl⟩

/-- The choice of each owner is unchanged when the history grows.
Thus the family of retained actual B-owners is monotone in time. -/
theorem coherentCycleOwnerCore_mono {W : Type v}
    (H : ℕ → Set (Set W))
    (P : ℕ → Set (HypergraphPiece W))
    (K : Finset (Set W)) (g N n n' : ℕ) (hn : n ≤ n') :
    coherentCycleOwnerCore H P K g N n ⊆
      coherentCycleOwnerCore H P K g N n' := by
  classical
  intro D hD
  obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hD
  apply Finset.mem_image.mpr
  exact ⟨e, coherentBatchCycleCore_mono H K g N n n' hn he, rfl⟩

/-- The owner count is bounded by the old support witness count;
in particular it is independent of the number of history levels. -/
theorem coherentCycleOwnerCore_card_le {W : Type v}
    (H : ℕ → Set (Set W))
    (P : ℕ → Set (HypergraphPiece W))
    (K : Finset (Set W)) (g N n : ℕ) :
    (coherentCycleOwnerCore H P K g N n).card ≤
      g * 2 ^ K.card := by
  classical
  calc
    (coherentCycleOwnerCore H P K g N n).card ≤
      (coherentBatchCycleCore H K g N n).card := by
        unfold coherentCycleOwnerCore
        exact Finset.card_image_le
    _ ≤ g * 2 ^ K.card :=
      coherentBatchCycleCore_card_le H K g N n

/-- Actual supports of all retained *whole* B-pieces. This can contain
more edges than the selected short-cycle core. -/
def coherentCycleOwnerSupport {W : Type v}
    (H : ℕ → Set (Set W))
    (P : ℕ → Set (HypergraphPiece W))
    (K : Finset (Set W)) (g N n : ℕ) : Set (Set W) :=
  {e | ∃ D ∈ coherentCycleOwnerCore H P K g N n, e ∈ D.edges}

/-- All selected support-edge witnesses are still present when entire
designated owner pieces, rather than isolated old edges, are retained. -/
theorem coherentBatchCycleCore_subset_ownerSupport {W : Type v}
    (H : ℕ → Set (Set W))
    (P : ℕ → Set (HypergraphPiece W))
    (K : Finset (Set W)) (g N n : ℕ)
    (hHMono : Monotone H)
    (hCover : ∀ t e, e ∈ H t →
      ∃ D : HypergraphPiece W, D ∈ P t ∧ e ∈ D.edges) :
    (↑(coherentBatchCycleCore H K g N n) : Set (Set W)) ⊆
      coherentCycleOwnerSupport H P K g N n := by
  intro e he
  exact coherentCycleOwnerCore_covers H P K g N n
    hHMono hCover e he

/-- No retained full owner contributes a support edge outside the actual
old ambient support at that stage, provided all designated pieces do so. -/
theorem coherentCycleOwnerSupport_subset_old {W : Type v}
    (H : ℕ → Set (Set W))
    (P : ℕ → Set (HypergraphPiece W))
    (K : Finset (Set W)) (g N n : ℕ)
    (hHMono : Monotone H) (hPMono : Monotone P)
    (hCover : ∀ t e, e ∈ H t →
      ∃ D : HypergraphPiece W, D ∈ P t ∧ e ∈ D.edges)
    (hAmbient : ∀ t (D : HypergraphPiece W), D ∈ P t →
      D.edges ⊆ H t) :
    coherentCycleOwnerSupport H P K g N n ⊆ H n := by
  rintro e ⟨D, hD, he⟩
  exact hAmbient n D
    (coherentCycleOwnerCore_subset H P K g N n
      hHMono hPMono hCover D hD) he

/-- All short-girth tests for every subfamily of a candidate batch are
unchanged when the old support is replaced by the supports of finitely
many *actual old designated B-pieces*.

This is stronger than selecting abstract support edges: each retained
edge has a retained B-owner, and we keep all support edges of that
owner. The owner family need not itself be a forest. -/
theorem coherentCycleOwnerSupport_girth_iff {W : Type v}
    (H : ℕ → Set (Set W))
    (P : ℕ → Set (HypergraphPiece W))
    (K J : Finset (Set W)) (g N n : ℕ)
    (hHMono : Monotone H) (hPMono : Monotone P)
    (hCover : ∀ t e, e ∈ H t →
      ∃ D : HypergraphPiece W, D ∈ P t ∧ e ∈ D.edges)
    (hAmbient : ∀ t (D : HypergraphPiece W), D ∈ P t →
      D.edges ⊆ H t)
    (hn : n ≤ N) (hJK : J ⊆ K) :
    GirthGT (H n ∪ (↑J : Set (Set W))) g ↔
      GirthGT (coherentCycleOwnerSupport H P K g N n ∪
        (↑J : Set (Set W))) g := by
  have hSub :=
    coherentCycleOwnerSupport_subset_old H P K g N n
      hHMono hPMono hCover hAmbient
  have hCore :=
    coherentBatchCycleCore_subset_ownerSupport H P K g N n
      hHMono hCover
  constructor
  · intro hOld
    apply girthGT_of_subset
      (H := coherentCycleOwnerSupport H P K g N n ∪
        (↑J : Set (Set W)))
      (K := H n ∪ (↑J : Set (Set W)))
    · intro e he
      rcases he with he | he
      · exact Or.inl (hSub he)
      · exact Or.inr he
    · exact hOld
  · intro hRetained
    apply (coherentBatchCycleCore_girth_iff H K J g N n
      hHMono hn hJK).mpr
    apply girthGT_of_subset
      (H := (↑(coherentBatchCycleCore H K g N n) :
        Set (Set W)) ∪ (↑J : Set (Set W)))
      (K := coherentCycleOwnerSupport H P K g N n ∪
        (↑J : Set (Set W)))
    · intro e he
      rcases he with he | he
      · exact Or.inl (hCore he)
      · exact Or.inr he
    · exact hRetained

end StructuralRamsey.Girth
