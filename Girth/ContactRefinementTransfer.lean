import Girth.ContactForgetLevels
import Girth.ContactTrainEmbedding
import Girth.ContactTrainPullback
import Girth.ContactParentMap

/-! Transport of actual train witnesses across retained cuts
and bijective relabelling of the edge type. These are the
bookkeeping operations used when the recursive core is built
with inserted single-part levels and then restored to the
original height. No carrier or copy label changes under
forgetting levels. -/

namespace StructuralRamsey.Girth
universe v
variable {V E I U F J : Type v}

namespace ContactTrainEmbedding
variable {m n : ℕ}
    {D : ContactHypergraphData V E I} {T : ContactTrainData E m}
    {H : ContactHypergraphData U F J} {S : ContactTrainData F m}
    (M : ContactTrainEmbedding D T H S)

/-- Restriction to retained cuts preserves actual train
embeddings, including strongness. -/
def retainLevels (f : Fin (n+1) → Fin (m+1)) (hf : Monotone f)
    (h0 : f ⟨0,by omega⟩ = ⟨0,by omega⟩)
    (ht : f ⟨n,by omega⟩ = ⟨m,by omega⟩) :
    ContactTrainEmbedding D (T.retainLevels f hf h0 ht)
      H (S.retainLevels f hf h0 ht) where
  vertex := M.vertex
  edge := M.edge
  carrier_eq := M.carrier_eq
  rel_iff := fun μ e g => M.rel_iff (f μ) e g
  strong := M.strong

end ContactTrainEmbedding

namespace ContactDesignatedEmbeddings
variable {m n : ℕ}
    {D : ContactHypergraphData V E I} {T : ContactTrainData E m}
    {H : ContactHypergraphData U F J} {S : ContactTrainData F m}
    (M : ContactDesignatedEmbeddings D T H S)

def retainLevels (f : Fin (n+1) → Fin (m+1)) (hf : Monotone f)
    (h0 : f ⟨0,by omega⟩ = ⟨0,by omega⟩)
    (ht : f ⟨n,by omega⟩ = ⟨m,by omega⟩) :
    ContactDesignatedEmbeddings D (T.retainLevels f hf h0 ht)
      H (S.retainLevels f hf h0 ht) where
  emb := fun i => (M.emb i).retainLevels f hf h0 ht
  vertex_eq := M.vertex_eq
  edge_eq := M.edge_eq

theorem retainLevels_arrow {Color : Type v}
    (f : Fin (n+1) → Fin (m+1)) (hf : Monotone f)
    (h0 : f ⟨0,by omega⟩ = ⟨0,by omega⟩)
    (ht : f ⟨n,by omega⟩ = ⟨m,by omega⟩)
    (h : M.Arrow Color) :
    (M.retainLevels f hf h0 ht).Arrow Color := h

end ContactDesignatedEmbeddings

namespace ContactTrainData
variable {m : ℕ} (T : ContactTrainData E m)

/-- Bijective edge relabelling keeps the actual wagon types,
including the top and all proper cuts. -/
def relabelEdges (e : F ≃ E) : ContactTrainData F m where
  Wagon := T.Wagon
  parent := fun μ f => T.parent μ (e f)
  surj := fun μ => (T.surj μ).comp e.surjective
  nested := fun μ ν h a b he => T.nested μ ν h (e a) (e b) he
  bottom := by
    intro a b h
    exact e.injective (T.bottom h)
  top := fun a b => T.top (e a) (e b)

end ContactTrainData

namespace ContactHypergraphData
variable {m : ℕ} (D : ContactHypergraphData V E I)
    (T : ContactTrainData E m)

theorem relabelEdges_wagonCarrier (e : F ≃ E) (μ : Fin (m+1)) (p : T.Wagon μ) :
    ((D.pullEdges e.toEmbedding).atCut ((T.relabelEdges e).parent μ)).contactWagonCarrier p =
      (D.atCut (T.parent μ)).contactWagonCarrier p := by
  ext x
  constructor
  · rintro ⟨f,hf,hx⟩
    exact ⟨e f,hf,hx⟩
  · rintro ⟨f,hf,hx⟩
    exact ⟨e.symm f,by change T.parent μ (e (e.symm f)) = p; rw [e.apply_symm_apply]; exact hf,
      by change x ∈ D.edgeCarrier (e (e.symm f)); rw [e.apply_symm_apply]; exact hx⟩

theorem relabelEdges_wagonBounds (e : F ≃ E) (q : Fin (m+1) → ℕ)
    (h : D.WagonBounds T q) :
    (D.pullEdges e.toEmbedding).WagonBounds (T.relabelEdges e) q := by
  intro μ hp
  have he : ((D.pullEdges e.toEmbedding).atCut ((T.relabelEdges e).parent μ)).contactWagonCarrier =
      (D.atCut (T.parent μ)).contactWagonCarrier :=
    funext (D.relabelEdges_wagonCarrier T e μ)
  rw [he]
  exact h μ hp

theorem relabelEdges_parameters (e : F ≃ E) (allowed : Fin m → Set V)
    (h : D.Parameters T allowed) :
    (D.pullEdges e.toEmbedding).Parameters (T.relabelEdges e) allowed := by
  intro j a b x he hx hy hn
  exact h j (e a) (e b) x he hx hy hn

end ContactHypergraphData

/-- The actual retained cut injection for a depth-d refinement:
zero is fixed, and every positive cut is shifted by d-1. -/
def contactRetainRefinement (d h : ℕ) (hd : 0 < d) :
    Fin (h+2) → Fin (d+h+1) :=
  fun μ => if hz : μ.val = 0 then ⟨0,by omega⟩ else ⟨μ.val+d-1,by have := μ.isLt; omega⟩

theorem contactRetainRefinement_strict (d h : ℕ) (hd : 0 < d) :
    StrictMono (contactRetainRefinement d h hd) := by
  intro x y hxy
  have hval : x.val < y.val := hxy
  change (contactRetainRefinement d h hd x).val < (contactRetainRefinement d h hd y).val
  by_cases hx : x.val = 0
  · have hy : y.val ≠ 0 := by omega
    simp only [contactRetainRefinement,dif_pos hx,dif_neg hy]
    omega
  · have hy : y.val ≠ 0 := by omega
    simp only [contactRetainRefinement,dif_neg hx,dif_neg hy]
    omega

theorem contactRetainRefinement_zero (d h : ℕ) (hd : 0 < d) :
    contactRetainRefinement d h hd 0 = 0 := by
  simp [contactRetainRefinement]

theorem contactRetainRefinement_top (d h : ℕ) (hd : 0 < d) :
    contactRetainRefinement d h hd ⟨h+1,by omega⟩ = ⟨d+h,by omega⟩ := by
  apply Fin.ext
  change (contactRetainRefinement d h hd ⟨h+1,by omega⟩).val = d+h
  simp only [contactRetainRefinement,dif_neg (by omega : h+1 ≠ 0)]
  omega

end StructuralRamsey.Girth
