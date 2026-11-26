import Girth.ContactFocusingChain
import Girth.ContactGluedOrder

/-! Transfer the full recursive picture invariant from actual
strip embeddings. There are two variants: main system-girth
preservation, and direct forest boost. -/

namespace StructuralRamsey.Girth
universe v
variable {V E I U F J X B : Type v}

namespace ContactDesignatedEmbeddings
variable {m : ℕ} {L : ContactHypergraphData V E I} {S : ContactTrainData E m}
    {base : B → Set X} {P : ContactBaseProjection L base} {b : B}
    {D : ContactHypergraphData U F J} {T : ContactTrainData F m}
    (M : ContactDesignatedEmbeddings (P.stripHypergraph b) (P.stripTrain S b) D T)

variable (hne : Nonempty (P.StripEdge b))
    (p : U → X)
    (hpart : ∀ i x, p ((M.emb i).vertex x) = P.stripPart b x)
    (himage : ∀ f, p '' D.edgeCarrier f = base b)
    (hinj : ∀ f, Set.InjOn p (D.edgeCarrier f))

noncomputable def nextProjection :
    ContactBaseProjection (M.stripGluing hne).outputHypergraph base :=
  (M.stripGluing hne).outputProjection P b p (M.stripGluing_active hne)
    (M.stripGluing_coreOver hne p hpart himage hinj)

theorem allowed_pullback_core (C : Set X) :
    (M.stripGluing hne).coreV ⁻¹'
        ((M.nextProjection hne p hpart himage hinj).vertex ⁻¹' C) =
      p ⁻¹' C := by
  ext x
  rfl

theorem allowed_pullback_std (i : J) (C : Set X) :
    (M.stripGluing hne).stdV i ⁻¹'
        ((M.nextProjection hne p hpart himage hinj).vertex ⁻¹' C) =
      P.vertex ⁻¹' C := by
  ext x
  change (M.stripGluing hne).outputProjectionVertex P p
      ((M.stripGluing hne).stdV i x) ∈ C ↔ P.vertex x ∈ C
  rw [(M.stripGluing hne).projection_vertex_std P b p
    (M.stripGluing_coreOver hne p hpart himage hinj)]

theorem next_parameters (allowed : Fin m → Set X)
    (hD : D.Parameters T (fun j => p ⁻¹' allowed j))
    (hL : L.Parameters S (fun j => P.vertex ⁻¹' allowed j))
    (q : Fin (m+1) → ℕ)
    (hgeom : D.PositiveBounds T q) :
    (M.stripGluing hne).outputHypergraph.Parameters (M.stripGluing hne).outputTrain
      (fun j => (M.nextProjection hne p hpart himage hinj).vertex ⁻¹' allowed j) := by
  apply (M.stripGluing hne).preserves_parameters
  · intro j
    change D.Parameter T j.castSucc j.succ
      ((M.stripGluing hne).coreV ⁻¹' ((M.nextProjection hne p hpart himage hinj).vertex ⁻¹' allowed j))
    rw [M.allowed_pullback_core hne p hpart himage hinj]
    exact hD j
  · intro i j
    change L.Parameter S j.castSucc j.succ
      ((M.stripGluing hne).stdV i ⁻¹' ((M.nextProjection hne p hpart himage hinj).vertex ⁻¹' allowed j))
    rw [M.allowed_pullback_std hne p hpart himage hinj]
    exact hL j
  · intro μ hp ht
    exact ⟨(hgeom μ hp ht).g1,(hgeom μ hp ht).g2⟩
  · exact M.copy_covered

/-- Main induction step, with only the actual old and core
bounds as hypotheses. -/
theorem next_systemBounds (q : Fin (m+1) → ℕ)
    (hq : ∀ μ, μ.val < m → 2 ≤ q μ)
    (hbase : ∀ a c : B, a ≠ c → (base a ∩ base c).Subsingleton)
    (hD0 : D.bottomCut.ZeroSmallMixedForestsThrough (q ⟨0,by omega⟩))
    (hD : D.PositiveBounds T q) (hL : L.SystemBounds S q)
    (hsize : ∀ e, (D.edgeCarrier e).Nontrivial) (hm : 0 < m) :
    (M.stripGluing hne).outputHypergraph.SystemBounds (M.stripGluing hne).outputTrain q := by
  let A := M.stripGluing hne
  have ha := M.stripGluing_active hne
  exact A.preserves_systemBounds q hq (A.stripStrong_of_projection P b ha hbase)
    (A.stripAbsorption_of_projection P b ha)
    ((D.bottomCut.zeroSmallMixedForests_iff (hq ⟨0,by omega⟩ hm)).mp hD0)
    hD hL M.copy_edge_subset hsize

/-- Forest boost, including the first step at j=2. -/
theorem next_forestBoost
    [Fintype (M.stripGluing hne).Vertex] {j : ℕ} (hj : 2 ≤ j)
    (q : Fin (m+1) → ℕ)
    (hq : ∀ μ, 0 < μ.val → μ.val < m → 2 ≤ q μ)
    (hbase : ∀ a c : B, a ≠ c → (base a ∩ base c).Subsingleton)
    (hlin : ∀ e f : F, e ≠ f → (D.edgeCarrier e ∩ D.edgeCarrier f).Subsingleton)
    (hg : LabelledGirthGT D.edgeCarrier j)
    (hD0 : D.bottomCut.ZeroSmallMixedForestsThrough (j-1))
    (hL0 : L.bottomCut.ZeroSmallMixedForestsThrough j)
    (hD : D.PositiveBounds T q) (hL : L.PositiveBounds S q) :
    (M.stripGluing hne).outputHypergraph.bottomCut.ZeroSmallMixedForestsThrough j ∧
      (M.stripGluing hne).outputHypergraph.PositiveBounds (M.stripGluing hne).outputTrain q := by
  let A := M.stripGluing hne
  have ha := M.stripGluing_active hne
  exact ⟨A.directIncrement hj P b ha hbase hlin hg hD0 hL0,
    A.preserves_positiveBounds q hq (A.stripStrong_of_projection P b ha hbase) hD hL⟩

/-- Compatible orders on the active strip give an actual order
on the tagged picture. -/
theorem next_order [Fintype U] [Fintype V] [Finite J] [LinearOrder U] [LinearOrder V]
    (hord : ∀ i (x y : P.StripVertex b), x.val < y.val →
      (M.emb i).vertex x < (M.emb i).vertex y) :
    ∃ o : LinearOrder (M.stripGluing hne).Vertex,
      (∀ x y : U, x < y → o.lt ((M.stripGluing hne).coreV x) ((M.stripGluing hne).coreV y)) ∧
      (∀ i (x y : V), x < y →
        o.lt ((M.stripGluing hne).stdV i x) ((M.stripGluing hne).stdV i y)) := by
  let A := M.stripGluing hne
  have hc : ContactGluedOrder.Compatible A.vertexGlue := by
    intro i x y u w hx hy hxy
    obtain ⟨hx,he⟩ := (M.vertexPartial_iff i x u).mp hx
    obtain ⟨hy,hf⟩ := (M.vertexPartial_iff i y w).mp hy
    exact he ▸ hf ▸ hord i ⟨x,hx⟩ ⟨y,hy⟩ hxy
  exact ContactGluedOrder.exists_order A.vertexGlue hc A.vertex_inj

end ContactDesignatedEmbeddings
end StructuralRamsey.Girth
