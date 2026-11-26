import Girth.ContactFutureStrip

/-! Complete the actual future-strip refinement data. The
new first parameters are the old refined parameters followed
by A₁ ∩ b ∩ c; the retained tail parameters and wagon bounds
are inherited from the actual output train. -/

namespace StructuralRamsey.Girth
universe v
variable {V E I V₀ E₀ I₀ X B : Type v}

namespace ContactTrainStrip
variable {d h : ℕ}
    {D : ContactHypergraphData V E I} {L : ContactHypergraphData V₀ E₀ I₀}
    {T : ContactTrainData E (h+1)} {S : ContactTrainData E₀ (h+1)}
    (A : ContactTrainStrip D L T S)
    {base : B → Set X} (P : ContactBaseProjection L base) (b c : B)
    (ha : A.ActiveOver P b) (hne : c ≠ b)
    (hd : 0 < d)
    (R : ContactTrainData (A.OldStripEdge P c) (d+h))
    (hret : ∀ e f, R.parent ⟨d,by omega⟩ e = R.parent ⟨d,by omega⟩ f ↔
      S.parent ⟨1,by omega⟩ e.val = S.parent ⟨1,by omega⟩ f.val)

noncomputable abbrev nextRefinement :=
  A.futureRefinement P b c ha hne rfl hd R hret

/-- The actual parameter vector of the next refinement, on base
parts. In particular the new part is a subset of A₁. -/
def futureAllowed
    (old : Fin d → Set X) (allowed : Fin (h+1) → Set X)
    (j : Fin (d+1+h)) : Set X :=
  if hj : j.val < d then old ⟨j.val,hj⟩
  else if he : j.val = d then (base b ∩ base c) ∩ allowed 0
  else allowed ⟨j.val-d,by have := j.isLt; omega⟩

include hne in
theorem futureAllowed_singleton
    (old : Fin d → Set X) (allowed : Fin (h+1) → Set X)
    (hold : ∀ j, (old j).Subsingleton)
    (hbase : ∀ u v : B, u ≠ v → (base u ∩ base v).Subsingleton)
    (j : Fin (d+1+h)) (hj : j.val ≤ d) :
    (futureAllowed (base := base) b c old allowed j).Subsingleton := by
  by_cases hlt : j.val < d
  · simpa only [futureAllowed,dif_pos hlt] using hold ⟨j.val,hlt⟩
  · have he : j.val = d := by omega
    rw [futureAllowed,dif_neg hlt,dif_pos he]
    intro x hx y hy
    exact hbase b c (fun h => hne h.symm) hx.1 hy.1

theorem futureAllowed_subset_first
    (old : Fin d → Set X) (allowed : Fin (h+1) → Set X)
    (hold : ∀ j, old j ⊆ allowed 0)
    (j : Fin (d+1+h)) (hj : j.val ≤ d) :
    futureAllowed (base := base) b c old allowed j ⊆ allowed 0 := by
  by_cases hlt : j.val < d
  · simpa only [futureAllowed,dif_pos hlt] using hold ⟨j.val,hlt⟩
  · have he : j.val = d := by omega
    rw [futureAllowed,dif_neg hlt,dif_pos he]
    exact Set.inter_subset_right

/-- All new parameters on the actual future strip, including the
inserted one-part overlap and every retained tail parameter. -/
theorem future_refinement_parameters
    (p : V → X) (hc : A.CoreOver P b p)
    (old : Fin d → Set X) (allowed : Fin (h+1) → Set X)
    (hL : ∀ j : Fin d,
      (L.pullEdges (A.oldStripInclusion P c)).Parameter R
        ⟨j.val,by have := j.isLt; omega⟩ ⟨j.val+1,by have := j.isLt; omega⟩
        (P.vertex ⁻¹' old j))
    (hH : A.outputHypergraph.Parameters A.outputTrain
      (fun j => A.outputProjectionVertex P p ⁻¹' allowed j)) :
    (A.futureHypergraph P b c ha hne).Parameters
      (A.nextRefinement P b c ha hne hd R hret).train
      (fun j => A.outputProjectionVertex P p ⁻¹'
        futureAllowed (base := base) b c old allowed j) := by
  let U := A.nextRefinement P b c ha hne hd R hret
  let H := A.futureHypergraph P b c ha hne
  let D₀ := L.pullEdges (A.oldStripInclusion P c)
  let proj := A.outputProjectionVertex P p
  let C : I → Set A.Vertex := fun i => A.coreV '' D.copyCarrier i
  let overlap : Set A.Vertex := proj ⁻¹' (base b ∩ base c)
  have hcarrier : ∀ i e, H.edgeCarrier (i,e) = A.stdV i '' D₀.edgeCarrier e :=
    A.future_carrier P b c ha hne
  have hcross : U.CrossTrace H C overlap :=
    A.future_cross_trace P b c ha hne p hc
  have hco (j : Fin (h+1)) :
      H.Parameter U.coarse j.castSucc j.succ (proj ⁻¹' allowed j) :=
    A.outputHypergraph.pull_parameter A.outputTrain (A.futureEmbedding P b c ha hne)
      j.castSucc j.succ _ (hH j)
  apply U.all_parameters H
  · intro j hj
    rw [futureAllowed,dif_pos hj]
    apply U.prefix_parameter D₀ H A.stdV hcarrier j.castSucc j.succ
      (by change j.val+1 ≤ d; omega) (by exact hj.le)
    intro i
    have he : A.stdV i ⁻¹' (proj ⁻¹' old ⟨j.val,hj⟩) =
        P.vertex ⁻¹' old ⟨j.val,hj⟩ := by
      ext x
      change proj (A.stdV i x) ∈ old ⟨j.val,hj⟩ ↔ P.vertex x ∈ old ⟨j.val,hj⟩
      exact iff_of_eq (congrArg (fun y => y ∈ old ⟨j.val,hj⟩)
        (A.projection_vertex_std P b p hc i x))
    rw [he]
    exact hL ⟨j.val,hj⟩
  · rw [futureAllowed,dif_neg (by change ¬ d < d; omega),dif_pos rfl]
    change H.Parameter U.train ⟨d,by omega⟩ ⟨d+1,by omega⟩
      (overlap ∩ proj ⁻¹' allowed 0)
    exact U.split_parameter H C overlap (proj ⁻¹' allowed 0) (hco 0) hcross
  · intro j hj
    rw [futureAllowed,dif_neg (by omega),dif_neg (by omega)]
    apply U.tail_parameter H j.castSucc j.succ (by exact hj)
      (by change d < j.val+1; omega)
    let k : Fin (h+1) := ⟨j.val-d,by have := j.isLt; omega⟩
    have h₁ : U.tailLevel j.castSucc hj = k.castSucc := Fin.ext rfl
    have h₂ : U.tailLevel j.succ (by change d < j.val+1; omega) = k.succ := by
      apply Fin.ext
      change j.val+1-d = j.val-d+1
      omega
    rw [h₁,h₂]
    exact hco k

/-- The actual new wagon bounds, not just the prefix. If the
retained first level is top (h=0), its family has at most one
label, so there is no extra positive-cut hypothesis. -/
theorem future_refinement_wagonBounds {g : ℕ} (hg : 2 ≤ g)
    (p : V → X) (hc : A.CoreOver P b p)
    (hbase : ∀ u v : B, u ≠ v → (base u ∩ base v).Subsingleton)
    (hD : D.bottomCut.ZeroSmallMixedForestsThrough g)
    (q : Fin (h+1+1) → ℕ) (hq : h > 0 → g ≤ q ⟨1,by omega⟩)
    (hH : A.outputHypergraph.WagonBounds A.outputTrain q)
    (firstAllowed : Set A.Vertex)
    (hpar : A.outputHypergraph.Parameter A.outputTrain ⟨0,by omega⟩ ⟨1,by omega⟩ firstAllowed)
    (hold : ∀ μ : Fin (d+h+1), μ.val < d →
      LabelledGirthGT ((L.pullEdges (A.oldStripInclusion P c)).atCut (R.parent μ)).contactWagonCarrier g) :
    (A.futureHypergraph P b c ha hne).WagonBounds
      (A.nextRefinement P b c ha hne hd R hret).train
      ((A.nextRefinement P b c ha hne hd R hret).newBounds g q) := by
  let U := A.nextRefinement P b c ha hne hd R hret
  let H := A.futureHypergraph P b c ha hne
  have hg₁ : LabelledGirthGT
      (A.outputHypergraph.atCut (A.outputTrain.parent ⟨1,by omega⟩)).contactWagonCarrier g := by
    by_cases hh : 0 < h
    · rintro ⟨C,hC⟩
      exact hH ⟨1,by omega⟩ (by omega) ⟨C,hC.trans (hq hh)⟩
    · have he : (⟨1,by omega⟩ : Fin (h+1+1)) = ⟨h+1,by omega⟩ :=
        Fin.ext (by omega)
      rw [he]
      exact A.outputHypergraph.top_wagonGirth A.outputTrain g
  have hp := A.future_refinement_prefix_girth P b c ha hne rfl hd hg R hret p hc
    hbase hD firstAllowed hpar hg₁ hold
  have ht : H.WagonBounds U.coarse q :=
    fun μ hμ => A.outputHypergraph.pull_wagonGirth A.outputTrain
      (A.futureEmbedding P b c ha hne) μ (hH μ hμ)
  exact U.all_wagonBounds H g q hp ht

end ContactTrainStrip
end StructuralRamsey.Girth
