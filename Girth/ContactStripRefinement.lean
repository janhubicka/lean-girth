import Girth.ContactTrainMainIteration
import Girth.ContactFutureRefinement
import Girth.ContactRefinementTransfer

/-! Candidate: the concrete refinement invariant for the main induction.

Use the ambient vertex type and the actual restricted edge labels. Isolated
ambient vertices are harmless for both wagon girth and train parameters. This
is exactly the representation used by `ContactFutureStrip`; cutting down the
vertex type to the union of the edges is needed only for the recursive core
call, not for the invariant. No auxiliary copy or edge labels are added.
-/

namespace StructuralRamsey.Girth
universe v
variable {V E I X B : Type v} {h : ℕ}
variable {D : ContactHypergraphData V E I} {base : B → Set X}

namespace ContactBaseProjection

/-- Depth-d refinement of a nonempty strip of a height-(h+1) train.
The prefix has singleton allowed parts contained in the first original
parameter. The retained positive cuts agree as equivalence relations,
not as chosen types of wagon labels. Tail bounds and tail parameters
will be pulled back from the actual coarse picture. -/
structure StripRefinement (P : ContactBaseProjection D base)
    (T : ContactTrainData E (h+1)) (allowed : Fin (h+1) → Set X)
    (g : ℕ) (b : B) where
  depth : ℕ
  depth_pos : 0 < depth
  train : ContactTrainData (P.StripEdge b) (depth+h)
  prefixAllowed : Fin depth → Set X
  singleton : ∀ j, (prefixAllowed j).Subsingleton
  subset_first : ∀ j, prefixAllowed j ⊆ allowed 0
  prefix_parameters : ∀ j : Fin depth,
    (D.pullEdges (P.stripEdgeEmb b)).Parameter train
      ⟨j.val,by have := j.isLt; omega⟩ ⟨j.val+1,by have := j.isLt; omega⟩
      (P.vertex ⁻¹' prefixAllowed j)
  prefix_girth : ∀ μ : Fin (depth+h+1), μ.val < depth →
    LabelledGirthGT ((D.pullEdges (P.stripEdgeEmb b)).atCut
      (train.parent μ)).contactWagonCarrier g
  retained : ∀ μ : Fin (h+2), 0 < μ.val → ∀ e f : P.StripEdge b,
    train.parent ⟨μ.val+depth-1,by have := μ.isLt; omega⟩ e =
      train.parent ⟨μ.val+depth-1,by have := μ.isLt; omega⟩ f ↔
    T.parent μ e.val = T.parent μ f.val

namespace StripRefinement
variable {P : ContactBaseProjection D base} {T : ContactTrainData E (h+1)}
    {allowed : Fin (h+1) → Set X} {g : ℕ} {b : B}
    (R : P.StripRefinement T allowed g b)

/-- The boundary hypothesis used by the checked split-refinement module. -/
theorem boundary (e f : P.StripEdge b) :
    R.train.parent ⟨R.depth,by omega⟩ e = R.train.parent ⟨R.depth,by omega⟩ f ↔
      T.parent ⟨1,by omega⟩ e.val = T.parent ⟨1,by omega⟩ f.val := by
  have hd := R.depth_pos
  have H := R.retained ⟨1,by omega⟩ (by omega) e f
  have he : (⟨1+R.depth-1,by omega⟩ : Fin (R.depth+h+1)) =
      ⟨R.depth,by omega⟩ := Fin.ext (by omega)
  rw [he] at H
  exact H

end StripRefinement

/-- The depth-one refinement is just the coarse train on the strip.
A matching allows the first parameter to be empty. The bottom girth
is inherited from the original system at the requested smaller cutoff.
No restriction on the original first parameter is needed. -/
noncomputable def matchingRefinement (P : ContactBaseProjection D base)
    (T : ContactTrainData E (h+1)) (allowed : Fin (h+1) → Set X)
    (g : ℕ) (b : B)
    (hmatch : ∀ e f : P.StripEdge b, e ≠ f →
      D.edgeCarrier e.val ∩ D.edgeCarrier f.val = ∅)
    (hg : LabelledGirthGT (D.atCut (T.parent 0)).contactWagonCarrier g) :
    P.StripRefinement T allowed g b := by
  let U := T.pullTrain (P.stripEdgeEmb b)
  let shift : Fin (1+h+1) → Fin (h+1+1) := fun μ => ⟨μ.val,by have := μ.isLt; omega⟩
  have hs : Monotone shift := fun _ _ hh => hh
  have hz : shift 0 = 0 := Fin.ext rfl
  have ht : shift ⟨1+h,by omega⟩ = ⟨h+1,by omega⟩ := Fin.ext (by omega)
  refine {
    depth := 1
    depth_pos := by omega
    train := U.retainLevels shift hs hz ht
    prefixAllowed := fun _ => ∅
    singleton := by
      intro j x hx
      exact (show False from hx).elim
    subset_first := fun _ => Set.empty_subset _
    prefix_parameters := ?_
    prefix_girth := ?_
    retained := ?_ }
  · intro j e f x _ hx hy _
    have he : e = f := by
      by_contra hn
      have hm : x ∈ D.edgeCarrier e.val ∩ D.edgeCarrier f.val := ⟨hx,hy⟩
      rw [hmatch e f hn] at hm
      exact hm
    subst f
    rfl
  · intro μ hm
    have hz' : shift μ = 0 := Fin.ext (by change μ.val = 0; omega)
    change LabelledGirthGT ((D.pullEdges (P.stripEdgeEmb b)).atCut
      (U.parent (shift μ))).contactWagonCarrier g
    rw [hz']
    exact D.pull_wagonGirth T (P.stripEdgeEmb b) 0 hg
  · intro μ _ e f
    have he : shift ⟨μ.val+1-1,by have := μ.isLt; omega⟩ = μ := Fin.ext (by omega)
    change U.parent (shift ⟨μ.val+1-1,by have := μ.isLt; omega⟩) e =
      U.parent (shift ⟨μ.val+1-1,by have := μ.isLt; omega⟩) f ↔ _
    rw [he]
    exact T.pullTrain_rel (P.stripEdgeEmb b) μ e f

end ContactBaseProjection

namespace ContactTrainPicture
variable {W F J : Type v}
variable {L : ContactHypergraphData W F J} {S : ContactTrainData F (h+1)}
variable [LinearOrder W] [LinearOrder X]
variable {allowed : Fin (h+1) → Set X} {q : Fin (h+2) → ℕ}

/-- The invariant used by `MainCoreSupply`. The reverse list contains
processed base edges, so the next call has a refinement whenever it
has a nonempty active strip. -/
def HasFutureRefinements (g : ℕ)
    (P : ContactTrainPicture L S base allowed q) (done : List B) : Prop :=
  ∀ b : B, b ∉ done → Nonempty (P.projection.StripEdge b) →
    Nonempty (P.projection.StripRefinement P.train allowed g b)

theorem hasFutureRefinements_skip {g : ℕ}
    {P : ContactTrainPicture L S base allowed q} {done : List B} {b : B}
    (H : HasFutureRefinements g P done) : HasFutureRefinements g P (b :: done) := by
  intro c hc hn
  exact H c (fun hd => hc (List.mem_cons_of_mem _ hd)) hn

end ContactTrainPicture

namespace ContactTrainStrip
variable {U G K U₀ G₀ K₀ : Type v}
variable {C : ContactHypergraphData U G K} {L : ContactHypergraphData U₀ G₀ K₀}
variable {T : ContactTrainData G (h+1)} {S : ContactTrainData G₀ (h+1)}
variable (A : ContactTrainStrip C L T S)
variable (P : ContactBaseProjection L base) (b c : B)
variable (ha : A.ActiveOver P b) (hne : c ≠ b)
variable (p : U → X) (hc : A.CoreOver P b p)
variable {allowed : Fin (h+1) → Set X} {g : ℕ}

/-- The exact graph equality needed to move the product-labelled future
refinement back to the subtype of actual output edges. Both sides have
no designated copies; in particular no deduplication is involved. -/
theorem future_pull_relabel :
    (A.futureHypergraph P b c ha hne).pullEdges
      (A.futureEdgeEquiv P b c ha hne).symm.toEmbedding =
    A.outputHypergraph.pullEdges ((A.outputProjection P b p ha hc).stripEdgeEmb c) := by
  let e := A.futureEdgeEquiv P b c ha hne
  have he : e.symm.toEmbedding.trans (A.futureEmbedding P b c ha hne) =
      (A.outputProjection P b p ha hc).stripEdgeEmb c := by
    ext f
    change (e (e.symm f)).val = f.val
    rw [e.apply_symm_apply]
  change (A.outputHypergraph.pullEdges (A.futureEmbedding P b c ha hne)).pullEdges
    e.symm.toEmbedding = _
  rw [← he]
  rfl

/-- Future refinement on the *actual* future strip, not a surrogate
product of labels. The old prefix data is used only on the old strip;
all new conditions are provided by the previously checked split lemmas.
-/
noncomputable def advanceStripRefinement
    (R : P.StripRefinement S allowed g c)
    (hg : 2 ≤ g)
    (hbase : ∀ u v : B, u ≠ v → (base u ∩ base v).Subsingleton)
    (hC : C.bottomCut.ZeroSmallMixedForestsThrough g)
    (hpar : A.outputHypergraph.Parameters A.outputTrain
      (fun j => A.outputProjectionVertex P p ⁻¹' allowed j))
    (hcoarse : LabelledGirthGT
      (A.outputHypergraph.atCut (A.outputTrain.parent ⟨1,by omega⟩)).contactWagonCarrier g) :
    (A.outputProjection P b p ha hc).StripRefinement A.outputTrain allowed g c := by
  let d := R.depth
  have hd : 0 < d := R.depth_pos
  let e := A.futureEdgeEquiv P b c ha hne
  let H := A.futureHypergraph P b c ha hne
  let U := A.nextRefinement P b c ha hne R.depth_pos R.train R.boundary
  let a := ContactTrainStrip.futureAllowed (base := base) b c R.prefixAllowed allowed
  have hparams := A.future_refinement_parameters P b c ha hne R.depth_pos R.train
    R.boundary p hc R.prefixAllowed allowed R.prefix_parameters hpar
  have hpref := A.future_refinement_prefix_girth P b c ha hne rfl R.depth_pos hg
    R.train R.boundary p hc hbase hC (A.outputProjectionVertex P p ⁻¹' allowed 0)
    (hpar 0) hcoarse R.prefix_girth
  have he := A.future_pull_relabel P b c ha hne p hc
  refine {
    depth := d+1
    depth_pos := by omega
    train := U.train.relabelEdges e.symm
    prefixAllowed := fun j => a ⟨j.val,by have := j.isLt; omega⟩
    singleton := ?_
    subset_first := ?_
    prefix_parameters := ?_
    prefix_girth := ?_
    retained := ?_ }
  · intro j
    have hj := j.isLt
    exact ContactTrainStrip.futureAllowed_singleton (base := base) b c hne
      R.prefixAllowed allowed R.singleton hbase ⟨j.val,by have := j.isLt; omega⟩ (by omega)
  · intro j
    have hj := j.isLt
    exact ContactTrainStrip.futureAllowed_subset_first (base := base) b c
      R.prefixAllowed allowed R.subset_first ⟨j.val,by have := j.isLt; omega⟩ (by omega)
  · intro j
    have hh := H.relabelEdges_parameters U.train e.symm
      (fun k => A.outputProjectionVertex P p ⁻¹' a k) hparams
    rw [he] at hh
    exact hh ⟨j.val,by have := j.isLt; omega⟩
  · intro μ hm
    have hh : LabelledGirthGT ((H.pullEdges e.symm.toEmbedding).atCut
        ((U.train.relabelEdges e.symm).parent μ)).contactWagonCarrier g := by
      rw [show ((H.pullEdges e.symm.toEmbedding).atCut
          ((U.train.relabelEdges e.symm).parent μ)).contactWagonCarrier =
          (H.atCut (U.train.parent μ)).contactWagonCarrier from
        funext (H.relabelEdges_wagonCarrier U.train e.symm μ)]
      exact hpref μ (by omega)
    rw [he] at hh
    exact hh
  · intro μ hm x y
    let ν : Fin (d+1+h+1) := ⟨μ.val+(d+1)-1,by have := μ.isLt; omega⟩
    have hν : d < ν.val := by change d < μ.val+(d+1)-1; omega
    have hμ : U.tailLevel ν hν = μ := Fin.ext (by
      change μ.val+(d+1)-1-d = μ.val
      omega)
    change U.train.parent ν (e.symm x) = U.train.parent ν (e.symm y) ↔ _
    rw [U.tail_eq ν hν,hμ]
    change (A.outputTrain.pullTrain (A.futureEmbedding P b c ha hne)).parent μ (e.symm x) =
      (A.outputTrain.pullTrain (A.futureEmbedding P b c ha hne)).parent μ (e.symm y) ↔ _
    rw [A.outputTrain.pullTrain_rel]
    have hx : A.futureEmbedding P b c ha hne (e.symm x) = x.val := by
      change (e (e.symm x)).val = x.val
      rw [e.apply_symm_apply]
    have hy : A.futureEmbedding P b c ha hne (e.symm y) = y.val := by
      change (e (e.symm y)).val = y.val
      rw [e.apply_symm_apply]
    rw [hx,hy]

end ContactTrainStrip

namespace ContactTrainPicture
variable {W F J : Type v}
variable {L : ContactHypergraphData W F J} {S : ContactTrainData F (h+1)}
variable [LinearOrder W] [LinearOrder X]
variable {allowed : Fin (h+1) → Set X} {q : Fin (h+2) → ℕ}

namespace Core
variable {P : ContactTrainPicture L S base allowed q} {b : B} (C : P.Core b)
    (hne : Nonempty (P.projection.StripEdge b))

/-- The extra invariant is preserved by the *same* gluing that preserves
full bounds and supplies the colour-focusing step. A new nonempty future
strip has a nonempty old strip, by the product equivalence. -/
theorem next_hasFutureRefinements {g : ℕ} {done : List B}
    (hg : 2 ≤ g) (hg0 : g ≤ q 0)
    (hg1 : 0 < h → g ≤ q ⟨1,by omega⟩)
    (hbase : ∀ a c : B, a ≠ c → (base a ∩ base c).Subsingleton)
    (hq : ∀ μ, μ.val < h+1 → 2 ≤ q μ)
    (hP : P.FullBounds)
    (hC : C.graph.bottomCut.ZeroSmallMixedForestsThrough (q 0))
    (hsize : ∀ e, (C.graph.edgeCarrier e).Nontrivial)
    (H : HasFutureRefinements g P done) :
    HasFutureRefinements g (C.next hne hbase (fun μ _ hh => hq μ hh)) (b :: done) := by
  let A := C.gluing hne
  let ha := C.family.stripGluing_active hne
  let hc := C.family.stripGluing_coreOver hne C.part C.part_emb C.edge_image C.edge_inj
  let Q := C.next hne hbase (fun μ _ hh => hq μ hh)
  have hQ : Q.FullBounds := C.next_fullBounds hne hbase hq (by omega) hP hC hsize
  have hCg : C.graph.bottomCut.ZeroSmallMixedForestsThrough g :=
    C.graph.bottomCut.zeroSmallMixedForests_mono hC hg0
  have hpar : A.outputHypergraph.Parameters A.outputTrain
      (fun j => A.outputProjectionVertex P.projection C.part ⁻¹' allowed j) :=
    Q.parameters
  have hcoarse : LabelledGirthGT
      (A.outputHypergraph.atCut (A.outputTrain.parent ⟨1,by omega⟩)).contactWagonCarrier g := by
    by_cases hh : 0 < h
    · rintro ⟨Z,hZ⟩
      exact (hQ ⟨1,by omega⟩ (by change 1 < h+1; omega)).g3 ⟨Z,hZ.trans (hg1 hh)⟩
    · have he : (⟨1,by omega⟩ : Fin (h+1+1)) = ⟨h+1,by omega⟩ := Fin.ext (by omega)
      rw [he]
      exact A.outputHypergraph.top_wagonGirth A.outputTrain g
  intro c hcd hn
  have hcb : c ≠ b := fun he => hcd (List.mem_cons.mpr (Or.inl he))
  have hcold : c ∉ done := fun he => hcd (List.mem_cons.mpr (Or.inr he))
  let e := A.futureEdgeEquiv P.projection b c ha hcb
  have hnold : Nonempty (P.projection.StripEdge c) := by
    obtain ⟨x⟩ := hn
    exact ⟨(e.symm x).2⟩
  obtain ⟨R⟩ := H c hcold hnold
  exact ⟨A.advanceStripRefinement P.projection b c ha hcb C.part hc R hg hbase hCg hpar hcoarse⟩

end Core

/-- Main iteration at cutoff greater than two. The only remaining local
obligation is to construct the core from a single available refinement.
Preservation of the other refinements is no longer a supply assumption. -/
theorem main_with_refinements (P : ContactTrainPicture L S base allowed q)
    [Fintype B] {Color : Type v} [Nonempty Color] {g : ℕ}
    (hg : 2 ≤ g) (hg0 : g ≤ q 0)
    (hg1 : 0 < h → g ≤ q ⟨1,by omega⟩)
    (hbase : ∀ a c : B, a ≠ c → (base a ∩ base c).Subsingleton)
    (hq : ∀ μ, μ.val < h+1 → 2 ≤ q μ)
    (supply : ∀ (Q : ContactTrainPicture L S base allowed q) (b : B),
      Q.FullBounds → Nonempty (Q.projection.StripEdge b) →
      Q.projection.StripRefinement Q.train allowed g b →
      ∃ C : Q.Core b,
        C.graph.bottomCut.ZeroSmallMixedForestsThrough (q 0) ∧
        (∀ e, (C.graph.edgeCarrier e).Nontrivial) ∧ C.family.Arrow Color)
    (hP : P.FullBounds) (hInv : HasFutureRefinements g P [])
    (hArrow : ∀ ρ : B → Color, ∃ i : P.Copy, ∃ c : Color,
      ∀ e : F, ρ (P.projection.edge ((P.family.emb i).edge e)) = c) :
    ∃ Q : ContactTrainPicture L S base allowed q, Q.FullBounds ∧ Q.family.Arrow Color := by
  refine P.main_of_coreSupply (by omega) hbase hq (HasFutureRefinements g)
    ?_ ?_ hP hInv hArrow
  · intro Q done b hI
    exact hasFutureRefinements_skip hI
  · intro Q done b hQ hI hb hn
    obtain ⟨R⟩ := hI b hb hn
    obtain ⟨C,hC,hs,hA⟩ := supply Q b hQ hn R
    exact ⟨C,hC,hs,hA,C.next_hasFutureRefinements hn hg hg0 hg1 hbase hq hQ hC hs hI⟩

end ContactTrainPicture

namespace ContactSeed
variable {J : Type v} [LinearOrder V] [LinearOrder X]
variable (A : ContactSeed D base J)
variable (T : ContactTrainData E (h+1))
variable (allowed : Fin (h+1) → Set X) (q : Fin (h+2) → ℕ)

/-- Initialize every actual strip simultaneously: the seed edge map is
injective on each component, and different components are disjoint.
Consequently the empty first parameter suffices for depth one. -/
theorem initial_hasFutureRefinements [Finite V] [Finite E] [Finite J]
    (horder : ∀ j, StrictMono (A.vertex j))
    (hcovered : ∀ x, ∃ e, x ∈ D.edgeCarrier e)
    (hlin : ∀ μ, μ.val < h+1 → (D.atCut (T.parent μ)).ContactLinear)
    (hG : D.WagonBounds T q)
    (hpar : ∀ i : J, D.Parameters T (fun j => A.vertex i ⁻¹' allowed j))
    {g : ℕ} (hg : g ≤ q 0) :
    ContactTrainPicture.HasFutureRefinements g
      (A.initialPicture (T := T) (by omega : 0 < h+1) allowed q horder hcovered hlin hG hpar) [] := by
  let P := A.initialPicture (T := T) (by omega : 0 < h+1) allowed q horder hcovered hlin hG hpar
  have hP : P.FullBounds := A.initialPicture_fullBounds (T := T) (by omega : 0 < h+1)
    allowed q horder hcovered hlin hG hpar
  intro b _ _
  have hmatch : ∀ e f : P.projection.StripEdge b, e ≠ f →
      P.graph.edgeCarrier e.val ∩ P.graph.edgeCarrier f.val = ∅ := by
    rintro ⟨⟨i,e⟩,he⟩ ⟨⟨j,f⟩,hf⟩ hn
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    have hi : i = j := hx.1.1.symm.trans hx.2.1
    subst j
    change A.edge i e = b at he
    change A.edge i f = b at hf
    have hef : e = f := (A.edge i).injective (he.trans hf.symm)
    subst f
    exact hn rfl
  have hbottom : LabelledGirthGT (P.graph.atCut (P.train.parent 0)).contactWagonCarrier g := by
    rintro ⟨Z,hZ⟩
    exact (hP 0 (by omega)).g3 ⟨Z,hZ.trans hg⟩
  exact ⟨P.projection.matchingRefinement P.train allowed g b hmatch hbottom⟩

end ContactSeed
end StructuralRamsey.Girth
