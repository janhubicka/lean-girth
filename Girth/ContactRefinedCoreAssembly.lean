import Girth.ContactForestBoostClass

/-! Assemble the refined recursive core in the main induction.
The forest-boost class has bottom budget q, not the smaller prefix
budget g. Only the positive inserted cuts use g. After forest boost,
forget the inserted cuts, keeping actual edges, copy labels, order,
and the entire mixed-forest conclusion unchanged. -/

namespace StructuralRamsey.Girth
universe v
variable {V E I X B : Type v} {h : ℕ}
variable {D : ContactHypergraphData V E I} {base : B → Set X}

namespace ContactBaseProjection.StripRefinement
variable {P : ContactBaseProjection D base} {T : ContactTrainData E (h+1)}
variable {allowed : Fin (h+1) → Set X} {g : ℕ} {b : B}
variable (R : P.StripRefinement T allowed g b)

/-- Restrict the ambient allowed sets to the actual part type of
this strip. The first d entries are singleton or empty. -/
def boostAllowed (j : Fin (R.depth+h)) : Set (base b) :=
  Subtype.val ⁻¹' R.allAllowed j

/-- The class-wide forest boost aims at the original bottom budget.
Its positive bounds, and hence the recursive rank, are precisely
those of the refined tail. -/
def boostBounds (q : Fin (h+2) → ℕ) (μ : Fin (R.depth+h+1)) : ℕ :=
  if μ.val = 0 then q 0 else R.allBounds q μ

theorem boostBounds_zero (q : Fin (h+2) → ℕ) : R.boostBounds q 0 = q 0 := by
  simp [boostBounds]

theorem boostBounds_two (q : Fin (h+2) → ℕ) (hg : 2 ≤ g)
    (hq : ∀ μ, μ.val < h+1 → 2 ≤ q μ) :
    ∀ μ, μ.val < R.depth+h → 2 ≤ R.boostBounds q μ := by
  intro μ hproper
  have hval := μ.isLt
  by_cases hz : μ.val = 0
  · rw [boostBounds,if_pos hz]
    exact hq 0 (by change (0 : ℕ) < h+1; omega)
  · rw [boostBounds,if_neg hz]
    by_cases hp : μ.val < R.depth
    · simpa only [allBounds,if_pos hp] using hg
    · let k : Fin (h+2) := ⟨μ.val-R.depth+1,by have := μ.isLt; omega⟩
      have hk : k.val < h+1 := by change μ.val-R.depth+1 < h+1; omega
      simpa only [allBounds,if_neg hp] using hq k hk

/-- The class-wide girth conclusion is proved for EVERY possible
input in the refined class, not just the original active strip.
This is the essential premise of the class-wide forest boost. -/
theorem boostClass_girth [LinearOrder X] (q : Fin (h+2) → ℕ)
    (hk : q 0 ≤ 2*g+1) (hfirst : 0 < h → q 0 ≤ q ⟨1,by omega⟩)
    (A : ContactBoostInput (base b) (R.depth+h) R.boostAllowed (R.boostBounds q)) :
    LabelledGirthGT A.graph.edgeCarrier (R.boostBounds q 0) := by
  rw [R.boostBounds_zero]
  have hd := R.depth_pos
  apply A.graph.refined_edge_girth A.train R.depth g (q 0) hd (by omega) hk
    A.endpoints.part R.boostAllowed
  · intro j hj x hx y hy
    apply Subtype.ext
    have hx' : x.val ∈ R.prefixAllowed ⟨j.val,hj⟩ := by
      change x.val ∈ R.allAllowed j at hx
      simpa only [allAllowed,dif_pos hj] using hx
    have hy' : y.val ∈ R.prefixAllowed ⟨j.val,hj⟩ := by
      change y.val ∈ R.allAllowed j at hy
      simpa only [allAllowed,dif_pos hj] using hy
    exact R.singleton _ hx' hy'
  · intro e x hx y hy he
    exact (A.endpoints.endpoint_of_mem e x hx).symm.trans
      ((congrArg (A.endpoints.endpoint e) he).trans (A.endpoints.endpoint_of_mem e y hy))
  · exact A.parameters
  · intro μ hp ht
    have hz : μ.val ≠ 0 := by omega
    have hg := A.positiveWagons μ hp (by omega)
    simpa only [boostBounds,if_neg hz,allBounds,if_pos ht] using hg
  · intro ht
    let μ : Fin (R.depth+h+1) := ⟨R.depth,by omega⟩
    have hp : 0 < μ.val := hd
    have hz : μ.val ≠ 0 := by omega
    have hn : ¬ μ.val < R.depth := by change ¬ R.depth < R.depth; omega
    have he : (⟨μ.val-R.depth+1,by have := μ.isLt; omega⟩ : Fin (h+2)) = ⟨1,by omega⟩ := by
      apply Fin.ext
      change R.depth-R.depth+1 = 1
      omega
    have hg := A.positiveWagons μ hp ht
    have hb : R.boostBounds q μ = q ⟨1,by omega⟩ := by
      rw [boostBounds,if_neg hz,allBounds,if_neg hn,he]
    rw [hb] at hg
    rintro ⟨C,hC⟩
    exact hg ⟨C,hC.trans (hfirst (by omega))⟩

/-- The retained cut map preserves the actual coarse equivalence
relation on the active strip, including bottom equality. -/
abbrev retainMap := contactRetainRefinement R.depth h R.depth_pos

theorem retainMap_strict : StrictMono R.retainMap :=
  contactRetainRefinement_strict R.depth h R.depth_pos

theorem retainMap_zero : R.retainMap 0 = 0 :=
  contactRetainRefinement_zero R.depth h R.depth_pos

theorem retainMap_top : R.retainMap ⟨h+1,by omega⟩ = ⟨R.depth+h,by omega⟩ :=
  contactRetainRefinement_top R.depth h R.depth_pos

noncomputable abbrev restoredTrain :=
  R.train.retainLevels R.retainMap R.retainMap_strict.monotone R.retainMap_zero R.retainMap_top

theorem restored_rel (μ : Fin (h+2)) (e f : P.StripEdge b) :
    R.restoredTrain.parent μ e = R.restoredTrain.parent μ f ↔
      (P.stripTrain T b).parent μ e = (P.stripTrain T b).parent μ f := by
  by_cases hz : μ.val = 0
  · have he : μ = 0 := Fin.ext (by simpa using hz)
    subst μ
    constructor
    · intro h
      exact congrArg ((P.stripTrain T b).parent 0) (R.restoredTrain.bottom h)
    · intro h
      exact congrArg (R.restoredTrain.parent 0) ((P.stripTrain T b).bottom h)
  · change R.train.parent (R.retainMap μ) e = R.train.parent (R.retainMap μ) f ↔ _
    have he : R.retainMap μ = ⟨μ.val+R.depth-1,by have := μ.isLt; omega⟩ := by
      simp only [retainMap,contactRetainRefinement,dif_neg hz]
    rw [he]
    exact (R.retained μ (by omega) e f).trans
      (T.pullTrain_rel (P.stripEdgeEmb b) μ e f).symm

/-- No additional parameter appears when the refined levels are
forgotten. All prefix parameters are contained in the original
first parameter, while a positive tail interval is unchanged. -/
theorem retainAllowed_subset (j : Fin (h+1)) (k : Fin (R.depth+h))
    (h₀ : (R.retainMap j.castSucc).val ≤ k.val)
    (h₁ : k.val < (R.retainMap j.succ).val) : R.allAllowed k ⊆ allowed j := by
  have hd := R.depth_pos
  have hj := j.isLt
  have hs : (R.retainMap j.succ).val = j.val+R.depth := by
    change (contactRetainRefinement R.depth h R.depth_pos j.succ).val = _
    simp only [contactRetainRefinement,dif_neg (by change j.val+1 ≠ 0; omega)]
    change j.val+1+R.depth-1 = j.val+R.depth
    omega
  rw [hs] at h₁
  by_cases hz : j.val = 0
  · have hk : k.val < R.depth := by omega
    have he : j = 0 := Fin.ext (by simpa using hz)
    rw [allAllowed,dif_pos hk,he]
    exact R.subset_first _
  · have hc : (R.retainMap j.castSucc).val = j.val+R.depth-1 := by
      change (contactRetainRefinement R.depth h R.depth_pos j.castSucc).val = _
      simp only [contactRetainRefinement,dif_neg (show j.castSucc.val ≠ 0 from hz)]
      rfl
    rw [hc] at h₀
    have hk : ¬ k.val < R.depth := by omega
    have he : (⟨k.val-R.depth+1,by have := k.isLt; omega⟩ : Fin (h+1)) = j := by
      apply Fin.ext
      change k.val-R.depth+1 = j.val
      omega
    rw [allAllowed,dif_neg hk,he]

/-- Restore the full original parameter vector on an arbitrary
witness over the refined input, not merely the input itself. -/
theorem restore_parameters {U F J : Type v} (H : ContactHypergraphData U F J)
    (S : ContactTrainData F (R.depth+h)) (part : U → X)
    (hp : H.Parameters S (fun j => part ⁻¹' R.allAllowed j)) :
    H.Parameters (S.retainLevels R.retainMap R.retainMap_strict.monotone
      R.retainMap_zero R.retainMap_top) (fun j => part ⁻¹' allowed j) :=
  H.retain_parameters S R.retainMap R.retainMap_strict R.retainMap_zero R.retainMap_top
    _ _ hp (fun j k h₀ h₁ => Set.preimage_mono (R.retainAllowed_subset j k h₀ h₁))

/-- At every retained positive cut, the refined boost budget is
exactly the original positive system-girth budget. -/
theorem retainBounds_eq (q : Fin (h+2) → ℕ) (μ : Fin (h+2)) (hp : 0 < μ.val) :
    R.boostBounds q (R.retainMap μ) = q μ := by
  have hd := R.depth_pos
  have he : (R.retainMap μ).val = μ.val+R.depth-1 := by
    simp only [retainMap,contactRetainRefinement,dif_neg (by omega : μ.val ≠ 0)]
  have hzero : (R.retainMap μ).val ≠ 0 := by omega
  have hpre : ¬ (R.retainMap μ).val < R.depth := by omega
  have hi : (⟨(R.retainMap μ).val-R.depth+1,
      by have := (R.retainMap μ).isLt; omega⟩ : Fin (h+2)) = μ := by
    apply Fin.ext
    change (R.retainMap μ).val-R.depth+1 = μ.val
    omega
  rw [boostBounds,if_neg hzero,allBounds,if_neg hpre,hi]

theorem restore_positive {U F J : Type v} (H : ContactHypergraphData U F J)
    (S : ContactTrainData F (R.depth+h)) (q : Fin (h+2) → ℕ)
    (hp : H.PositiveBounds S (R.boostBounds q)) :
    H.PositiveBounds (S.retainLevels R.retainMap R.retainMap_strict.monotone
      R.retainMap_zero R.retainMap_top) q := by
  intro μ hpos ht
  have he : (R.retainMap μ).val = μ.val+R.depth-1 := by
    simp only [retainMap,contactRetainRefinement,dif_neg (by omega : μ.val ≠ 0)]
  have hd := R.depth_pos
  have h := hp (R.retainMap μ) (by omega) (by omega)
  rw [R.retainBounds_eq q μ hpos] at h
  exact h

end ContactBaseProjection.StripRefinement

namespace ContactDesignatedEmbeddings
variable {U F J : Type v} {m : ℕ}
variable {H : ContactHypergraphData U F J}
variable {T T' : ContactTrainData E m} {S : ContactTrainData F m}

/-- An equality of cut equivalence relations, rather than of chosen
wagon label types, is enough to change the source train. -/
def changeSourceTrain (M : ContactDesignatedEmbeddings D T H S)
    (hrel : ∀ μ e f, T.parent μ e = T.parent μ f ↔ T'.parent μ e = T'.parent μ f) :
    ContactDesignatedEmbeddings D T' H S where
  emb := fun j => {
    vertex := (M.emb j).vertex
    edge := (M.emb j).edge
    carrier_eq := (M.emb j).carrier_eq
    rel_iff := fun μ e f => ((M.emb j).rel_iff μ e f).trans (hrel μ e f)
    strong := (M.emb j).strong }
  vertex_eq := M.vertex_eq
  edge_eq := M.edge_eq

end ContactDesignatedEmbeddings

namespace ContactTrainPicture
variable {T : ContactTrainData E (h+1)}
variable [LinearOrder V] [LinearOrder X]
variable {allowed : Fin (h+1) → Set X} {q : Fin (h+2) → ℕ}
variable (Q : ContactTrainPicture D T base allowed q) (b : B)
variable {g : ℕ} (R : Q.projection.StripRefinement Q.train allowed g b)

/-- The actual refined active strip belongs to the fixed refined
class. The only omitted cut bound is the bottom one, which follows
uniformly from the class-wide girth theorem. -/
noncomputable def refinedBoostInput (hne : Nonempty (Q.projection.StripEdge b)) :
    ContactBoostInput (base b) (R.depth+h) R.boostAllowed (R.boostBounds q) := by
  letI : Finite Q.Vertex := Q.finiteV
  letI : Finite Q.Edge := Q.finiteE
  letI : LinearOrder Q.Vertex := Q.order
  refine {
    Vertex := Q.projection.StripVertex b
    Edge := Q.projection.StripEdge b
    Copy := PEmpty.{v+1}
    finiteV := inferInstance
    finiteE := inferInstance
    nonemptyE := hne
    graph := Q.projection.stripHypergraph b
    train := R.train
    endpoints := Q.projection.stripEndpoints b
    order := inferInstance
    part_mono := ?_
    linear := Q.projection.strip_linear b Q.linear
    parameters := R.all_parameters Q.parameters
    positiveWagons := ?_ }
  · intro x y hh
    change Q.projection.vertex x.val ≤ Q.projection.vertex y.val
    have hh' : x.val ≤ y.val := hh
    rcases lt_or_eq_of_le hh' with hlt | he
    · exact Q.projection_order x.val y.val hlt
    · rw [he]
  · intro μ hp ht
    have hg := R.all_wagonBounds q Q.positive μ ht
    simpa only [ContactBaseProjection.StripRefinement.boostBounds,if_neg (by omega : μ.val ≠ 0)] using hg

/-- Forget the inserted levels on the actual forest-boosted witness.
The designated labels and the edge and vertex maps do not change. -/
noncomputable def restoreCore (hne : Nonempty (Q.projection.StripEdge b))
    {Color : Type v} (W : (Q.refinedBoostInput b R hne).Witness Color) : Q.Core b := by
  let S := W.out.train.retainLevels R.retainMap R.retainMap_strict.monotone R.retainMap_zero R.retainMap_top
  let M := (W.family.retainLevels R.retainMap R.retainMap_strict.monotone
    R.retainMap_zero R.retainMap_top).changeSourceTrain R.restored_rel
  let part : W.out.Vertex → X := fun x => (W.out.endpoints.part x).val
  refine {
    Vertex := W.out.Vertex
    Edge := W.out.Edge
    Copy := W.out.Copy
    finiteV := W.out.finiteV
    finiteE := W.out.finiteE
    finiteC := W.finiteC
    graph := W.out.graph
    train := S
    family := M
    part := part
    part_emb := ?_
    edge_image := ?_
    edge_inj := ?_
    order := W.out.order
    copy_order := W.emb_order
    linear := W.out.linear
    covered := W.out.endpoints.covered
    parameters := R.restore_parameters W.out.graph W.out.train part W.out.parameters
    positive := R.restore_positive W.out.graph W.out.train q W.positive }
  · intro i x
    exact congrArg Subtype.val (W.emb_part i x)
  · intro e
    ext x
    constructor
    · rintro ⟨y,_,rfl⟩
      exact (W.out.endpoints.part y).property
    · intro hx
      refine ⟨W.out.endpoints.endpoint e ⟨x,hx⟩,W.out.endpoints.endpoint_mem e _,?_⟩
      exact congrArg Subtype.val (W.out.endpoints.part_endpoint e ⟨x,hx⟩)
  · intro e x hx y hy he
    have hpart : W.out.endpoints.part x = W.out.endpoints.part y := Subtype.ext he
    exact (W.out.endpoints.endpoint_of_mem e x hx).symm.trans
      ((congrArg (W.out.endpoints.endpoint e) hpart).trans (W.out.endpoints.endpoint_of_mem e y hy))

/-- The main q>2 local core obligation is reduced exactly to the
cutoff-two base supply for the smaller positive vector. The class-wide
girth and boost hypotheses are discharged here. -/
theorem refinedCore_of_cutoffTwo {Color : Type v} [Finite Color] [Nonempty Color]
    (hne : Nonempty (Q.projection.StripEdge b))
    (hg : 2 ≤ g) (hq : ∀ μ, μ.val < h+1 → 2 ≤ q μ)
    (hk : q 0 ≤ 2*g+1) (hfirst : 0 < h → q 0 ≤ q ⟨1,by omega⟩)
    (hsize : (base b).Nontrivial)
    (supply : ∀ A : ContactBoostInput (base b) (R.depth+h) R.boostAllowed (R.boostBounds q),
      Nonempty (A.Witness Color)) :
    ∃ C : Q.Core b, C.graph.bottomCut.ZeroSmallMixedForestsThrough (q 0) ∧
      (∀ e, (C.graph.edgeCarrier e).Nontrivial) ∧ C.family.Arrow Color := by
  classical
  letI : Finite Q.Vertex := Q.finiteV
  let EP := Q.projection.stripEndpoints b
  letI : Finite (base b) := Finite.of_injective
    (EP.endpoint (Classical.choice hne)) (EP.endpoint_inj _)
  have hd := R.depth_pos
  have hq0 := hq 0 (by change (0 : ℕ) < h+1; omega)
  have hbudget : q 0-1+1 = q 0 := by omega
  obtain ⟨W,hW⟩ := ContactBoostInput.forestBoost
    (P := base b) (Color := Color) (m := R.depth+h)
    (allowed := R.boostAllowed) (q := R.boostBounds q)
    (by omega) (R.boostBounds_two q hg hq) (R.boostClass_girth q hk hfirst)
    supply (q 0-1) (by rw [R.boostBounds_zero,hbudget]) (Q.refinedBoostInput b R hne)
  rw [hbudget] at hW
  let C := Q.restoreCore b R hne W
  refine ⟨C,hW,?_,W.arrow⟩
  intro e
  obtain ⟨x,hx,y,hy,hxy⟩ := hsize
  rw [← C.edge_image e] at hx hy
  obtain ⟨u,hu,he⟩ := hx
  obtain ⟨w,hw,hf⟩ := hy
  exact ⟨u,hu,w,hw,fun h => hxy (he.symm.trans ((congrArg C.part h).trans hf))⟩


section Coarse

/-- The cutoff-two case requires no inserted single-part levels.
Its active strip is already an admissible member of the fixed class. -/
noncomputable def coarseBoostInput (hne : Nonempty (Q.projection.StripEdge b)) :
    ContactBoostInput (base b) (h+1) (fun j => Subtype.val ⁻¹' allowed j) q := by
  letI : Finite Q.Vertex := Q.finiteV
  letI : Finite Q.Edge := Q.finiteE
  letI : LinearOrder Q.Vertex := Q.order
  refine {
    Vertex := Q.projection.StripVertex b
    Edge := Q.projection.StripEdge b
    Copy := PEmpty.{v+1}
    finiteV := inferInstance
    finiteE := inferInstance
    nonemptyE := hne
    graph := Q.projection.stripHypergraph b
    train := Q.projection.stripTrain Q.train b
    endpoints := Q.projection.stripEndpoints b
    order := inferInstance
    part_mono := ?_
    linear := Q.projection.strip_linear b Q.linear
    parameters := ?_
    positiveWagons := fun μ hp ht => Q.strip_positive_wagonBounds b μ hp ht }
  · intro x y hh
    change Q.projection.vertex x.val ≤ Q.projection.vertex y.val
    have hh' : x.val ≤ y.val := hh
    rcases lt_or_eq_of_le hh' with hlt | he
    · exact Q.projection_order x.val y.val hlt
    · rw [he]
  · intro j
    exact Q.projection.strip_parameter Q.train b j.castSucc j.succ
      (Q.projection.vertex ⁻¹' allowed j) (Q.parameters j)

noncomputable def coarseCore (hne : Nonempty (Q.projection.StripEdge b))
    {Color : Type v} (W : (Q.coarseBoostInput b hne).Witness Color) : Q.Core b := by
  let L : Q.LocalWitness b (Equiv.refl (base b)) := {
    Vertex := W.out.Vertex
    Edge := W.out.Edge
    Copy := W.out.Copy
    finiteV := W.out.finiteV
    finiteE := W.out.finiteE
    finiteC := W.finiteC
    graph := W.out.graph
    train := W.out.train
    family := W.family
    endpoints := W.out.endpoints
    emb_part := W.emb_part
    order := W.out.order
    emb_order := W.emb_order
    linear := W.out.linear
    positive := W.positive }
  exact L.toCore (fun j => Subtype.val ⁻¹' allowed j) (fun _ _ => Iff.rfl) W.out.parameters

/-- The nontriviality needed by bottom preservation follows from
projection onto a base edge of size at least two. -/
theorem Core.nontrivial_of_base (C : Q.Core b) (hsize : (base b).Nontrivial) :
    ∀ e, (C.graph.edgeCarrier e).Nontrivial := by
  intro e
  obtain ⟨x,hx,y,hy,hxy⟩ := hsize
  rw [← C.edge_image e] at hx hy
  obtain ⟨u,hu,he⟩ := hx
  obtain ⟨w,hw,hf⟩ := hy
  exact ⟨u,hu,w,hw,fun h => hxy (he.symm.trans ((congrArg C.part h).trans hf))⟩

/-- At cutoff two, linearity supplies the whole class-wide girth
hypothesis, and the same forest boost supplies the local core. -/
theorem coarseCore_of_cutoffTwo {Color : Type v} [Finite Color] [Nonempty Color]
    (hne : Nonempty (Q.projection.StripEdge b))
    (hq : ∀ μ, μ.val < h+1 → 2 ≤ q μ) (hzero : q 0 = 2)
    (hsize : (base b).Nontrivial)
    (supply : ∀ A : ContactBoostInput (base b) (h+1)
      (fun j => Subtype.val ⁻¹' allowed j) q, Nonempty (A.Witness Color)) :
    ∃ C : Q.Core b, C.graph.bottomCut.ZeroSmallMixedForestsThrough (q 0) ∧
      (∀ e, (C.graph.edgeCarrier e).Nontrivial) ∧ C.family.Arrow Color := by
  classical
  letI : Finite Q.Vertex := Q.finiteV
  let EP := Q.projection.stripEndpoints b
  letI : Finite (base b) := Finite.of_injective
    (EP.endpoint (Classical.choice hne)) (EP.endpoint_inj _)
  have hG (A : ContactBoostInput (base b) (h+1)
      (fun j => Subtype.val ⁻¹' allowed j) q) : LabelledGirthGT A.graph.edgeCarrier (q 0) := by
    rw [hzero]
    exact contactLabelledGirthGT_two_of_pairwiseSubsingleton _ A.linear
  obtain ⟨W,hW⟩ := ContactBoostInput.forestBoost
    (P := base b) (Color := Color) (m := h+1)
    (allowed := fun j => Subtype.val ⁻¹' allowed j) (q := q)
    (by omega) hq hG supply 1 (by rw [hzero]) (Q.coarseBoostInput b hne)
  let C := Q.coarseCore b hne W
  refine ⟨C,?_,C.nontrivial_of_base hsize,W.arrow⟩
  rw [hzero]
  exact hW

end Coarse

end ContactTrainPicture
end StructuralRamsey.Girth
