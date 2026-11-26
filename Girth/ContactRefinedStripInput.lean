import Girth.ContactStripRefinement

/-! Candidate continuation: prepare the input of the recursive call from
an actual maintained strip refinement. The ambient vertex representation is
used only for maintaining the refinement; its recursive input is precisely the
edge-covered strip. No extra tail bounds or parameters are assumed. -/

namespace StructuralRamsey.Girth
universe v
variable {V E I X B : Type v} {h : ℕ}
variable {D : ContactHypergraphData V E I} {base : B → Set X}

namespace ContactBaseProjection.StripRefinement
variable {P : ContactBaseProjection D base} {T : ContactTrainData E (h+1)}
    {allowed : Fin (h+1) → Set X} {g : ℕ} {b : B}
    (R : P.StripRefinement T allowed g b)

/-- Complete the prefix parameter vector by the actual coarse tail. -/
def allAllowed (j : Fin (R.depth+h)) : Set X :=
  if hj : j.val < R.depth then R.prefixAllowed ⟨j.val,hj⟩
  else allowed ⟨j.val-R.depth+1,by have := j.isLt; omega⟩

/-- The bottom entry is g; the first retained positive cut is at depth.
The value at the universal top is irrelevant. -/
def allBounds (q : Fin (h+2) → ℕ) (μ : Fin (R.depth+h+1)) : ℕ :=
  if μ.val < R.depth then g
  else q ⟨μ.val-R.depth+1,by have := μ.isLt; omega⟩

/-- The maintained equivalences give a well-defined injection of the
refined wagon labels at every retained positive cut into the coarse
wagon labels. In particular this does not identify equal carriers. -/
noncomputable def retainedWagon (μ : Fin (h+2)) (hμ : 0 < μ.val) :
    R.train.Wagon ⟨μ.val+R.depth-1,by have := μ.isLt; omega⟩ → T.Wagon μ :=
  fun p => T.parent μ (Classical.choose (R.train.surj _ p)).val

 theorem retainedWagon_parent (μ : Fin (h+2)) (hμ : 0 < μ.val)
    (e : P.StripEdge b) :
    R.retainedWagon μ hμ (R.train.parent ⟨μ.val+R.depth-1,by have := μ.isLt; omega⟩ e) =
      T.parent μ e.val := by
  exact (R.retained μ hμ _ e).mp (Classical.choose_spec (R.train.surj _ _))

 theorem retainedWagon_injective (μ : Fin (h+2)) (hμ : 0 < μ.val) :
    Function.Injective (R.retainedWagon μ hμ) := by
  intro p p' hp
  obtain ⟨e,rfl⟩ := R.train.surj _ p
  obtain ⟨f,rfl⟩ := R.train.surj _ p'
  rw [R.retainedWagon_parent,R.retainedWagon_parent] at hp
  exact (R.retained μ hμ e f).mpr hp

/-- A refined wagon at a retained level has its actual vertices in the
corresponding coarse wagon. The strip vertex subtype is essential here. -/
theorem retainedWagon_subset (μ : Fin (h+2)) (hμ : 0 < μ.val)
    (p : R.train.Wagon ⟨μ.val+R.depth-1,by have := μ.isLt; omega⟩) :
    P.stripVertexEmb b '' ((P.stripHypergraph b).atCut
      (R.train.parent ⟨μ.val+R.depth-1,by have := μ.isLt; omega⟩)).contactWagonCarrier p ⊆
      (D.atCut (T.parent μ)).contactWagonCarrier (R.retainedWagon μ hμ p) := by
  rintro x ⟨y,⟨e,he,hy⟩,rfl⟩
  exact ⟨e.val,(R.retainedWagon_parent μ hμ e).symm.trans (congrArg (R.retainedWagon μ hμ) he),hy⟩

/-- Pull back girth at a retained positive cut, with injection on both
labels and actual vertices. -/
theorem retained_girth (μ : Fin (h+2)) (hμ : 0 < μ.val) {k : ℕ}
    (hg : LabelledGirthGT (D.atCut (T.parent μ)).contactWagonCarrier k) :
    LabelledGirthGT ((P.stripHypergraph b).atCut
      (R.train.parent ⟨μ.val+R.depth-1,by have := μ.isLt; omega⟩)).contactWagonCarrier k := by
  rintro ⟨C,hC⟩
  let K : LabelledBergeCycle (D.atCut (T.parent μ)).contactWagonCarrier := {
    length := C.length
    hlength := C.hlength
    label := fun i => R.retainedWagon μ hμ (C.label i)
    vertex := fun i => (C.vertex i).val
    label_injective := fun i j he => C.label_injective (R.retainedWagon_injective μ hμ he)
    vertex_injective := fun i j he => C.vertex_injective (Subtype.ext he)
    left_mem := fun i => R.retainedWagon_subset μ hμ (C.label i) ⟨C.vertex i,C.left_mem i,rfl⟩
    right_mem := fun i => R.retainedWagon_subset μ hμ (C.label (cyclicSucc i))
      ⟨C.vertex i,C.right_mem i,rfl⟩ }
  exact hg ⟨K,hC⟩

/-- The maintained ambient prefix girth implies girth on the covered
vertex subtype, with exactly the same edge and wagon labels. -/
theorem covered_prefix_girth (μ : Fin (R.depth+h+1)) (hμ : μ.val < R.depth) :
    LabelledGirthGT ((P.stripHypergraph b).atCut (R.train.parent μ)).contactWagonCarrier g := by
  rintro ⟨C,hC⟩
  let H := D.pullEdges (P.stripEdgeEmb b)
  have hmem (p : R.train.Wagon μ) (x : P.StripVertex b)
      (hx : x ∈ ((P.stripHypergraph b).atCut (R.train.parent μ)).contactWagonCarrier p) :
      x.val ∈ (H.atCut (R.train.parent μ)).contactWagonCarrier p := by
    obtain ⟨e,he,hxe⟩ := hx
    exact ⟨e,he,hxe⟩
  let K : LabelledBergeCycle (H.atCut (R.train.parent μ)).contactWagonCarrier := {
    length := C.length
    hlength := C.hlength
    label := C.label
    vertex := fun i => (C.vertex i).val
    label_injective := C.label_injective
    vertex_injective := fun i j he => C.vertex_injective (Subtype.ext he)
    left_mem := fun i => hmem _ _ (C.left_mem i)
    right_mem := fun i => hmem _ _ (C.right_mem i) }
  exact R.prefix_girth μ hμ ⟨K,hC⟩

/-- Complete all parameters, using the retained equivalence relation at
both ends of each tail interval and the actual original parameter. -/
theorem all_parameters (hp : D.Parameters T (fun j => P.vertex ⁻¹' allowed j)) :
    (P.stripHypergraph b).Parameters R.train (fun j => P.stripPart b ⁻¹' R.allAllowed j) := by
  intro j e f x he hx hy hn
  change P.vertex x.val ∉ R.allAllowed j at hn
  by_cases hj : j.val < R.depth
  · have hn' : P.vertex x.val ∉ R.prefixAllowed ⟨j.val,hj⟩ := by
      simpa only [allAllowed,dif_pos hj] using hn
    exact R.prefix_parameters ⟨j.val,hj⟩ e f x.val he hx hy hn'
  · have hd := R.depth_pos
    have hj' := j.isLt
    let k : Fin (h+1) := ⟨j.val-R.depth+1,by omega⟩
    have h0 : 0 < k.castSucc.val := by change 0 < j.val-R.depth+1; omega
    have h1 : 0 < k.succ.val := by change 0 < j.val-R.depth+1+1; omega
    have e0 : (⟨k.castSucc.val+R.depth-1,by have := k.castSucc.isLt; omega⟩ : Fin (R.depth+h+1)) = j.castSucc := Fin.ext (by
      change j.val-R.depth+1+R.depth-1 = j.val
      omega)
    have e1 : (⟨k.succ.val+R.depth-1,by have := k.succ.isLt; omega⟩ : Fin (R.depth+h+1)) = j.succ := Fin.ext (by
      change j.val-R.depth+1+1+R.depth-1 = j.val+1
      omega)
    have r0 := R.retained k.castSucc h0 e f
    have r1 := R.retained k.succ h1 e f
    rw [e0] at r0
    rw [e1] at r1
    have hn' : P.vertex x.val ∉ allowed k := by
      simpa only [allAllowed,dif_neg hj] using hn
    exact r0.mpr (hp k e.val f.val x.val (r1.mp he) hx hy hn')

/-- The coarse positive system bounds supply every missing retained
wagon bound. The finer bounds below depth are already in the invariant. -/
theorem all_wagonBounds (q : Fin (h+2) → ℕ)
    (hp : D.PositiveBounds T q) :
    (P.stripHypergraph b).WagonBounds R.train (R.allBounds q) := by
  intro μ hproper
  by_cases hμ : μ.val < R.depth
  · simpa only [allBounds,if_pos hμ] using R.covered_prefix_girth μ hμ
  · have hd := R.depth_pos
    have hval := μ.isLt
    let k : Fin (h+2) := ⟨μ.val-R.depth+1,by omega⟩
    have hk : 0 < k.val := by change 0 < μ.val-R.depth+1; omega
    have hkt : k.val < h+1 := by change μ.val-R.depth+1 < h+1; omega
    have he : (⟨k.val+R.depth-1,by have := k.isLt; omega⟩ : Fin (R.depth+h+1)) = μ := Fin.ext (by
      change μ.val-R.depth+1+R.depth-1 = μ.val
      omega)
    have hg := R.retained_girth k hk (hp k hk hkt).g3
    rw [he] at hg
    simpa only [allBounds,if_neg hμ] using hg

/-- The local input has the required short-cycle exclusion. This is a
consequence of the maintained invariant and current coarse positive
bounds, rather than a hypothesis on a separately chosen refinement. -/
include R in
theorem edge_girth (q : Fin (h+2) → ℕ) (k : ℕ)
    (hk : k ≤ 2*g+1) (hfirst : 0 < h → k ≤ q ⟨1,by omega⟩)
    (hp : D.Parameters T (fun j => P.vertex ⁻¹' allowed j))
    (hb : D.PositiveBounds T q) :
    LabelledGirthGT (P.stripHypergraph b).edgeCarrier k := by
  have hd := R.depth_pos
  apply (P.stripHypergraph b).refined_edge_girth R.train R.depth g k hd (by omega) hk
      (P.stripPart b) R.allAllowed
  · intro j hj
    simpa only [allAllowed,dif_pos hj] using R.singleton ⟨j.val,hj⟩
  · exact P.strip_part_inj b
  · exact R.all_parameters hp
  · intro μ _ hμ
    exact R.covered_prefix_girth μ hμ
  · intro hh
    have hpos : 0 < h := by omega
    have hg : LabelledGirthGT (D.atCut (T.parent ⟨1,by omega⟩)).contactWagonCarrier k := by
      rintro ⟨C,hC⟩
      exact (hb ⟨1,by omega⟩ (by change (0 : ℕ) < 1; omega) (by change 1 < h+1; omega)).g3 ⟨C,hC.trans (hfirst hpos)⟩
    have hret := R.retained_girth ⟨1,by omega⟩ (by change (0 : ℕ) < 1; omega) hg
    have he : (⟨1+R.depth-1,by omega⟩ : Fin (R.depth+h+1)) = ⟨R.depth,by omega⟩ := Fin.ext (by change 1+R.depth-1 = R.depth; omega)
    rw [he] at hret
    exact hret

end ContactBaseProjection.StripRefinement
end StructuralRamsey.Girth
