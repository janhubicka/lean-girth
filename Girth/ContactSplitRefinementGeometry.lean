import Girth.ContactSplitRefinement
import Girth.ContactSplitChildGirth
import Girth.ContactTrainPullback

/-! Geometry of the actual split refinement. The new edge type
is the product of standard labels and old strip-edge labels.
Carrier equalities, the retained parent maps, and the leaf
obstruction supply all wagon girth bounds and parameters. -/

namespace StructuralRamsey.Girth
universe v
variable {V U E I J Q : Type v}

namespace ContactTrainData
variable {m : ℕ} (T : ContactTrainData E m)

/-- The actual parent map between two cuts is well defined by
surjectivity of the finer parent and nesting. -/
noncomputable def parentMap (μ ν : Fin (m+1)) (_hle : μ ≤ ν)
    (p : T.Wagon μ) : T.Wagon ν :=
  T.parent ν (Classical.choose (T.surj μ p))

theorem parentMap_parent (μ ν : Fin (m+1)) (hle : μ ≤ ν) (e : E) :
    T.parentMap μ ν hle (T.parent μ e) = T.parent ν e :=
  T.nested μ ν hle _ e (Classical.choose_spec (T.surj μ (T.parent μ e)))

end ContactTrainData

namespace ContactHypergraphData
variable (D : ContactHypergraphData V E I)
variable {m : ℕ} (T : ContactTrainData E m)

theorem wagon_parent_subset (μ ν : Fin (m+1)) (hle : μ ≤ ν) (p : T.Wagon μ) :
    (D.atCut (T.parent μ)).contactWagonCarrier p ⊆
      (D.atCut (T.parent ν)).contactWagonCarrier (T.parentMap μ ν hle p) := by
  rintro x ⟨e,he,hx⟩
  refine ⟨e,?_,hx⟩
  rw [← he,T.parentMap_parent]

theorem top_wagonGirth (g : ℕ) :
    LabelledGirthGT (D.atCut (T.parent ⟨m,by omega⟩)).contactWagonCarrier g := by
  rintro ⟨C,_⟩
  let i : Fin C.length := ⟨0,by have := C.hlength; omega⟩
  obtain ⟨e,he⟩ := T.surj _ (C.label i)
  obtain ⟨f,hf⟩ := T.surj _ (C.label (cyclicSucc i))
  have heq := he.symm.trans ((T.top e f).trans hf)
  exact contactSucc_ne C.hlength i (C.label_injective heq).symm

end ContactHypergraphData

namespace ContactSplitRefinement
variable {d h : ℕ} (R : ContactSplitRefinement (E := E) (Q := Q) d h)
    (D : ContactHypergraphData V E I) (H : ContactHypergraphData U (Q × E) J)
    (emb : Q → V ↪ U)
    (hcarrier : ∀ i e, H.edgeCarrier (i,e) = emb i '' D.edgeCarrier e)

def firstRetained : Fin (d+1+h+1) := ⟨d+1,by omega⟩

def lastPrefix : Fin (d+1+h+1) := ⟨d,by omega⟩

theorem prefix_carrier (μ : Fin (d+1+h+1)) (hμ : μ.val ≤ d)
    (p : R.train.Wagon μ) :
    (H.atCut (R.train.parent μ)).contactWagonCarrier p =
      emb (R.prefixWagonEquiv μ hμ p).1 ''
        (D.atCut (R.old.parent (R.depthLevel μ hμ))).contactWagonCarrier
          (R.prefixWagonEquiv μ hμ p).2 := by
  classical
  obtain ⟨e,rfl⟩ := R.train.surj μ p
  rcases e with ⟨i,f⟩
  rw [R.prefixWagonEquiv_parent]
  ext x
  constructor
  · rintro ⟨⟨j,g⟩,he,hx⟩
    obtain ⟨hij,hfg⟩ := (R.prefix_eq μ hμ (j,g) (i,f)).mp he
    change j = i at hij
    subst j
    rw [hcarrier] at hx
    obtain ⟨y,hy,rfl⟩ := hx
    exact ⟨y,⟨g,hfg,hy⟩,rfl⟩
  · rintro ⟨y,⟨g,hg,hy⟩,rfl⟩
    refine ⟨(i,g),(R.prefix_eq μ hμ (i,g) (i,f)).mpr ⟨rfl,hg⟩,?_⟩
    rw [hcarrier]
    exact ⟨y,hy,rfl⟩

theorem tail_carrier (μ : Fin (d+1+h+1)) (hμ : d < μ.val)
    (p : R.train.Wagon μ) :
    (H.atCut (R.train.parent μ)).contactWagonCarrier p =
      (H.atCut (R.coarse.parent (R.tailLevel μ hμ))).contactWagonCarrier
        (R.tailWagonEquiv μ hμ p) := by
  obtain ⟨e,rfl⟩ := R.train.surj μ p
  rw [R.tailWagonEquiv_parent]
  ext x
  constructor
  · rintro ⟨f,hf,hx⟩
    exact ⟨f,(R.tail_eq μ hμ f e).mp hf,hx⟩
  · rintro ⟨f,hf,hx⟩
    exact ⟨f,(R.tail_eq μ hμ f e).mpr hf,hx⟩

theorem tail_girth (μ : Fin (d+1+h+1)) (hμ : d < μ.val) {g : ℕ}
    (hg : LabelledGirthGT
      (H.atCut (R.coarse.parent (R.tailLevel μ hμ))).contactWagonCarrier g) :
    LabelledGirthGT (H.atCut (R.train.parent μ)).contactWagonCarrier g :=
  labelledGirthGT_of_injective_shrinking _ _ (R.tailWagonEquiv μ hμ)
    (R.tailWagonEquiv μ hμ).injective
    (fun p => by rw [R.tail_carrier H μ hμ]) g hg

/-- The standard label of a prefix wagon. -/
noncomputable def standard (μ : Fin (d+1+h+1)) (hμ : μ.val ≤ d)
    (p : R.train.Wagon μ) : Q :=
  (R.prefixWagonEquiv μ hμ p).1

theorem standard_parent (μ ν : Fin (d+1+h+1)) (hle : μ ≤ ν)
    (hν : ν.val ≤ d) (hμ : μ.val ≤ d) (p : R.train.Wagon μ) :
    R.standard ν hν (R.train.parentMap μ ν hle p) = R.standard μ hμ p := by
  obtain ⟨e,rfl⟩ := R.train.surj μ p
  rw [R.train.parentMap_parent]
  unfold standard
  rw [R.prefixWagonEquiv_parent,R.prefixWagonEquiv_parent]

/-- Once a short cycle at a prefix cut is in a single parent at
the new split level, every wagon of the cycle lies in a single
standard. The old local refined bound excludes it. -/
theorem prefix_girth_of_lastPrefix (μ : Fin (d+1+h+1)) (hμ : μ.val < d) {g : ℕ}
    (hg : LabelledGirthGT
      (D.atCut (R.old.parent (R.depthLevel μ hμ.le))).contactWagonCarrier g)
    (hParent : LabelledGirthGT
      (H.atCut (R.train.parent ⟨d,by omega⟩)).contactWagonCarrier g) :
    LabelledGirthGT (H.atCut (R.train.parent μ)).contactWagonCarrier g := by
  classical
  let ν : Fin (d+1+h+1) := ⟨d,by omega⟩
  have hle : μ ≤ ν := hμ.le
  let F := (H.atCut (R.train.parent μ)).contactWagonCarrier
  let K := (H.atCut (R.train.parent ν)).contactWagonCarrier
  let p := R.train.parentMap μ ν hle
  apply contact_girth_of_parent F K p (H.wagon_parent_subset R.train μ ν hle) hParent
  intro C hC hc
  let i₀ : Fin C.length := ⟨0,by have := C.hlength; omega⟩
  let j := R.standard μ hμ.le (C.label i₀)
  have hs : ∀ i, R.standard μ hμ.le (C.label i) = j := by
    intro i
    rw [← R.standard_parent μ ν hle (by exact le_rfl) hμ.le,
      ← R.standard_parent μ ν hle (by exact le_rfl) hμ.le]
    exact congrArg (R.standard ν (by exact le_rfl)) (hc i i₀)
  let lab : Fin C.length → R.old.Wagon (R.depthLevel μ hμ.le) :=
    fun i => (R.prefixWagonEquiv μ hμ.le (C.label i)).2
  have hlabel : Function.Injective lab := by
    intro i k he
    apply C.label_injective
    apply (R.prefixWagonEquiv μ hμ.le).injective
    exact Prod.ext ((hs i).trans (hs k).symm) he
  have hmem : ∀ i, C.vertex i ∈ emb j ''
      (D.atCut (R.old.parent (R.depthLevel μ hμ.le))).contactWagonCarrier (lab i) := by
    intro i
    have hx := C.left_mem i
    change C.vertex i ∈ (H.atCut (R.train.parent μ)).contactWagonCarrier (C.label i) at hx
    rw [R.prefix_carrier D H emb hcarrier μ hμ.le] at hx
    change C.vertex i ∈ emb (R.standard μ hμ.le (C.label i)) ''
      (D.atCut (R.old.parent (R.depthLevel μ hμ.le))).contactWagonCarrier (lab i) at hx
    rw [hs i] at hx
    exact hx
  choose z hz using hmem
  let B : LabelledBergeCycle (D.atCut (R.old.parent (R.depthLevel μ hμ.le))).contactWagonCarrier := {
    length := C.length
    hlength := C.hlength
    label := lab
    vertex := z
    label_injective := hlabel
    vertex_injective := fun i k he =>
      C.vertex_injective ((hz i).2.symm.trans ((congrArg (emb j) he).trans (hz k).2))
    left_mem := fun i => (hz i).1
    right_mem := by
      intro i
      have hx := C.right_mem i
      change C.vertex i ∈ (H.atCut (R.train.parent μ)).contactWagonCarrier (C.label (cyclicSucc i)) at hx
      rw [R.prefix_carrier D H emb hcarrier μ hμ.le] at hx
      change C.vertex i ∈ emb (R.standard μ hμ.le (C.label (cyclicSucc i))) ''
        (D.atCut (R.old.parent (R.depthLevel μ hμ.le))).contactWagonCarrier (lab (cyclicSucc i)) at hx
      rw [hs (cyclicSucc i)] at hx
      obtain ⟨x,hx,he⟩ := hx
      exact ((emb j).injective (he.trans (hz i).2.symm)) ▸ hx
  }
  exact hg ⟨B,hC⟩

/-- Distinct new children in a common retained first wagon
have distinct standard labels by exact restriction. -/
theorem split_standard_injective (p r : R.train.Wagon ⟨d,by omega⟩)
    (hparent : R.train.parentMap ⟨d,by omega⟩ ⟨d+1,by omega⟩
      (by change d ≤ d+1; omega) p =
      R.train.parentMap ⟨d,by omega⟩ ⟨d+1,by omega⟩
        (by change d ≤ d+1; omega) r)
    (hstandard : R.standard ⟨d,by omega⟩ le_rfl p =
      R.standard ⟨d,by omega⟩ le_rfl r) : p = r := by
  obtain ⟨⟨i,e⟩,rfl⟩ := R.train.surj _ p
  obtain ⟨⟨j,f⟩,rfl⟩ := R.train.surj _ r
  unfold standard at hstandard
  rw [R.prefixWagonEquiv_parent,R.prefixWagonEquiv_parent] at hstandard
  change i = j at hstandard
  subst j
  rw [R.train.parentMap_parent,R.train.parentMap_parent] at hparent
  have hc := (R.tail_eq ⟨d+1,by omega⟩ (by change d < d+1; omega) (i,e) (i,f)).mp hparent
  have hlevel : R.tailLevel ⟨d+1,by omega⟩ (by change d < d+1; omega) =
      (⟨1,by omega⟩ : Fin (h+1+1)) := by
    apply Fin.ext
    change d+1-d = 1
    omega
  rw [hlevel] at hc
  exact (R.prefix_eq ⟨d,by omega⟩ le_rfl (i,e) (i,f)).mpr
    ⟨rfl,(R.boundary i e f).mpr hc⟩

end ContactSplitRefinement
end StructuralRamsey.Girth
