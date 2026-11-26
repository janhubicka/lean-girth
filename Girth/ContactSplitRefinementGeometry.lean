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

include hcarrier in
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

include hcarrier

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

omit hcarrier

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


/-- Every pair of edges from different standards meets, if at all,
inside the corresponding core copies in the permitted overlap of
the two base edges. This is supplied by the actual tagged picture. -/
def CrossTrace (_R : ContactSplitRefinement (E := E) (Q := Q) d h) (coreCopy : Q → Set U) (crossAllowed : Set U) : Prop :=
  ∀ i j, i ≠ j → ∀ e f,
    H.edgeCarrier (i,e) ∩ H.edgeCarrier (j,f) ⊆
      coreCopy i ∩ coreCopy j ∩ crossAllowed

/-- The new children of the retained first wagon have girth >g:
their switch vertices lie in the core-copy intersection and the
new allowed part. The selected core join tree rules out the cycle. -/
theorem lastPrefix_girth (coreCopy : Q → Set U) (crossAllowed firstAllowed : Set U)
    {g : ℕ} (hg : LabelledGirthGT
      (H.atCut (R.coarse.parent ⟨1,by omega⟩)).contactWagonCarrier g)
    (hparam : H.Parameter R.coarse ⟨0,by omega⟩ ⟨1,by omega⟩ firstAllowed)
    (hcross : R.CrossTrace H coreCopy crossAllowed)
    (hforest : ∀ s : Finset Q, s.Nonempty → s.card ≤ g →
      Nonempty (ContactJoinTree (fun i : {i // i ∈ s} => coreCopy i.val)))
    (hinter : ∀ i j, i ≠ j → (coreCopy i ∩ coreCopy j ∩ crossAllowed).Subsingleton) :
    LabelledGirthGT (H.atCut (R.train.parent ⟨d,by omega⟩)).contactWagonCarrier g := by
  classical
  let μ : Fin (d+1+h+1) := ⟨d,by omega⟩
  let ν : Fin (d+1+h+1) := ⟨d+1,by omega⟩
  have hle : μ ≤ ν := by change d ≤ d+1; omega
  have hν : d < ν.val := by change d < d+1; omega
  have hlev : R.tailLevel ν hν = (⟨1,by omega⟩ : Fin (h+1+1)) := by
    apply Fin.ext
    change d+1-d = 1
    omega
  have hg' := R.tail_girth H ν hν (by rw [hlev]; exact hg)
  let F := (H.atCut (R.train.parent μ)).contactWagonCarrier
  let K := (H.atCut (R.train.parent ν)).contactWagonCarrier
  let parent := R.train.parentMap μ ν hle
  let std := R.standard μ (by exact le_rfl)
  apply contact_split_child_girth F K parent std coreCopy (crossAllowed ∩ firstAllowed)
    hg' (H.wagon_parent_subset R.train μ ν hle)
  · exact R.split_standard_injective
  · intro p r hne hpr x hx
    obtain ⟨⟨i,e⟩,he,hxe⟩ := hx.1
    obtain ⟨⟨j,f⟩,hf,hxf⟩ := hx.2
    have hsi : std p = i := by
      rw [← he]
      exact congrArg Prod.fst (R.prefixWagonEquiv_parent μ (by exact le_rfl) (i,e))
    have hsj : std r = j := by
      rw [← hf]
      exact congrArg Prod.fst (R.prefixWagonEquiv_parent μ (by exact le_rfl) (j,f))
    have hij : i ≠ j := by
      intro heq
      apply hne
      exact R.split_standard_injective p r hpr (hsi.trans (heq.trans hsj.symm))
    have hp : R.train.parent ν (i,e) = R.train.parent ν (j,f) := by
      rw [← R.train.parentMap_parent μ ν hle,← R.train.parentMap_parent μ ν hle,he,hf]
      exact hpr
    have hp' := (R.tail_eq ν hν (i,e) (j,f)).mp hp
    rw [hlev] at hp'
    have hxfirst : x ∈ firstAllowed := by
      by_contra hn
      have heq := R.coarse.bottom (hparam (i,e) (j,f) x hp' hxe hxf hn)
      exact hij (congrArg Prod.fst heq)
    have h := hcross i j hij e f ⟨hxe,hxf⟩
    change x ∈ coreCopy (std p) ∩ coreCopy (std r) ∩ (crossAllowed ∩ firstAllowed)
    rw [hsi,hsj]
    exact ⟨h.1,h.2,hxfirst⟩
  · exact hforest
  · intro i j hne x hx y hy
    exact hinter i j hne ⟨hx.1,hx.2.1⟩ ⟨hy.1,hy.2.1⟩

/-- The same cross-trace calculation proves the new parameter
between the split level and the retained first level. -/
theorem split_parameter (coreCopy : Q → Set U) (crossAllowed firstAllowed : Set U)
    (hparam : H.Parameter R.coarse ⟨0,by omega⟩ ⟨1,by omega⟩ firstAllowed)
    (hcross : R.CrossTrace H coreCopy crossAllowed) :
    H.Parameter R.train ⟨d,by omega⟩ ⟨d+1,by omega⟩
      (crossAllowed ∩ firstAllowed) := by
  rintro ⟨i,e⟩ ⟨j,f⟩ x hp hx hy hn
  have hco := (R.tail_eq ⟨d+1,by omega⟩ (by change d < d+1; omega) (i,e) (j,f)).mp hp
  have hlev : R.tailLevel ⟨d+1,by omega⟩ (by change d < d+1; omega) =
      (⟨1,by omega⟩ : Fin (h+1+1)) := by
    apply Fin.ext
    change d+1-d = 1
    omega
  rw [hlev] at hco
  by_cases hij : i = j
  · subst j
    exact (R.prefix_eq ⟨d,by omega⟩ le_rfl (i,e) (i,f)).mpr
      ⟨rfl,(R.boundary i e f).mpr hco⟩
  · have hxCross := (hcross i j hij e f ⟨hx,hy⟩).2
    have hxFirst : x ∈ firstAllowed := by
      by_contra h
      exact hij (congrArg Prod.fst (R.coarse.bottom (hparam _ _ x hco hx hy h)))
    exact (hn ⟨hxCross,hxFirst⟩).elim

include hcarrier in
theorem prefix_parameter (μ ν : Fin (d+1+h+1))
    (hν : ν.val ≤ d) (hμ : μ.val ≤ d)
    (allowed : Set U)
    (hpar : ∀ i : Q, D.Parameter R.old (R.depthLevel μ hμ) (R.depthLevel ν hν)
      (emb i ⁻¹' allowed)) :
    H.Parameter R.train μ ν allowed := by
  rintro ⟨i,e⟩ ⟨j,f⟩ x hp hx hy hn
  obtain ⟨hij,hp'⟩ := (R.prefix_eq ν hν (i,e) (j,f)).mp hp
  change i = j at hij
  subst j
  rw [hcarrier] at hx hy
  obtain ⟨y,hyE,he⟩ := hx
  obtain ⟨z,hzF,hf⟩ := hy
  have hEq := (emb i).injective (he.trans hf.symm)
  subst z
  exact (R.prefix_eq μ hμ (i,e) (i,f)).mpr
    ⟨rfl,hpar i e f y hp' hyE hzF (fun h => hn (he ▸ h))⟩

theorem tail_parameter (μ ν : Fin (d+1+h+1))
    (hμ : d < μ.val) (hν : d < ν.val) (allowed : Set U)
    (hp : H.Parameter R.coarse (R.tailLevel μ hμ) (R.tailLevel ν hν) allowed) :
    H.Parameter R.train μ ν allowed := by
  intro e f x he hx hy hn
  exact (R.tail_eq μ hμ e f).mpr (hp e f x ((R.tail_eq ν hν e f).mp he) hx hy hn)


/-- Combine the prefix and retained tail bounds on the very same
new train. The cutoff at a retained proper level is unchanged. -/
def newBounds (g : ℕ) (q : Fin (h+1+1) → ℕ) (μ : Fin (d+1+h+1)) : ℕ :=
  if hm : μ.val ≤ d then g else q (R.tailLevel μ (by omega))

theorem all_wagonBounds (g : ℕ) (q : Fin (h+1+1) → ℕ)
    (hprefix : ∀ μ : Fin (d+1+h+1), μ.val ≤ d →
      LabelledGirthGT (H.atCut (R.train.parent μ)).contactWagonCarrier g)
    (htail : H.WagonBounds R.coarse q) :
    H.WagonBounds R.train (R.newBounds g q) := by
  intro μ hproper
  by_cases hμ : μ.val ≤ d
  · simpa only [newBounds,dif_pos hμ] using hprefix μ hμ
  · have hh : d < μ.val := by omega
    have hp : (R.tailLevel μ hh).val < h+1 := by
      change μ.val-d < h+1
      omega
    have hg := R.tail_girth H μ hh (htail _ hp)
    simpa only [newBounds,dif_neg hμ] using hg

/-- The parameters of the new train: retain the old refined
parameters up to d, insert the one-part intersection parameter,
and retain the remaining coarse parameters after it. -/
theorem all_parameters (allowed : Fin (d+1+h) → Set U)
    (hprefix : ∀ j : Fin (d+1+h), j.val < d →
      H.Parameter R.train j.castSucc j.succ (allowed j))
    (hsplit : H.Parameter R.train ⟨d,by omega⟩ ⟨d+1,by omega⟩
      (allowed ⟨d,by omega⟩))
    (htail : ∀ j : Fin (d+1+h), d < j.val →
      H.Parameter R.train j.castSucc j.succ (allowed j)) :
    H.Parameters R.train allowed := by
  intro j
  by_cases hlt : j.val < d
  · exact hprefix j hlt
  · by_cases he : j.val = d
    · have hj : j = (⟨d,by omega⟩ : Fin (d+1+h)) := Fin.ext he
      rw [hj]
      exact hsplit
    · exact htail j (by omega)

end ContactSplitRefinement
end StructuralRamsey.Girth
