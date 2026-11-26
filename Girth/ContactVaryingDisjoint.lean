import Girth.ContactPictureZero
import Girth.ContactShorterTrain

/-! Disjoint union of varying padded components. Unlike picture
zero the components need not have the same vertex type or edge
carrier map. Their edge label type and train equivalences agree.
Only their universal top wagon is identified. -/

namespace StructuralRamsey.Girth
universe v
variable {Q E I P : Type v} {V : Q → Type v}

def contactComponentEmb (i : Q) : V i ↪ Sigma V where
  toFun := Sigma.mk i
  inj' := by intro x y h; cases h; rfl

theorem contactComponentEmb_shared (i j : Q)
    {x : V i} {y : V j} (h : contactComponentEmb i x = contactComponentEmb j y) :
    i = j := congrArg Sigma.fst h

/-- A cycle in a disjoint union of varying carrier families
has a single component label, and its connectors project along
the injective vertex tag of that component. -/
theorem contact_disjoint_family_girth
    (K : (i : Q) → P → Set (V i)) {g : ℕ}
    (hg : ∀ i, LabelledGirthGT (K i) g) :
    LabelledGirthGT (fun p : Q × P => contactComponentEmb p.1 '' K p.1 p.2) g := by
  classical
  rintro ⟨C,hC⟩
  have hn : 0 < C.length := by have := C.hlength; omega
  let i₀ : Fin C.length := ⟨0,hn⟩
  let j := (C.label i₀).1
  have hl : ∀ i, (C.label i).1 = j := by
    apply contactCycle_all_of_zero hn (fun i => (C.label i).1 = j) rfl
    intro i hi
    obtain ⟨x,hx,hxe⟩ := C.left_mem i
    obtain ⟨y,hy,hye⟩ := C.right_mem i
    exact (contactComponentEmb_shared _ _ (hye.trans hxe.symm)).trans hi
  have hmem : ∀ i, C.vertex i ∈ contactComponentEmb j '' K j (C.label i).2 := by
    intro i
    have hx := C.left_mem i
    change C.vertex i ∈ contactComponentEmb (C.label i).1 '' K (C.label i).1 (C.label i).2 at hx
    rw [hl i] at hx
    exact hx
  choose z hz using hmem
  let B : LabelledBergeCycle (K j) := {
    length := C.length
    hlength := C.hlength
    label := fun i => (C.label i).2
    vertex := z
    label_injective := fun i k h => C.label_injective (Prod.ext ((hl i).trans (hl k).symm) h)
    vertex_injective := fun i k h =>
      C.vertex_injective ((hz i).2.symm.trans ((congrArg (contactComponentEmb j) h).trans (hz k).2))
    left_mem := fun i => (hz i).1
    right_mem := by
      intro i
      have hx := C.right_mem i
      change C.vertex i ∈ contactComponentEmb (C.label (cyclicSucc i)).1 ''
        K (C.label (cyclicSucc i)).1 (C.label (cyclicSucc i)).2 at hx
      rw [hl (cyclicSucc i)] at hx
      obtain ⟨w,hw,he⟩ := hx
      exact ((contactComponentEmb j).injective (he.trans (hz i).2.symm)) ▸ hw
  }
  exact hg j ⟨B,hC⟩

namespace ContactHypergraphData
variable (D : (i : Q) → ContactHypergraphData (V i) E I)

def varyingDisjoint : ContactHypergraphData (Sigma V) (Q × E) PEmpty.{v+1} where
  edgeCarrier := fun p => contactComponentEmb p.1 '' (D p.1).edgeCarrier p.2
  copyCarrier := PEmpty.elim
  copyEdges := PEmpty.elim

variable {m : ℕ} (T : ContactTrainData E m)

theorem varying_disjoint_carrier (hm : 0 < m)
    (μ : Fin (m+1)) (hproper : μ.val < m)
    (p : (T.disjointTrain Q hm).Wagon μ) :
    ((varyingDisjoint D).atCut ((T.disjointTrain Q hm).parent μ)).contactWagonCarrier p =
      contactComponentEmb (T.disjointWagonEquiv Q hm μ hproper p).1 ''
        ((D (T.disjointWagonEquiv Q hm μ hproper p).1).atCut (T.parent μ)).contactWagonCarrier
          (T.disjointWagonEquiv Q hm μ hproper p).2 := by
  obtain ⟨⟨i,e⟩,rfl⟩ := (T.disjointTrain Q hm).surj μ p
  rw [T.disjointWagonEquiv_parent]
  ext x
  constructor
  · rintro ⟨⟨j,f⟩,he,hx⟩
    have h := congrArg (T.disjointWagonEquiv Q hm μ hproper) he
    rw [T.disjointWagonEquiv_parent,T.disjointWagonEquiv_parent] at h
    have hj : j = i := congrArg Prod.fst h
    have hf : T.parent μ f = T.parent μ e := congrArg Prod.snd h
    subst j
    obtain ⟨y,hy,rfl⟩ := hx
    exact ⟨y,⟨f,hf,hy⟩,rfl⟩
  · rintro ⟨y,⟨f,hf,hy⟩,rfl⟩
    refine ⟨(i,f),?_,⟨y,hy,rfl⟩⟩
    apply (T.disjointWagonEquiv Q hm μ hproper).injective
    rw [T.disjointWagonEquiv_parent,T.disjointWagonEquiv_parent,hf]

theorem varying_disjoint_girth (hm : 0 < m)
    (μ : Fin (m+1)) (hproper : μ.val < m) {g : ℕ}
    (hg : ∀ i, LabelledGirthGT ((D i).atCut (T.parent μ)).contactWagonCarrier g) :
    LabelledGirthGT
      ((varyingDisjoint D).atCut ((T.disjointTrain Q hm).parent μ)).contactWagonCarrier g := by
  let e := T.disjointWagonEquiv Q hm μ hproper
  let K : Q × T.Wagon μ → Set (Sigma V) := fun p =>
    contactComponentEmb p.1 '' ((D p.1).atCut (T.parent μ)).contactWagonCarrier p.2
  have hK : LabelledGirthGT K g :=
    contact_disjoint_family_girth (fun i => ((D i).atCut (T.parent μ)).contactWagonCarrier) hg
  exact labelledGirthGT_of_injective_shrinking K _ e e.injective
    (fun p => by rw [varying_disjoint_carrier D T hm μ hproper]) g hK

/-- The complete positive/zero proper-cut vector transfers to
the common shorter train of the padded union. -/
theorem varying_disjoint_wagonBounds (hm : 0 < m)
    (q : Fin (m+1) → ℕ) (hg : ∀ i, (D i).WagonBounds T q) :
    (varyingDisjoint D).WagonBounds (T.disjointTrain Q hm) q :=
  fun μ hp => varying_disjoint_girth D T hm μ hp (fun i => hg i μ hp)

theorem varying_disjoint_linear
    (hlin : ∀ i, ∀ e f : E, e ≠ f →
      ((D i).edgeCarrier e ∩ (D i).edgeCarrier f).Subsingleton) :
    ∀ e f : Q × E, e ≠ f →
      ((varyingDisjoint D).edgeCarrier e ∩ (varyingDisjoint D).edgeCarrier f).Subsingleton := by
  rintro ⟨i,e⟩ ⟨j,f⟩ hne x hx y hy
  obtain ⟨u,hu,he⟩ := hx.1
  obtain ⟨w,hw,hf⟩ := hx.2
  have hij := contactComponentEmb_shared i j (he.trans hf.symm)
  subst j
  have hEq := (contactComponentEmb i).injective (he.trans hf.symm)
  subst w
  obtain ⟨u',hu',he'⟩ := hy.1
  obtain ⟨w',hw',hf'⟩ := hy.2
  have hEq' := (contactComponentEmb i).injective (he'.trans hf'.symm)
  subst w'
  exact he.symm.trans ((congrArg (contactComponentEmb i)
    (hlin i e f (fun h => hne (congrArg (Prod.mk i) h)) ⟨hu,hw⟩ ⟨hu',hw'⟩)).trans he')

/-- Parameters of the varying disjoint union are exactly the
component parameters, even at the universal top. -/
theorem varying_disjoint_parameters (hm : 0 < m)
    (allowed : (i : Q) → Fin m → Set (V i))
    (h : ∀ i, (D i).Parameters T (allowed i)) :
    (varyingDisjoint D).Parameters (T.disjointTrain Q hm)
      (fun k => {x | x.2 ∈ allowed x.1 k}) := by
  intro k e f x hpar hx hy hn
  rcases e with ⟨i,e⟩
  rcases f with ⟨j,f⟩
  obtain ⟨u,hu,he⟩ := hx
  obtain ⟨w,hw,hf⟩ := hy
  have hij := contactComponentEmb_shared i j (he.trans hf.symm)
  subst j
  have hEq := (contactComponentEmb i).injective (he.trans hf.symm)
  subst w
  have hco : T.parent k.succ e = T.parent k.succ f := by
    have hp := Quotient.exact hpar
    change k.succ.val = m ∨ i = i ∧ T.parent k.succ e = T.parent k.succ f at hp
    rcases hp with ht | ⟨_,ht⟩
    · have he : k.succ = (⟨m,by omega⟩ : Fin (m+1)) := Fin.ext ht
      rw [he]
      exact T.top _ _
    · exact ht
  have hn' : u ∉ allowed i k := by
    intro hu'
    apply hn
    rw [← he]
    exact hu'
  have hfine := h i k e f u hco hu hw hn'
  apply Quotient.sound
  exact Or.inr ⟨rfl,hfine⟩

end ContactHypergraphData
end StructuralRamsey.Girth
