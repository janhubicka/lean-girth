import Girth.ContactTrainData
import Girth.ContactWagonRelabel

/-! Picture zero at one proper cut: vertex-disjoint copies of one
train, with one designated copy per component. This establishes
G1--G4 from edge linearity and the wagon-girth bound of the input.
It does not assume any system-girth property of the input copies. -/

namespace StructuralRamsey.Girth
universe v
variable {V E I P J : Type v}

namespace ContactHypergraphData
variable (D : ContactHypergraphData V E I)

def disjointCopies (J : Type v) : ContactHypergraphData (J × V) (J × E) J where
  edgeCarrier := fun e => {x | x.1 = e.1 ∧ x.2 ∈ D.edgeCarrier e.2}
  copyCarrier := fun j => {x | x.1 = j}
  copyEdges := fun j => {e | e.1 = j}

def disjointCut (J : Type v) (p : E → P) :
    OrderOneData (J × V) (J × E) J (J × P) :=
  (D.disjointCopies J).atCut (fun e => (e.1,p e.2))

theorem disjoint_wagon_mem (p : E → P) (w : J × P) (x : J × V) :
    x ∈ (D.disjointCut J p).contactWagonCarrier w ↔
      x.1 = w.1 ∧ x.2 ∈ (D.atCut p).contactWagonCarrier w.2 := by
  constructor
  · rintro ⟨e,he,hx⟩
    have h₁ : e.1 = w.1 := congrArg Prod.fst he
    have h₂ : p e.2 = w.2 := congrArg Prod.snd he
    exact ⟨hx.1.trans h₁,e.2,h₂,hx.2⟩
  · rintro ⟨hx,e,he,hxe⟩
    exact ⟨(w.1,e),Prod.ext rfl he,⟨hx,hxe⟩⟩

def component (z : (J × V) ⊕ (J × P)) : J :=
  match z with
  | .inl x => x.1
  | .inr w => w.1

theorem disjoint_copy_mem (p : E → P) (hsurj : Function.Surjective p)
    (j : J) (z : (J × V) ⊕ (J × P)) :
    z ∈ (D.disjointCut J p).contactCopyClique j ↔ component z = j := by
  cases z with
  | inl x => rfl
  | inr w =>
    constructor
    · rintro ⟨e,he,hp⟩
      exact (congrArg Prod.fst hp).symm.trans he
    · intro hw
      obtain ⟨e,he⟩ := hsurj w.2
      exact ⟨(w.1,e),hw,Prod.ext rfl he⟩

theorem disjoint_wagon_component (p : E → P) (w : J × P)
    (z : (J × V) ⊕ (J × P))
    (h : z ∈ (D.disjointCut J p).contactWagonClique w) :
    component z = w.1 := by
  cases z with
  | inl x => exact ((D.disjoint_wagon_mem p w x).mp h).1
  | inr r => exact congrArg Prod.fst (show r = w from h)

theorem disjoint_adj_component (p : E → P) (hsurj : Function.Surjective p)
    {z t : (J × V) ⊕ (J × P)}
    (h : contactAdjacent (D.disjointCut J p).contactClique z t) :
    component z = component t := by
  obtain ⟨_,a,hz,ht⟩ := h
  cases a with
  | inl j =>
    exact ((D.disjoint_copy_mem p hsurj j z).mp hz).trans
      ((D.disjoint_copy_mem p hsurj j t).mp ht).symm
  | inr w =>
    exact (D.disjoint_wagon_component p w z hz).trans
      (D.disjoint_wagon_component p w t ht).symm

theorem disjoint_g1 (p : E → P) : (D.disjointCut J p).ContactG1 := by
  refine ⟨?_,?_,?_⟩
  · intro j e he x hx
    exact hx.1.trans he
  · intro j e hn
    obtain ⟨x,hx,_,_,_⟩ := hn
    exact hx.1.1.symm.trans hx.2
  · intro j w _ x hx hxp
    obtain ⟨e,he,hxe⟩ := hxp
    exact ⟨e,hxe.1.symm.trans hx,he,hxe⟩

theorem disjoint_g2 (p : E → P) (hsurj : Function.Surjective p) :
    (D.disjointCut J p).ContactG2 := by
  intro i j hij hn
  obtain ⟨z,hz,_,_,_⟩ := hn
  exact (hij (((D.disjoint_copy_mem p hsurj i z).mp hz.1).symm.trans
    ((D.disjoint_copy_mem p hsurj j z).mp hz.2))).elim

/-- Linearity lifts to the disjoint union without identifying
different labels. -/
theorem disjoint_linear (p : E → P) (h : (D.atCut p).ContactLinear) :
    (D.disjointCut J p).ContactLinear := by
  constructor
  · intro e f hef x hx y hy
    have hfirst : e.1 = f.1 := hx.1.1.symm.trans hx.2.1
    have hne : e.2 ≠ f.2 := fun he => hef (Prod.ext hfirst he)
    exact Prod.ext (hx.1.1.trans hy.1.1.symm)
      (h.1 e.2 f.2 hne ⟨hx.1.2,hx.2.2⟩ ⟨hy.1.2,hy.2.2⟩)
  · intro r s hrs x hx y hy
    have hx₁ := (D.disjoint_wagon_mem p r x).mp hx.1
    have hx₂ := (D.disjoint_wagon_mem p s x).mp hx.2
    have hy₁ := (D.disjoint_wagon_mem p r y).mp hy.1
    have hy₂ := (D.disjoint_wagon_mem p s y).mp hy.2
    have hfirst : r.1 = s.1 := hx₁.1.symm.trans hx₂.1
    have hne : r.2 ≠ s.2 := fun he => hrs (Prod.ext hfirst he)
    exact Prod.ext (hx₁.1.trans hy₁.1.symm)
      (h.2 r.2 s.2 hne ⟨hx₁.2,hx₂.2⟩ ⟨hy₁.2,hy₂.2⟩)

/-- Any labelled Berge cycle is entirely in one component, so it
projects to a genuine labelled cycle in the original cut. -/
theorem disjoint_g3 (p : E → P) {q : ℕ}
    (h : LabelledGirthGT (D.atCut p).contactWagonCarrier q) :
    LabelledGirthGT (D.disjointCut J p).contactWagonCarrier q := by
  rintro ⟨C,hq⟩
  have hn : 0 < C.length := by have := C.hlength; omega
  let k₀ : Fin C.length := ⟨0,hn⟩
  let j₀ := (C.label k₀).1
  have hl : ∀ k, (C.label k).1 = j₀ := by
    apply contactCycle_all_of_zero hn (fun k => (C.label k).1 = j₀) rfl
    intro k hk
    have hleft := (D.disjoint_wagon_mem p (C.label k) (C.vertex k)).mp (C.left_mem k)
    have hright := (D.disjoint_wagon_mem p (C.label (cyclicSucc k)) (C.vertex k)).mp (C.right_mem k)
    exact hright.1.symm.trans (hleft.1.trans hk)
  have hv : ∀ k, (C.vertex k).1 = j₀ :=
    fun k => ((D.disjoint_wagon_mem p (C.label k) (C.vertex k)).mp (C.left_mem k)).1.trans (hl k)
  let B : LabelledBergeCycle (D.atCut p).contactWagonCarrier := {
    length := C.length
    hlength := C.hlength
    label := fun k => (C.label k).2
    vertex := fun k => (C.vertex k).2
    label_injective := fun _ _ he =>
      C.label_injective (Prod.ext ((hl _).trans (hl _).symm) he)
    vertex_injective := fun _ _ he =>
      C.vertex_injective (Prod.ext ((hv _).trans (hv _).symm) he)
    left_mem := fun k => ((D.disjoint_wagon_mem p (C.label k) (C.vertex k)).mp (C.left_mem k)).2
    right_mem := fun k => ((D.disjoint_wagon_mem p (C.label (cyclicSucc k))
      (C.vertex k)).mp (C.right_mem k)).2
  }
  exact h ⟨B,hq⟩

/-- Every actual contact polygon is covered by its component copy.
This establishes G4 for every budget. -/
theorem disjoint_g4 (p : E → P) (hsurj : Function.Surjective p) (q : ℕ) :
    ContactG4 (D.disjointCut J p).contactClique q := by
  classical
  intro C hC _
  have hn : 0 < C.length := by have := C.hlength; omega
  let k₀ : Fin C.length := ⟨0,hn⟩
  let j := component (C.vertex k₀)
  have hcomp : ∀ k, component (C.vertex k) = j := by
    apply contactCycle_all_of_zero hn (fun k => component (C.vertex k) = j) rfl
    intro k hk
    exact (D.disjoint_adj_component p hsurj (hC k)).symm.trans hk
  have hcover : C.Covered (D.disjointCut J p).contactClique :=
    ⟨Sum.inl j,fun k => (D.disjoint_copy_mem p hsurj j (C.vertex k)).mpr (hcomp k)⟩
  exact ⟨fun _ => hcover,fun hn => C.covered_hasChord hn hcover⟩

theorem disjoint_systemGirth (p : E → P) (hsurj : Function.Surjective p) {q : ℕ}
    (hlin : (D.atCut p).ContactLinear)
    (hg : LabelledGirthGT (D.atCut p).contactWagonCarrier q) :
    (D.disjointCut J p).ContactSystemGirthGT q :=
  ⟨D.disjoint_linear p hlin,D.disjoint_g1 p,D.disjoint_g2 p hsurj,
    D.disjoint_g3 p hg,D.disjoint_g4 p hsurj q⟩

end ContactHypergraphData
end StructuralRamsey.Girth
