import Girth.ContactJoinTreeCharacterization
import Girth.LabelledBergeCore
import Mathlib.Data.Fin.VecNotation

/-! Join trees of small families of traces. Each trace is empty, a
singleton, or one actual edge of a high-girth hypergraph. Repeated
trace sets remain distinct labels. This is the marked-edge family
needed both in the injective-owner case of the forest increment
and when constructing a tree of incident edge separators. -/

namespace StructuralRamsey.Girth
universe v
variable {V E J : Type v}

/-- The trace condition remembers an actual ambient edge label. -/
def ContactEdgeTraces (edge : E → Set V) (F : J → Set V) : Prop :=
  ∀ j, (F j).Subsingleton ∨ ∃ e, F j = edge e

/-- A real polygon in the selected trace graph with no covered
triangle and no chord gives a short actual labelled Berge cycle.
The edge labels and the side owners are both proved injective. -/
theorem contact_trace_no_bad [Fintype J]
    (edge : E → Set V) (F : J → Set V) (ht : ContactEdgeTraces edge F)
    {q : ℕ} (hcard : Fintype.card J ≤ q) (hg : LabelledGirthGT edge q)
    (B : ContactPolygon V PUnit.{v+1})
    (hb : B.Bad (fun j => {z | ∃ x ∈ F j, z = Sum.inl x})) : False := by
  classical
  let K : J → Set (V ⊕ PUnit.{v+1}) := fun j => {z | ∃ x ∈ F j, z = Sum.inl x}
  have hreal : ∀ k, ∃ x : V, B.vertex k = Sum.inl x := by
    intro k
    obtain ⟨_,a,hk,_⟩ := hb.1 k
    obtain ⟨x,_,he⟩ := hk
    exact ⟨x,he⟩
  choose x hx using hreal
  have hInj : Function.Injective x := by
    intro i j he
    exact B.vertex_injective ((hx i).trans ((congrArg Sum.inl he).trans (hx j).symm))
  have hown : ∀ i, ∃ j, x i ∈ F j ∧ x (cyclicSucc i) ∈ F j := by
    intro i
    obtain ⟨_,j,hi,hs⟩ := hb.1 i
    obtain ⟨u,hu,he⟩ := hi
    obtain ⟨w,hw,hf⟩ := hs
    exact ⟨j, (Sum.inl.inj ((hx i).symm.trans he)).symm ▸ hu,
      (Sum.inl.inj ((hx (cyclicSucc i)).symm.trans hf)).symm ▸ hw⟩
  choose own ho using hown
  have h2 : 2 ≤ B.length := by have := B.hlength; omega
  have no_third : ∀ i j, j ≠ i → j ≠ cyclicSucc i → x j ∉ F (own i) := by
    intro i j hji hjs hj
    exact B.bad_no_three hb (own i)
      (fun he => contactSucc_ne h2 i he.symm)
      (fun he => hji he.symm) (fun he => hjs he.symm)
      ⟨x i,(ho i).1,hx i⟩
      ⟨x (cyclicSucc i),(ho i).2,hx (cyclicSucc i)⟩
      ⟨x j,hj,hx j⟩
  have he : ∀ i, ∃ e, F (own i) = edge e := by
    intro i
    rcases ht (own i) with hsub | h
    · exact (contactSucc_ne h2 i (hInj (hsub (ho i).1 (ho i).2)).symm).elim
    · exact h
  choose ed hed using he
  have distinct_of_same_trace : ∀ i j : Fin B.length, F (own i) = F (own j) → i = j := by
    intro i j he
    by_contra hne
    have hj : x j ∈ F (own i) := by rw [he]; exact (ho j).1
    have hs : j = cyclicSucc i := by
      by_contra hh
      exact no_third i j (fun eq => hne eq.symm) hh hj
    have hj' : x (cyclicSucc j) ∈ F (own i) := by rw [he]; exact (ho j).2
    have hneq : cyclicSucc j ≠ i := by
      rw [hs]
      exact contactSucc_sq_ne B.hlength i
    have hneq' : cyclicSucc j ≠ cyclicSucc i := fun eq =>
      hne ((ContactCyclicRestriction.contactCyclicSucc_injective eq).symm)
    exact no_third i (cyclicSucc j) hneq hneq' hj'
  have ownInj : Function.Injective own := fun i j he =>
    distinct_of_same_trace i j (congrArg F he)
  have edInj : Function.Injective ed := by
    intro i j he
    apply distinct_of_same_trace i j
    rw [hed i,hed j,he]
  have hbudget : B.length ≤ q := by
    have h := Fintype.card_le_of_injective own ownInj
    rw [Fintype.card_fin] at h
    exact h.trans hcard
  let C : LabelledBergeCycle edge := {
    length := B.length
    hlength := h2
    label := ed
    vertex := fun i => x (cyclicSucc i)
    label_injective := edInj
    vertex_injective := hInj.comp ContactCyclicRestriction.contactCyclicSucc_injective
    left_mem := by
      intro i
      rw [← hed i]
      exact (ho i).2
    right_mem := by
      intro i
      rw [← hed (cyclicSucc i)]
      exact (ho (cyclicSucc i)).1
  }
  exact hg ⟨C,hbudget⟩

/-- The trace graph is chordal, and all its triangles are covered,
regardless of the lengths of candidate polygon obstructions. -/
theorem contact_trace_g4 [Fintype J]
    (edge : E → Set V) (F : J → Set V) (ht : ContactEdgeTraces edge F)
    {q : ℕ} (hcard : Fintype.card J ≤ q) (hg : LabelledGirthGT edge q)
    (r : ℕ) :
    ContactG4 (fun j => {z : V ⊕ PUnit.{v+1} | ∃ x ∈ F j, z = Sum.inl x}) r := by
  apply contactG4_of_no_bad
  intro B _ hb
  exact contact_trace_no_bad edge F ht hcard hg B hb

private theorem contact_trace_real_adj (F : J → Set V) (x y : V) :
    contactAdjacent (fun j => {z : V ⊕ PUnit.{v+1} | ∃ w ∈ F j, z = Sum.inl w})
        (Sum.inl x) (Sum.inl y) ↔ (contactFamilyGraph F).Adj x y := by
  constructor
  · rintro ⟨hne,j,⟨u,hu,he⟩,⟨w,hw,hf⟩⟩
    exact ⟨fun eq => hne (congrArg Sum.inl eq),j,
      (Sum.inl.inj he).symm ▸ hu,(Sum.inl.inj hf).symm ▸ hw⟩
  · rintro ⟨hne,j,hx,hy⟩
    exact ⟨fun he => hne (Sum.inl.inj he),j,⟨x,hx,rfl⟩,⟨y,hy,rfl⟩⟩

theorem contact_trace_chordal [Fintype J]
    (edge : E → Set V) (F : J → Set V) (ht : ContactEdgeTraces edge F)
    {q : ℕ} (hcard : Fintype.card J ≤ q) (hg : LabelledGirthGT edge q) :
    ContactChordal (contactFamilyGraph F) := by
  intro n z hn hInj hside
  let K : J → Set (V ⊕ PUnit.{v+1}) := fun j => {z | ∃ x ∈ F j, z = Sum.inl x}
  let C : ContactPolygon V PUnit.{v+1} := {
    length := n
    hlength := by omega
    vertex := fun i => Sum.inl (z i)
    vertex_injective := fun _ _ he => hInj (Sum.inl.inj he)
  }
  have hc : C.IsCycle K := fun i => (contact_trace_real_adj F _ _).mpr (hside i)
  have hw : C.twiceWeight ≤ 2*n := by
    simp [ContactPolygon.twiceWeight,C,contactWeight,contactKind,
      twiceOccurrenceWeight,Nat.mul_comm]
  obtain ⟨i,j,hnc,hadj⟩ := ((contact_trace_g4 edge F ht hcard hg n) C hc hw).2 hn
  exact ⟨i,j,hnc.1,hnc.2.1,hnc.2.2,(contact_trace_real_adj F _ _).mp hadj⟩

theorem contact_trace_conformal [Fintype J]
    (edge : E → Set V) (F : J → Set V) (ht : ContactEdgeTraces edge F)
    (hlin : ∀ e f : E, e ≠ f → (edge e ∩ edge f).Subsingleton)
    {q : ℕ} (hcard : Fintype.card J ≤ q) (hg : LabelledGirthGT edge q) :
    ContactConformal F := by
  classical
  intro s hne hsingle hpair
  obtain ⟨x,hx⟩ := hne
  by_cases hsub : (↑s : Set V).Subsingleton
  · obtain ⟨j,hj⟩ := hsingle x hx
    refine ⟨j,?_⟩
    intro y hy
    have he : y = x := hsub hy hx
    simpa only [he] using hj
  obtain ⟨x,hx,y,hy,hxy⟩ := Set.not_subsingleton_iff.mp hsub
  obtain ⟨j,hxj,hyj⟩ := hpair x hx y hy hxy
  obtain ⟨e,he⟩ : ∃ e, F j = edge e := by
    rcases ht j with h | h
    · exact (hxy (h hxj hyj)).elim
    · exact h
  refine ⟨j,?_⟩
  intro z hz
  by_contra hnot
  have hzx : z ≠ x := fun h => hnot (h.symm ▸ hxj)
  have hzy : z ≠ y := fun h => hnot (h.symm ▸ hyj)
  let C : ContactPolygon V PUnit.{v+1} := {
    length := 3
    hlength := by omega
    vertex := ![Sum.inl x,Sum.inl y,Sum.inl z]
    vertex_injective := by
      intro a b hab
      fin_cases a <;> fin_cases b <;> simp_all
  }
  let K : J → Set (V ⊕ PUnit.{v+1}) := fun j => {z | ∃ x ∈ F j, z = Sum.inl x}
  have hc : C.IsCycle K := by
    intro i
    fin_cases i
    · exact (contact_trace_real_adj F x y).mpr ⟨hxy,hpair x hx y hy hxy⟩
    · exact (contact_trace_real_adj F y z).mpr ⟨(fun he => hzy he.symm),hpair y hy z hz (fun he => hzy he.symm)⟩
    · exact (contact_trace_real_adj F z x).mpr ⟨hzx,hpair z hz x hx hzx⟩
  have hw : C.twiceWeight ≤ 2*3 := by
    simp [ContactPolygon.twiceWeight,C,Fin.sum_univ_succ,cyclicSucc,
      contactWeight,contactKind,twiceOccurrenceWeight]
  obtain ⟨a,ha⟩ := ((contact_trace_g4 edge F ht hcard hg 3) C hc hw).1 rfl
  have hmem (i : Fin 3) (u : V) (hu : C.vertex i = Sum.inl u) : u ∈ F a := by
    obtain ⟨w,hw,hw'⟩ := ha i
    exact (Sum.inl.inj (hu.symm.trans hw')).symm ▸ hw
  have hxa := hmem 0 x rfl
  have hya := hmem 1 y rfl
  have hza := hmem 2 z rfl
  obtain ⟨f,hf⟩ : ∃ f, F a = edge f := by
    rcases ht a with h | h
    · exact (hxy (h hxa hya)).elim
    · exact h
  have hef : e = f := by
    by_contra hh
    apply hxy
    apply hlin e f hh
    · exact ⟨he ▸ hxj,hf ▸ hxa⟩
    · exact ⟨he ▸ hyj,hf ▸ hya⟩
  apply hnot
  rw [he,hef,← hf]
  exact hza

/-- Construct the join tree on the ACTUAL trace labels, including
duplicates and empty traces. This is the high-girth trace family
lemma needed for direct forest increment. -/
theorem contact_trace_joinTree [Fintype V] [Fintype J] [Nonempty J]
    (edge : E → Set V) (F : J → Set V) (ht : ContactEdgeTraces edge F)
    (hlin : ∀ e f : E, e ≠ f → (edge e ∩ edge f).Subsingleton)
    {q : ℕ} (hcard : Fintype.card J ≤ q) (hg : LabelledGirthGT edge q) :
    Nonempty (ContactJoinTree F) :=
  contact_joinTree_of_chordal_conformal F
    (contact_trace_chordal edge F ht hcard hg)
    (contact_trace_conformal edge F ht hlin hcard hg)

end StructuralRamsey.Girth
