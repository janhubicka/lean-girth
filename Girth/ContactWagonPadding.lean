import Girth.ContactCanonicalFilling
import Girth.ContactSplitRefinementGeometry

/-! Padding first wagons to a fixed template in the cutoff-two
construction. Each padded wagon has its own private template
positions. Different padded wagons meet only at their old shared
vertices. Consequently padding higher wagon carriers introduces
no new Berge connectors between distinct labels. -/

namespace StructuralRamsey.Girth
universe v
variable {V P X J : Type v}

structure ContactWagonPadding (K : P → Set V) (X : Type v) where
  inside : (p : P) → K p ↪ X

namespace ContactWagonPadding
variable {K : P → Set V} (A : ContactWagonPadding K X)

abbrev Vertex := V ⊕ (Σ p : P, {x : X // x ∉ Set.range (A.inside p)})

def oldVertex : V ↪ A.Vertex := ⟨Sum.inl,Sum.inl_injective⟩

noncomputable def placeFun (p : P) (x : X) : A.Vertex := by
  classical
  exact if h : x ∈ Set.range (A.inside p) then
    Sum.inl (Classical.choose h).val
  else Sum.inr ⟨p,⟨x,h⟩⟩

theorem placeFun_old (p : P) (u : K p) :
    A.placeFun p (A.inside p u) = A.oldVertex u.val := by
  classical
  unfold placeFun
  let hx : A.inside p u ∈ Set.range (A.inside p) := ⟨u,rfl⟩
  rw [dif_pos hx]
  have he := (A.inside p).injective (Classical.choose_spec hx)
  exact congrArg (fun u : K p => A.oldVertex u.val) he

theorem placeFun_private (p : P) (x : X) (hx : x ∉ Set.range (A.inside p)) :
    A.placeFun p x = Sum.inr ⟨p,⟨x,hx⟩⟩ := by
  classical
  unfold placeFun
  rw [dif_neg hx]

theorem placeFun_inj (p : P) : Function.Injective (A.placeFun p) := by
  classical
  intro x y h
  by_cases hx : x ∈ Set.range (A.inside p)
  · obtain ⟨u,rfl⟩ := hx
    rw [A.placeFun_old] at h
    by_cases hy : y ∈ Set.range (A.inside p)
    · obtain ⟨w,rfl⟩ := hy
      rw [A.placeFun_old] at h
      exact congrArg (A.inside p) (Subtype.ext (A.oldVertex.injective h))
    · rw [A.placeFun_private p y hy] at h
      cases h
  · rw [A.placeFun_private p x hx] at h
    by_cases hy : y ∈ Set.range (A.inside p)
    · obtain ⟨w,rfl⟩ := hy
      rw [A.placeFun_old] at h
      cases h
    · rw [A.placeFun_private p y hy] at h
      have he := Sum.inr.inj h
      exact congrArg (fun z : Σ p : P, {x : X // x ∉ Set.range (A.inside p)} =>
        z.2.val) he

noncomputable def place (p : P) : X ↪ A.Vertex :=
  ⟨A.placeFun p,A.placeFun_inj p⟩

noncomputable def padded (p : P) : Set A.Vertex := Set.range (A.place p)

theorem old_mem_padded (p : P) (x : V) :
    A.oldVertex x ∈ A.padded p ↔ x ∈ K p := by
  classical
  constructor
  · rintro ⟨y,hy⟩
    by_cases h : y ∈ Set.range (A.inside p)
    · obtain ⟨u,rfl⟩ := h
      change A.placeFun p (A.inside p u) = A.oldVertex x at hy
      rw [A.placeFun_old] at hy
      exact A.oldVertex.injective hy ▸ u.property
    · change A.placeFun p y = A.oldVertex x at hy
      rw [A.placeFun_private p y h] at hy
      cases hy
  · intro hx
    exact ⟨A.inside p ⟨x,hx⟩,A.placeFun_old p ⟨x,hx⟩⟩

theorem private_mem_padded (p r : P) (x : X) (hx : x ∉ Set.range (A.inside r)) :
    (Sum.inr ⟨r,⟨x,hx⟩⟩ : A.Vertex) ∈ A.padded p ↔ p = r := by
  classical
  constructor
  · rintro ⟨y,hy⟩
    by_cases h : y ∈ Set.range (A.inside p)
    · obtain ⟨u,rfl⟩ := h
      change A.placeFun p (A.inside p u) = Sum.inr _ at hy
      rw [A.placeFun_old] at hy
      cases hy
    · change A.placeFun p y = Sum.inr _ at hy
      rw [A.placeFun_private p y h] at hy
      exact congrArg Sigma.fst (Sum.inr.inj hy)
  · intro he
    subst p
    exact ⟨x,A.placeFun_private r x hx⟩

theorem padded_intersection (p r : P) (hne : p ≠ r) :
    A.padded p ∩ A.padded r = A.oldVertex '' (K p ∩ K r) := by
  ext z
  cases z with
  | inl x =>
    change (A.oldVertex x ∈ A.padded p ∧ A.oldVertex x ∈ A.padded r) ↔ _
    rw [A.old_mem_padded,A.old_mem_padded]
    constructor
    · intro h
      exact ⟨x,h,rfl⟩
    · rintro ⟨y,hy,he⟩
      have hEq : y = x := A.oldVertex.injective he
      exact hEq ▸ hy
  | inr u =>
    rcases u with ⟨q,⟨x,hx⟩⟩
    constructor
    · intro h
      exact (hne (((A.private_mem_padded p q x hx).mp h.1).trans
        ((A.private_mem_padded r q x hx).mp h.2).symm)).elim
    · rintro ⟨y,_,hy⟩
      cases hy

/-- For any partition of the original first wagons, the higher
carrier is the union of the padded wagons in its class. -/
noncomputable def unionCarrier {W : Type v} (parent : P → W) (w : W) : Set A.Vertex :=
  {x | ∃ p, parent p = w ∧ x ∈ A.padded p}

def oldUnionCarrier {W : Type v} (parent : P → W) (w : W) : Set V :=
  {x | ∃ p, parent p = w ∧ x ∈ K p}

/-- Every shared connector of distinct padded higher wagons is
an original vertex, with exactly its original incidences. -/
theorem union_intersection {W : Type v} (parent : P → W)
    (a b : W) (hne : a ≠ b) :
    A.unionCarrier parent a ∩ A.unionCarrier parent b =
      A.oldVertex '' (A.oldUnionCarrier parent a ∩ A.oldUnionCarrier parent b) := by
  ext x
  constructor
  · rintro ⟨⟨p,hp,hxp⟩,⟨r,hr,hxr⟩⟩
    have hpne : p ≠ r := fun he => hne (hp.symm.trans ((congrArg parent he).trans hr))
    have hmem : x ∈ A.padded p ∩ A.padded r := ⟨hxp,hxr⟩
    rw [A.padded_intersection p r hpne] at hmem
    obtain ⟨v,hv,rfl⟩ := hmem
    exact ⟨v,⟨⟨p,hp,hv.1⟩,⟨r,hr,hv.2⟩⟩,rfl⟩
  · rintro ⟨v,⟨⟨p,hp,hvp⟩,⟨r,hr,hvr⟩⟩,rfl⟩
    exact ⟨⟨p,hp,(A.old_mem_padded p v).mpr hvp⟩,
      ⟨r,hr,(A.old_mem_padded r v).mpr hvr⟩⟩

/-- Padding preserves all labelled girth bounds of a wagon cut,
even when private vertices occur in several nested higher levels.
Every connector of a genuine cycle pulls back uniquely. -/
theorem union_girth {W : Type v} (parent : P → W) {g : ℕ}
    (hg : LabelledGirthGT (A.oldUnionCarrier parent) g) :
    LabelledGirthGT (A.unionCarrier parent) g := by
  classical
  rintro ⟨C,hC⟩
  have hmem : ∀ i, ∃ x, x ∈ A.oldUnionCarrier parent (C.label i) ∩
      A.oldUnionCarrier parent (C.label (cyclicSucc i)) ∧
      A.oldVertex x = C.vertex i := by
    intro i
    have hn : C.label i ≠ C.label (cyclicSucc i) :=
      fun h => contactSucc_ne C.hlength i (C.label_injective h).symm
    have h : C.vertex i ∈ A.unionCarrier parent (C.label i) ∩
      A.unionCarrier parent (C.label (cyclicSucc i)) := ⟨C.left_mem i,C.right_mem i⟩
    rw [A.union_intersection parent _ _ hn] at h
    exact h
  choose x hx using hmem
  let B : LabelledBergeCycle (A.oldUnionCarrier parent) := {
    length := C.length
    hlength := C.hlength
    label := C.label
    vertex := x
    label_injective := C.label_injective
    vertex_injective := fun i j h =>
      C.vertex_injective ((hx i).2.symm.trans ((congrArg A.oldVertex h).trans (hx j).2))
    left_mem := fun i => (hx i).1.1
    right_mem := fun i => (hx i).1.2
  }
  exact hg ⟨B,hC⟩

/-- Filling the padded edges by a template uses exactly the
canonical substitution already constructed. -/
noncomputable def paddedHypergraph : ContactHypergraphData A.Vertex P PEmpty.{v+1} where
  edgeCarrier := A.padded
  copyCarrier := PEmpty.elim
  copyEdges := PEmpty.elim

noncomputable def filling {F J : Type v} (L : ContactHypergraphData X F J)
    (hcover : ∀ x, ∃ f, x ∈ L.edgeCarrier f) (hne : Nonempty F) :
    ContactFilling A.paddedHypergraph L where
  place := A.place
  range_eq := fun _ => rfl
  template_cover := hcover
  template_nonempty := hne

end ContactWagonPadding
end StructuralRamsey.Girth
