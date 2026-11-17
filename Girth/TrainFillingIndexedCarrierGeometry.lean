import Girth.TrainFillingIndexedChoiceCore

set_option Elab.async false

/-! # Whole contracted carriers, finite enumerations and predicates -/

namespace StructuralRamsey.Girth.IndexedPrivateChoice

universe v
variable {C V P X : Type v}
variable (U : C → PrivateWagonInput V P X)

/-- A physical contracted edge has its COMPLETE first-wagon carrier,
not merely the selected W* edge subset inside that wagon. -/
def contractedCarrier (e : C × P) : Set (Vertex U) :=
  (tagVertex U e.1) '' Set.range ((U e.1).place e.2)

/-- The contracted first-wagon edge carrier stays in its own
choice component, with all other choices completely disjoint. -/
theorem contractedCarrier_subset_component (e : C × P) :
    contractedCarrier U e ⊆ componentCarrier U e.1 := by
  rintro z ⟨w, _hw, rfl⟩
  exact ⟨w, rfl⟩

/-- The whole contracted heterogeneous G0 is a LINEAR physical
hypergraph whenever each choice's old first wagons form a linear family.
No two-vertex hypothesis is needed for linearity itself; it is needed
only to rule out duplicate contracted edge carriers. -/
theorem contractedCarrier_linear
    (hOld : ∀ c : C, ∀ p q : P, p ≠ q →
      ((U c).oldCarrier p ∩ (U c).oldCarrier q).Subsingleton) :
    ∀ e f : C × P, e ≠ f →
      (contractedCarrier U e ∩ contractedCarrier U f).Subsingleton := by
  rintro ⟨c, p⟩ ⟨d, q⟩ hef
  by_cases hcd : c = d
  · subst d
    have hpq : p ≠ q := by
      intro h
      exact hef (congrArg (Prod.mk c) h)
    have hSmall : (Set.range ((U c).place p) ∩
        Set.range ((U c).place q)).Subsingleton :=
      (U c).ranges_inter_subsingleton (hOld c) p q hpq
    intro z hz w hw
    obtain ⟨x, hx, hxz⟩ := hz.1
    obtain ⟨y, hy, hyz⟩ := hz.2
    have hxy : x = y := (tagVertex_injective U c) (hxz.trans hyz.symm)
    subst y
    obtain ⟨u, hu, huw⟩ := hw.1
    obtain ⟨v, hv, hvw⟩ := hw.2
    have huv : u = v := (tagVertex_injective U c) (huw.trans hvw.symm)
    subst v
    have hxu : x = u := hSmall ⟨hx, hy⟩ ⟨hu, hv⟩
    calc
      z = tagVertex U c x := hxz.symm
      _ = tagVertex U c u := congrArg (tagVertex U c) hxu
      _ = w := huw
  · intro z hz w hw
    have hc : z ∈ componentCarrier U c :=
      contractedCarrier_subset_component U (c, p) hz.1
    have hd : z ∈ componentCarrier U d :=
      contractedCarrier_subset_component U (d, q) hz.2
    exact False.elim ((Set.disjoint_left.mp
      (componentCarrier_disjoint U c d hcd)) hc hd)

/-- The actual contracted edge carriers are physically distinct.

Nontriviality of X is essential: a single-vertex X would allow distinct
first wagons to have the same singleton carrier even in a linear train.
The local old-wagon intersection hypothesis is the ordinary first-wagon
linearity of G0; it is not an output realization assumption. -/
theorem contractedCarrier_injective [Nontrivial X]
    (hOld : ∀ c : C, ∀ p q : P, p ≠ q →
      ((U c).oldCarrier p ∩ (U c).oldCarrier q).Subsingleton) :
    Function.Injective (contractedCarrier U) := by
  rintro ⟨c, p⟩ ⟨d, q⟩ hEq
  have hcd : c = d := by
    obtain ⟨x⟩ := (inferInstance : Nonempty X)
    have hz : tagVertex U c ((U c).place p x) ∈
        contractedCarrier U (c, p) :=
      ⟨(U c).place p x, ⟨x, rfl⟩, rfl⟩
    rw [hEq] at hz
    obtain ⟨z, _hz, hzEq⟩ := hz
    exact (congrArg Sigma.fst hzEq).symm
  subst d
  have hRange : Set.range ((U c).place p) =
      Set.range ((U c).place q) := by
    ext z
    constructor
    · intro hz
      have hTag : tagVertex U c z ∈ contractedCarrier U (c, p) :=
        ⟨z, hz, rfl⟩
      rw [hEq] at hTag
      obtain ⟨w, hw, hwz⟩ := hTag
      have hzw : w = z := (tagVertex_injective U c) hwz
      simpa only [hzw] using hw
    · intro hz
      have hTag : tagVertex U c z ∈ contractedCarrier U (c, q) :=
        ⟨z, hz, rfl⟩
      rw [← hEq] at hTag
      obtain ⟨w, hw, hwz⟩ := hTag
      have hzw : w = z := (tagVertex_injective U c) hwz
      simpa only [hzw] using hw
  have hpq : p = q := by
    by_contra hpq
    have hSmall : (Set.range ((U c).place p) ∩
        Set.range ((U c).place q)).Subsingleton :=
      (U c).ranges_inter_subsingleton (hOld c) p q hpq
    obtain ⟨x, y, hxy⟩ := exists_pair_ne X
    have hxP : (U c).place p x ∈ Set.range ((U c).place p) := ⟨x, rfl⟩
    have hyP : (U c).place p y ∈ Set.range ((U c).place p) := ⟨y, rfl⟩
    have hxQ : (U c).place p x ∈ Set.range ((U c).place q) := by
      rw [← hRange]
      exact hxP
    have hyQ : (U c).place p y ∈ Set.range ((U c).place q) := by
      rw [← hRange]
      exact hyP
    have hxyPlace : (U c).place p x = (U c).place p y :=
      hSmall ⟨hxP, hxQ⟩ ⟨hyP, hyQ⟩
    exact hxy ((U c).place_injective p hxyPlace)
  exact congrArg (Prod.mk c) hpq

end StructuralRamsey.Girth.IndexedPrivateChoice

namespace StructuralRamsey.Girth.IndexedPrivateChoice

universe v
variable {C V P X : Type v} (U : C → PrivateWagonInput V P X)

/-- Canonical finite enumeration of a first-wagon edge. It retains the
entire X-placement and the choice tag, not merely selected W* edges. -/
noncomputable def contractedEnumeration [Fintype X]
    (e : C × P) :
    Fin (Fintype.card X) ↪ Vertex U where
  toFun := fun i =>
    tagVertex U e.1 ((U e.1).place e.2 ((Fintype.equivFin X).symm i))
  inj' := by
    intro i j hij
    have hLocal :
        (U e.1).place e.2 ((Fintype.equivFin X).symm i) =
        (U e.1).place e.2 ((Fintype.equivFin X).symm j) :=
      (tagVertex_injective U e.1) hij
    exact (Fintype.equivFin X).symm.injective
      ((U e.1).place_injective e.2 hLocal)

/-- The enumerated edge is precisely the actual contracted carrier. -/
theorem contractedEnumeration_range [Fintype X]
    (e : C × P) :
    Set.range (contractedEnumeration U e : Fin (Fintype.card X) → Vertex U) =
      contractedCarrier U e := by
  ext z
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨(U e.1).place e.2 ((Fintype.equivFin X).symm i),
      ⟨(Fintype.equivFin X).symm i, rfl⟩, rfl⟩
  · rintro ⟨w, ⟨x, hx⟩, hzw⟩
    refine ⟨Fintype.equivFin X x, ?_⟩
    change tagVertex U e.1
      ((U e.1).place e.2 ((Fintype.equivFin X).symm
        (Fintype.equivFin X x))) = z
    simpa only [Equiv.symm_apply_apply] using
      (congrArg (tagVertex U e.1) hx).trans hzw

/-- Every actual contracted edge has the same finite cardinality,
with an explicit injective enumeration of its WHOLE carrier. -/
theorem contractedFamily_uniform [Fintype X] :
    ∀ edge ∈ Set.range (contractedCarrier U),
      ∃ i : Fin (Fintype.card X) ↪ Vertex U,
        Set.range (i : Fin (Fintype.card X) → Vertex U) = edge := by
  rintro edge ⟨e, rfl⟩
  exact ⟨contractedEnumeration U e, contractedEnumeration_range U e⟩

/-- No new isolated vertices appear in the contracted choice union:
private vertices lie in their own expanded wagon, while each old
vertex lies in some old first wagon by the input's actual coverage. -/
theorem contractedFamily_covers
    (hOldCover : ∀ c : C, ∀ v : V,
      ∃ p : P, v ∈ (U c).oldCarrier p) :
    ∀ z : Vertex U, ∃ e : C × P, z ∈ contractedCarrier U e := by
  rintro ⟨c, z⟩
  cases z with
  | inl v =>
      obtain ⟨p, hv⟩ := hOldCover c v
      refine ⟨(c, p), ?_⟩
      exact ⟨Sum.inl v, ((U c).old_mem_range p v).mpr hv, rfl⟩
  | inr z =>
      rcases z with ⟨⟨p, x⟩, hx⟩
      refine ⟨(c, p), ?_⟩
      have hp : (U c).place p x =
          Sum.inr (⟨(p, x), hx⟩ : (U c).PrivateVertex) := by
        simp only [PrivateWagonInput.place, dif_neg hx]
      exact ⟨(U c).place p x, ⟨x, rfl⟩,
        congrArg (tagVertex U c) hp⟩

/-- An explicitly chosen common enumeration of X, useful when
the chosen numbering must also preserve within-predicate orders. -/
noncomputable def contractedEnumerationOfEquiv {k : ℕ}
    (enumerateX : Fin k ≃ X) (e : C × P) :
    Fin k ↪ Vertex U where
  toFun := fun i =>
    tagVertex U e.1 ((U e.1).place e.2 (enumerateX i))
  inj' := by
    intro i j hij
    have hLocal : (U e.1).place e.2 (enumerateX i) =
        (U e.1).place e.2 (enumerateX j) :=
      (tagVertex_injective U e.1) hij
    exact enumerateX.injective ((U e.1).place_injective e.2 hLocal)

/-- Its image is the actual whole first-wagon carrier, independent of
the enumeration, so changing to an ordered enumeration loses no edges. -/
theorem contractedEnumerationOfEquiv_range {k : ℕ}
    (enumerateX : Fin k ≃ X) (e : C × P) :
    Set.range (contractedEnumerationOfEquiv U enumerateX e : Fin k → Vertex U) =
      contractedCarrier U e := by
  ext z
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨(U e.1).place e.2 (enumerateX i), ⟨enumerateX i, rfl⟩, rfl⟩
  · rintro ⟨w, ⟨x, hx⟩, hzw⟩
    refine ⟨enumerateX.symm x, ?_⟩
    change tagVertex U e.1 ((U e.1).place e.2
      (enumerateX (enumerateX.symm x))) = z
    simpa only [Equiv.apply_symm_apply] using
      (congrArg (tagVertex U e.1) hx).trans hzw

/-- Predicates on old target vertices are retained, while private
positions inherit the predicate of their local X-coordinate. -/
def contractedVertexColour {I : Type*}
    (oldColour : V → I) (templateColour : X → I) :
    Vertex U → I
  | ⟨_, .inl v⟩ => oldColour v
  | ⟨_, .inr z⟩ => templateColour z.1.2

/-- If each old first-wagon coordinate respects the original unary
predicate, every actual private placement also preserves that predicate.
There is no separately postulated colour map on contracted edges. -/
theorem contractedVertexColour_place {I : Type*}
    (oldColour : V → I) (templateColour : X → I)
    (hColour : ∀ c : C, ∀ p : P,
      ∀ z : {v : V // v ∈ (U c).oldCarrier p},
        oldColour z.1 = templateColour ((U c).coordinate p z))
    (c : C) (p : P) (x : X) :
    contractedVertexColour U oldColour templateColour
        (tagVertex U c ((U c).place p x)) = templateColour x := by
  classical
  by_cases h : x ∈ Set.range ((U c).coordinate p)
  · obtain ⟨z, hz⟩ := h
    have hp : (U c).place p x = Sum.inl z.1 := by
      rw [← hz]
      exact (U c).place_old p z
    change contractedVertexColour U oldColour templateColour
      (tagVertex U c ((U c).place p x)) = templateColour x
    rw [hp]
    change oldColour z.1 = templateColour x
    exact (hColour c p z).trans (congrArg templateColour hz)
  · have hp : (U c).place p x =
        Sum.inr (⟨(p, x), h⟩ : (U c).PrivateVertex) := by
      simp only [PrivateWagonInput.place, dif_neg h]
    change contractedVertexColour U oldColour templateColour
      (tagVertex U c ((U c).place p x)) = templateColour x
    rw [hp]
    rfl

/-- Thus the concrete enumeration of every contracted G0 edge has the
same fixed template colour profile, not a choice-dependent one. -/
theorem contractedEnumeration_colour [Fintype X] {I : Type*}
    (oldColour : V → I) (templateColour : X → I)
    (hColour : ∀ c : C, ∀ p : P,
      ∀ z : {v : V // v ∈ (U c).oldCarrier p},
        oldColour z.1 = templateColour ((U c).coordinate p z))
    (e : C × P) (i : Fin (Fintype.card X)) :
    contractedVertexColour U oldColour templateColour
        (contractedEnumeration U e i) =
      templateColour ((Fintype.equivFin X).symm i) :=
  contractedVertexColour_place U oldColour templateColour hColour
    e.1 e.2 ((Fintype.equivFin X).symm i)

end StructuralRamsey.Girth.IndexedPrivateChoice
