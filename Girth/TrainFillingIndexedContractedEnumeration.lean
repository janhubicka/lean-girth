import Girth.TrainFillingIndexedContractedCarriers

set_option Elab.async false

/-!
# Exact finite arity of all heterogeneous contracted first wagons

The actual G0 first-wagon carrier indexed by (choice, wagon) is the
image of the common X under the checked private first-wagon placement.
No auxiliary edge-size hypothesis is required: for finite X, choose
an enumeration of X and compose with each actual placement.

This gives explicit bijective enumerations of every physical
contracted carrier by Fin(card X). It supplies the exact uniform-arity
premise needed by the relational M-support presentation, including
empty choice and old-wagon index types. No relational M is assumed.
-/

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
