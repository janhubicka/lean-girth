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
    Set.range (U.contractedEnumeration e : Fin (Fintype.card X) → Vertex U) =
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
  exact ⟨U.contractedEnumeration e, U.contractedEnumeration_range e⟩

end StructuralRamsey.Girth.IndexedPrivateChoice
