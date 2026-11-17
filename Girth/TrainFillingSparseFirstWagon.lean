import Girth.PartiteOrderCompatibility
import Girth.TrainFillingPrivateRealUnionLinear
import Girth.TrainFillingPrivateCompletedOrderedW

set_option autoImplicit false
set_option Elab.async false

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure
open StructuralRamsey.Partite (System)

universe u v
variable {K : RelLanguage.{u}} {A V P : Type v}

/-- The sparse disjoint union keeps precisely the restrictions to the
first wagons, with the original fine coordinates on each tagged vertex. -/
def firstWagonSparseSystem (Target : System K A V) (carrier : P → Set V) :
    System K A (FirstWagonUnionVertex carrier) where
  toRelStructure := firstWagonDisjointUnion carrier (fun p => Target.toRelStructure.induce (carrier p))
  part w := Target.part w.2.1
  transversal := by
    intro r z hz i j hij
    obtain ⟨p, t, ht, hRel⟩ := hz
    change Target.part (z i).2.1 = Target.part (z j).2.1 at hij
    rw [ht i, ht j] at hij
    have hEq : t i = t j := Subtype.ext
      (Target.transversal r (Subtype.val ∘ t) hRel i j hij)
    exact (ht i).trans ((congrArg (fun x => (⟨p, x⟩ : FirstWagonUnionVertex carrier)) hEq).trans
      (ht j).symm)

/-- Original forward comparisons remain forward within every tagged wagon. -/
theorem firstWagonSparseSystem_forwardCompatible [LT A]
    (Target : System K.withOrder A V) (carrier : P → Set V)
    (hTarget : PartiteOrderCompatible Target) :
    PartiteOrderCompatible (firstWagonSparseSystem Target carrier) := by
  intro z hz
  obtain ⟨p, t, ht, hRel⟩ := hz
  change Target.part (z 0).2.1 < Target.part (z 1).2.1
  rw [ht (0 : Fin 2), ht (1 : Fin 2)]
  exact hTarget (Subtype.val ∘ t) hRel

/-- A spanning relation confines each physical sparse edge to one wagon.
Its untagged carrier is exactly an original physical edge contained there. -/
theorem firstWagonSparseSystem_support_eq_tagged
    (Small : RelStructure K A) (Target : System K A V) (carrier : P → Set V)
    (hPositive : ∀ r : K.Symbol, 0 < K.arity r) (hSpan : HasSpanningRelation Small) :
    supportCopies Small (firstWagonSparseSystem Target carrier).toRelStructure =
      taggedFirstWagonEdges carrier (supportCopies Small Target.toRelStructure) := by
  ext e
  change e ∈ supportCopies Small (firstWagonDisjointUnion carrier
    (fun p => Target.toRelStructure.induce (carrier p))) ↔ _
  rw [firstWagonDisjointUnion_supportCopies_iff Small carrier _ hPositive hSpan]
  constructor
  · rintro ⟨p, f, ⟨a, ha⟩, he⟩
    let inc := RelStructure.inclusion Target.toRelStructure (carrier p)
    refine ⟨p, f, ⟨inc.comp a, ?_⟩, he⟩
    rw [ha]
    exact UniformPrivateTemplate.image_copyCarrier_comp Small
      (Target.toRelStructure.induce (carrier p)) Target.toRelStructure inc a
  · rintro ⟨p, f, ⟨a, ha⟩, he⟩
    let inc := RelStructure.inclusion Target.toRelStructure (carrier p)
    have hRange (u : A) : ∃ x : {v : V // v ∈ carrier p}, a u = inc x := by
      have hu : a u ∈ Subtype.val '' f := ha.symm ▸ (show a u ∈ copyCarrier a from ⟨u, rfl⟩)
      obtain ⟨x, _, hx⟩ := hu
      exact ⟨x, hx.symm⟩
    let aLocal := a.factorThroughRange inc hRange
    have hComp : inc.comp aLocal = a := Embedding.ext (fun u => (Classical.choose_spec (hRange u)).symm)
    refine ⟨p, f, ⟨aLocal, ?_⟩, he⟩
    apply (Set.image_injective.mpr (Subtype.val_injective : Function.Injective
      (Subtype.val : {v : V // v ∈ carrier p} → V)))
    change Subtype.val '' f = inc '' copyCarrier aLocal
    calc
      Subtype.val '' f = copyCarrier a := ha
      _ = copyCarrier (inc.comp aLocal) := congrArg copyCarrier hComp.symm
      _ = inc '' copyCarrier aLocal :=
        (UniformPrivateTemplate.image_copyCarrier_comp Small
          (Target.toRelStructure.induce (carrier p)) Target.toRelStructure inc aLocal).symm

end StructuralRamsey.Girth
