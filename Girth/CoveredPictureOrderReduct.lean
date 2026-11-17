import Girth.DesignatedPicture
import Girth.OrderReductUniformEdge

/-! # Edge support of the order reduct of a covered picture -/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}} {UA VB P X : Type v}

/-- The ordered and unordered supports agree when the unordered source is
irreducible and every unordered source carrier in the target lifts to an
ordered copy on the same vertices. The ambient picture can have partial order. -/
theorem supportCopies_orderReduct_eq_of_designatedCover
    {A : RelStructure L.withOrder UA} {B : RelStructure L.withOrder VB}
    {D : RelStructure L.withOrder P} {C : StructuralRamsey.Partite.System L.withOrder P X}
    {family : Set (Embedding B D)}
    (hCover : DesignatedCoversIrreducibles B D C family)
    (hIrr : A.orderReduct.Irreducible)
    (hLift : supportCopies A.orderReduct B.orderReduct ⊆ supportCopies A B) :
    supportCopies A.orderReduct C.toRelStructure.orderReduct =
      supportCopies A C.toRelStructure := by
  classical
  apply Set.Subset.antisymm
  · rintro S ⟨a, rfl⟩
    have hCarrier : (C.toRelStructure.induce (copyCarrier a)).Irreducible := by
      intro x y hxy
      obtain ⟨r, z, i, j, hr, hi, hj⟩ := hIrr.range_embedding a hxy
      exact ⟨.inl r, z, i, j, hr, hi, hj⟩
    obtain ⟨c, hc⟩ := hCover (copyCarrier a) hCarrier
    have hFactor (x : UA) : ∃ b : VB, a x = c.embedding.orderReduct b :=
      hc ⟨a x, ⟨x, rfl⟩⟩
    let b := a.factorThroughRange c.embedding.orderReduct hFactor
    have hb (x : UA) : a x = c.embedding.orderReduct (b x) :=
      Classical.choose_spec (hFactor x)
    obtain ⟨b', hEq⟩ := hLift (show copyCarrier b ∈ _ from ⟨b, rfl⟩)
    refine ⟨c.embedding.comp b', ?_⟩
    change Set.range a = Set.range (c.embedding ∘ b')
    have hComp : (a : UA → X) = c.embedding ∘ b := funext hb
    rw [hComp, Set.range_comp, Set.range_comp]
    exact congrArg (Set.image (c.embedding : VB → X)) hEq
  · rintro S ⟨a, rfl⟩
    exact ⟨a.orderReduct, rfl⟩

/-- Strong inducedness of a carrier uses precisely the ambient edge support. -/
theorem aStrong_orderReduct_iff_of_support_eq
    {A : RelStructure L.withOrder UA} {C : RelStructure L.withOrder X}
    {S : Set X}
    (hSupport : supportCopies A.orderReduct C.orderReduct = supportCopies A C) :
    AStrong A.orderReduct C.orderReduct S ↔ AStrong A C S := by
  constructor
  · intro h a
    exact h a.orderReduct
  · intro h a
    have ha : copyCarrier a ∈ supportCopies A.orderReduct C.orderReduct := ⟨a, rfl⟩
    rw [hSupport] at ha
    obtain ⟨b, hEq⟩ := ha
    simpa only [hEq] using h b

/-- An induced embedding of the unordered single-edge source has an
irreducible range, including when the ambient order is partial. -/
theorem uniformEdgeSource_irreducible (k : ℕ) :
    (uniformEdgeSource.{v} k).Irreducible := by
  intro x y _
  exact ⟨(), ULift.up, x.down, y.down, fun _ _ h => congrArg ULift.down h, rfl, rfl⟩

/-- The relation of the edge already witnesses irreducibility in the ordered
language. -/
theorem orderedUniformEdgeSource_irreducible (k : ℕ) :
    (uniformEdgeSource.{v} k).ordered.Irreducible := by
  intro x y hxy
  obtain ⟨r, t, i, j, hr, hi, hj⟩ := uniformEdgeSource_irreducible k hxy
  exact ⟨.inl r, t, i, j, hr, hi, hj⟩

/-- In the actual covered picture of a finite uniform target, forgetting
the partial order leaves the ambient edge carriers unchanged. -/
theorem uniformEdgeSupport_orderReduct_eq_of_designatedCover
    (k : ℕ) (E : Set (Set VB)) [Finite VB] [LinearOrder VB]
    (hUniform : ∀ e ∈ E, e.ncard = k)
    {D : RelStructure (uniformEdgeLanguage k).withOrder P}
    {C : StructuralRamsey.Partite.System (uniformEdgeLanguage k).withOrder P X}
    {family : Set (Embedding (uniformEdgeTarget k E).ordered D)}
    (hCover : DesignatedCoversIrreducibles (uniformEdgeTarget k E).ordered D C family) :
    supportCopies (uniformEdgeSource k) C.toRelStructure.orderReduct =
      supportCopies (uniformEdgeSource k).ordered C.toRelStructure :=
  supportCopies_orderReduct_eq_of_designatedCover
    (A := (uniformEdgeSource k).ordered) hCover
    (uniformEdgeSource_irreducible k) (orderedUniformEdge_carrierLift k E hUniform)

end StructuralRamsey.Girth
