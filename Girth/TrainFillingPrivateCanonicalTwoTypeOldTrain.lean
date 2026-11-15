import Girth.TrainFillingPrivateTwoTypeOrderGirth
import Girth.TrainFillingPrivateSelectedStageFilling

set_option Elab.async false

/-!
# The canonical two-type filling uses the SAME actual old train

The verified generic full-system-girth theorem applies to
S.train on the COMPLETE Aold-support old edges of selected N.

Earlier Track 5 adapters represented the same old physical edge
type as the OldEdge subtype of an arbitrary UniformFillingData H,
and transported S.train along the equivalence
  actualFilledOldEdgeEquiv Aold N H hOld.

For the actual cutoff-two canonical filling
  H = UniformFillingData.ofSupportCopies Asmall R
        (supportCopies Aold N) place ...,
the two old-edge subtypes are literally THE SAME TYPE.
The equivalence is the identity and restricting any train
along it is the identity, not a different selected train.

This removes the remaining old-train mismatch before
combining the new two-type OrderStage girth theorem with
the actual selected (old parent, EHN choice) scattering
realization.

The two edge languages and edge cardinalities remain
INDEPENDENT. The small local hypergraph X is never
required to contain a copy of the large old edge type.

Candidate source; a local exact-head Lean build remains necessary.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u0 u1 v

variable {Lold : RelLanguage.{u0}} {Lsmall : RelLanguage.{u1}}
variable {Uold Usmall N X : Type v}

/-- Restricting an actual train along the identity embedding
does not alter the train's hierarchy or any of its
equivalence relations. -/
theorem EdgeTrainLevels.restrict_equiv_refl
    {E : Type v} {m : ℕ} (T : EdgeTrainLevels E m) :
    T.restrict (Equiv.refl E).toEmbedding = T := by
  cases T
  rfl

/-- In the ACTUAL canonical filling, the identification
of the physical old-edge subtype with the old Aold-support
subtype is precisely Equiv.refl: no edge occurrence or
train label is changed in either direction. -/
theorem canonicalTwoTypeOldEdgeEquiv_eq_refl
    (Aold : RelStructure Lold Uold)
    (N : RelStructure Lold N)
    (Asmall : RelStructure Lsmall Usmall)
    [Nontrivial Usmall]
    (R : RelStructure Lsmall X)
    (place : OldACarrierEdge Aold N → (X ↪ N))
    (hRange : ∀ e, Set.range (place e) = e.1)
    (hOldLinear : ∀ e f : OldACarrierEdge Aold N,
      e ≠ f → (e.1 ∩ f.1).Subsingleton)
    (hCovers : ∀ x : X, ∃ a : Embedding Asmall R,
      x ∈ copyCarrier a) :
    let H : UniformFillingData N X :=
      UniformFillingData.ofSupportCopies Asmall R
        (supportCopies Aold N) place hRange hOldLinear hCovers
    IndexedPrivateChoice.actualFilledOldEdgeEquiv
        (X := X) Aold N H (by rfl) =
      Equiv.refl (OldACarrierEdge Aold N) := by
  let H : UniformFillingData N X :=
    UniformFillingData.ofSupportCopies Asmall R
      (supportCopies Aold N) place hRange hOldLinear hCovers
  apply Equiv.ext
  intro e
  apply Subtype.ext
  rfl

end StructuralRamsey.Girth

namespace StructuralRamsey.Girth.IndexedPrivateChoice

open StructuralRamsey.RelStructure

universe u0 u1 v

variable {Lold : RelLanguage.{u0}} {Lsmall : RelLanguage.{u1}}
variable {Uold Usmall C V P X : Type v}
variable (U : C → PrivateWagonInput V P X)

/-- For the SAME actual canonical H, the earlier selected
old-train construction is EQUAL to S.train, not only
related by a parameter-dependent rel-iff. This is
exactly what the two-type OrderStage girth bridge
needs at the labelled selected-parent call site. -/
theorem actualSelectedFilledOldTrain_eq_stage_for_canonicalH
    [Nontrivial X]
    (Aold : RelStructure Lold Uold)
    (M : RelStructure Lold (Vertex U))
    {t : List ℕ}
    (T : EdgeTrainLevels P t.length) (hm : 0 < t.length)
    (hSupport : supportCopies Aold M =
      Set.range (contractedCarrier U))
    (hLinear : ∀ c : C, ∀ p q : P, p ≠ q →
      ((U c).oldCarrier p ∩ (U c).oldCarrier q).Subsingleton)
    {Base : Type v} (D : RelStructure Lold Base)
    (family : Set (Embedding M D))
    (allowed : Fin (t.length + 1) → Set Base)
    (S : TrainRecursiveWitness.ForestTailStage Aold M
      D family t
      (contractedPhysicalTrain U Aold M T hm hSupport hLinear)
      allowed)
    (Asmall : RelStructure Lsmall Usmall)
    [Nontrivial Usmall]
    (R : RelStructure Lsmall X)
    (place : OldACarrierEdge Aold S.system.toRelStructure →
      (X ↪ S.Vertex))
    (hRange : ∀ e, Set.range (place e) = e.1)
    (hCovers : ∀ x : X, ∃ a : Embedding Asmall R,
      x ∈ copyCarrier a) :
    let H : UniformFillingData S.Vertex X :=
      UniformFillingData.ofSupportCopies Asmall R
        (supportCopies Aold S.system.toRelStructure)
        place hRange
        (oldACarrier_edges_inter_subsingleton_of_aLinear
          Aold S.system.toRelStructure S.aLinear)
        hCovers
    actualSelectedFilledOldTrain U Aold M T hm
        hSupport hLinear D family allowed
        S H (by rfl) = S.train := by
  let H : UniformFillingData S.Vertex X :=
    UniformFillingData.ofSupportCopies Asmall R
      (supportCopies Aold S.system.toRelStructure)
      place hRange
      (oldACarrier_edges_inter_subsingleton_of_aLinear
        Aold S.system.toRelStructure S.aLinear)
      hCovers
  change S.train.restrict
    ((actualFilledOldEdgeEquiv (X := X) Aold
        S.system.toRelStructure H (by rfl)).toEmbedding) = S.train
  rw [canonicalTwoTypeOldEdgeEquiv_eq_refl
    Aold S.system.toRelStructure Asmall R place hRange
    (oldACarrier_edges_inter_subsingleton_of_aLinear
      Aold S.system.toRelStructure S.aLinear) hCovers]
  exact S.train.restrict_equiv_refl

end StructuralRamsey.Girth.IndexedPrivateChoice
