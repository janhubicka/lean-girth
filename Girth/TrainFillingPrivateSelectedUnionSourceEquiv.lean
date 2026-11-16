import Girth.TrainFillingPrivateSelectedUnion
import Girth.TrainFillingPrivateActualSourceOwnerTransport

set_option Elab.async false

/-!
# Exact original edge type of a selected EHN first-wagon summand

The fromSelectedUnion constructor DOES NOT invent local edges:
its oldCarrier is exactly the input carrier and its piece.localEdges
is definitionally supportCopies of the corresponding induced local
relational structure. Consequently its OriginalEdge type is the
genuine dependent first-wagon edge type.

We specialize to the original train's wagonClassCarrier and obtain
the actual source edge equivalence. This is an identification for
the concrete fromSelectedUnion constructor, not for arbitrary
SummandPrivateTemplate records.

Source candidate: exact-head Lean kernel and axiom checks required.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}} {UA V W X : Type v}

/-- The full original physical edge type is canonically equivalent
to the OriginalEdge type of the selected heterogeneous template.
The selected W-copy changes coordinates in X, not the old edge set. -/
noncomputable def selectedUnionActualSourceEdgeEquiv
    [Nontrivial UA]
    (A : RelStructure L UA) (D : RelStructure L V)
    {m : ℕ}
    (T : EdgeTrainLevels
      {e : Set V // e ∈ supportCopies A D} m)
    (μ : Fin (m + 1))
    (g : ℕ) (hg : 2 ≤ g)
    (hGirth : LabelledGirthGT
      (T.wagonClassCarrier
        (fun e : {e : Set V // e ∈ supportCopies A D} => e.1) μ) g)
    (B : RelStructure L W) (R : RelStructure L X)
    (include : (p : Quotient (T.wagonSetoid μ)) →
      Embedding (D.induce
        (T.wagonClassCarrier
          (fun e : {e : Set V // e ∈ supportCopies A D} => e.1) μ p)) B)
    (selected : Embedding B R)
    (hInclude : ∀ p, AStrong A B (copyCarrier (include p)))
    (hSelected : AStrong A R (copyCarrier selected))
    (hCovered : ∀ p (x : {x : V //
      x ∈ T.wagonClassCarrier
        (fun e : {e : Set V // e ∈ supportCopies A D} => e.1) μ p}),
      ∃ a : Embedding A
        (D.induce (T.wagonClassCarrier
          (fun e : {e : Set V // e ∈ supportCopies A D} => e.1) μ p)),
        x ∈ copyCarrier a) :
    (SummandPrivateTemplate.fromSelectedUnion A B R
      (T.wagonClassCarrier
        (fun e : {e : Set V // e ∈ supportCopies A D} => e.1) μ)
      (fun p => D.induce
        (T.wagonClassCarrier
          (fun e : {e : Set V // e ∈ supportCopies A D} => e.1) μ p))
      include selected hInclude hSelected hCovered).OriginalEdge ≃
        {e : Set V // e ∈ supportCopies A D} := by
  change OriginalFirstWagonEdges A D
    (T.wagonClassCarrier
      (fun e : {e : Set V // e ∈ supportCopies A D} => e.1) μ) ≃
      {e : Set V // e ∈ supportCopies A D}
  exact T.actualSourceEdgeEquiv A D μ g hg hGirth

/-- Inverse images under this concrete selected-summand equivalence
retain the EXACT source train wagon quotient label. -/
theorem selectedUnionActualSourceEdgeEquiv_symm_owner
    [Nontrivial UA]
    (A : RelStructure L UA) (D : RelStructure L V)
    {m : ℕ}
    (T : EdgeTrainLevels
      {e : Set V // e ∈ supportCopies A D} m)
    (μ : Fin (m + 1))
    (g : ℕ) (hg : 2 ≤ g)
    (hGirth : LabelledGirthGT
      (T.wagonClassCarrier
        (fun e : {e : Set V // e ∈ supportCopies A D} => e.1) μ) g)
    (B : RelStructure L W) (R : RelStructure L X)
    (include : (p : Quotient (T.wagonSetoid μ)) →
      Embedding (D.induce
        (T.wagonClassCarrier
          (fun e : {e : Set V // e ∈ supportCopies A D} => e.1) μ p)) B)
    (selected : Embedding B R)
    (hInclude : ∀ p, AStrong A B (copyCarrier (include p)))
    (hSelected : AStrong A R (copyCarrier selected))
    (hCovered : ∀ p (x : {x : V //
      x ∈ T.wagonClassCarrier
        (fun e : {e : Set V // e ∈ supportCopies A D} => e.1) μ p}),
      ∃ a : Embedding A
        (D.induce (T.wagonClassCarrier
          (fun e : {e : Set V // e ∈ supportCopies A D} => e.1) μ p)),
        x ∈ copyCarrier a)
    (e : {e : Set V // e ∈ supportCopies A D}) :
    ((selectedUnionActualSourceEdgeEquiv A D T μ g hg hGirth
        B R include selected hInclude hSelected hCovered).symm e).1 =
      T.wagonClassOwner μ e := by
  change
    ((T.actualSourceEdgeEquiv A D μ g hg hGirth).symm e).1 =
      T.wagonClassOwner μ e
  exact T.actualSourceEdgeEquiv_symm_owner A D μ g hg hGirth e

end StructuralRamsey.Girth
