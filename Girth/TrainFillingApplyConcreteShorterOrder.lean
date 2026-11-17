import Girth.TrainFillingOrderedContraction
import Girth.TrainFillingApplyShorterOrder

set_option autoImplicit false
set_option Elab.async false

namespace StructuralRamsey.Girth.TrainRecursiveWitness

open StructuralRamsey.RelStructure
open StructuralRamsey.Partite (System)
open StructuralRamsey.Girth.IndexedPrivateChoice
open CoverageFree.Physical

universe u v
variable {K : RelLanguage.{u}} {A V X C : Type v} {k : ℕ} {tail : List ℕ}
variable [LinearOrder A] [Finite A] [Nontrivial A]
variable [LinearOrder V] [Fintype V] [LinearOrder X] [Finite X] [Nontrivial X]
variable [LinearOrder C] [Finite C]
variable {A₀ : RelStructure K A} {Target : System K.withOrder A V}
variable {R : System K.withOrder A X} {enumerate : X ≃ ULift.{v} (Fin k)}
variable {original : EdgeTrainLevels (OldACarrierEdge A₀.ordered Target.toRelStructure)
  (tail.length + 1)}

namespace CutoffTwoContraction

variable
  (localCopy : ∀ (_ : C) (p : original.FirstWagon),
    Embedding (Target.toRelStructure.induce (cutoffTwoFirstCarrier original Subtype.val p))
      R.toRelStructure)
  (localStrong : ∀ (c : C) (p : original.FirstWagon),
    AStrong A₀.ordered R.toRelStructure (copyCarrier (localCopy c p)))
  (localCover : ∀ (p : original.FirstWagon)
    (x : {v : V // v ∈ cutoffTwoFirstCarrier original Subtype.val p}),
    ∃ a : Embedding A₀.ordered
      (Target.toRelStructure.induce (cutoffTwoFirstCarrier original Subtype.val p)), x ∈ copyCarrier a)
  (firstLinear : ∀ p q : original.FirstWagon, p ≠ q →
    (cutoffTwoFirstCarrier original Subtype.val p ∩
      cutoffTwoFirstCarrier original Subtype.val q).Subsingleton)
  (templateCover : ∀ x : X, ∃ a : Embedding A₀.ordered R.toRelStructure, x ∈ copyCarrier a)
  (targetCover : ∀ x : V, ∃ a : Embedding A₀.ordered Target.toRelStructure, x ∈ copyCarrier a)
  (hColour : ∀ (c : C) (p : original.FirstWagon)
    (x : {v : V // v ∈ cutoffTwoFirstCarrier original Subtype.val p}),
    Target.part x.1 = R.part (localCopy c p x))
  (hCoordinates : ∀ c p, StrictMono (localCopy c p))
  (hEnumerate : StrictMono (fun i : Fin k => enumerate.symm (ULift.up i)))
  (hXBlocks : ∀ x y : X, R.part x ≠ R.part y → x < y → R.part x < R.part y)

local notation "Constructed" => ofLocalCopies (enumerate := enumerate) localCopy localStrong
  localCover firstLinear templateCover targetCover hColour hCoordinates hEnumerate hXBlocks

/-- Apply the shorter order assertion to the concrete contraction. Its full
order, physical support and allowed contacts follow from the construction. -/
theorem ofLocalCopies_exists_shorterOrderWitness
    [Nonempty (C × original.FirstWagon)]
    (ht : Admissible tail)
    (allowed : Fin (tail.length + 1 + 1) → Set A)
    (κ : Type v) [Fintype κ] [Nonempty κ]
    (hOriginalParameters : original.AdjacentParameters Subtype.val
      (fun ν => Target.part ⁻¹' allowed ν))
    (hOriginalCuts : ∀ j : Fin tail.length, LabelledGirthGT
      (original.wagonClassCarrier Subtype.val j.castSucc.succ) (tail.get j))
    (hOrder : ProjectedOrderEverySpanningType.{v, v} tail) :
    UnrestrictedPredicateOrderWitness (cutoffTwoShortSource R.part enumerate)
      (Constructed).system tail ((Constructed).train (List.length_pos_iff.mpr ht.nonempty))
      (cutoffTwoTailSymbols allowed)
      ({s : Set X // s ∈ supportCopies A₀.ordered R.toRelStructure} → κ) := by
  let prep := Constructed
  letI := prep.insertionOrder
  letI : Finite (OldACarrierEdge A₀.ordered Target.toRelStructure) :=
    Finite.of_injective (fun e : OldACarrierEdge A₀.ordered Target.toRelStructure => e.1)
      Subtype.val_injective
  letI : Finite original.FirstWagon :=
    inferInstanceAs (Finite (Quotient (original.wagonSetoid (0 : Fin (tail.length + 1)).succ)))
  letI : Finite (Vertex (cutoffTwoChoices A₀ Target R original
      prep.localCopy prep.localStrong prep.localCover)) := by infer_instance
  refine CutoffTwoContraction.exists_shorterOrderWitness_of_originalBounds ht A₀ Target R
    enumerate original prep allowed κ ?_ prep.supportNonempty prep.supportCovers
    hOriginalParameters hOriginalCuts ?_ hOrder
  · exact ofLocalCopies_extendsOrder (enumerate := enumerate) localCopy localStrong localCover
      firstLinear templateCover targetCover hColour hCoordinates hEnumerate hXBlocks
  · intro ν c x hx
    exact ⟨.inl (.inr (Target.part x)), ⟨Target.part x, hx, rfl⟩, rfl⟩

end CutoffTwoContraction
end StructuralRamsey.Girth.TrainRecursiveWitness
