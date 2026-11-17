import Girth.TrainFillingConditionalCutoffTwoRaw
import Girth.TrainRecursiveColouredShorterOrder
import Girth.TrainFillingShortenedOriginalBounds
import Girth.TrainFillingOrderedShortenedSupport

set_option autoImplicit false
set_option Elab.async false

namespace StructuralRamsey.Girth.TrainRecursiveWitness

open StructuralRamsey.RelStructure
open StructuralRamsey.Partite (System)
open CoverageFree.Physical

universe u v
variable {K : RelLanguage.{u}} {A V X C : Type v} {k : ℕ} {tail : List ℕ}
variable [LinearOrder A] [Finite A] [Nontrivial A] [Finite X] [Nontrivial X]

/-- Apply the strictly shorter unrestricted order theorem to the actual
contracted train, with the literal word of template-edge colours. -/
theorem CutoffTwoContraction.exists_shorterOrderWitness
    (ht : Admissible tail)
    (A₀ : RelStructure K A) (Target : System K.withOrder A V)
    (R : System K.withOrder A X) (enumerate : X ≃ ULift.{v} (Fin k))
    (original : EdgeTrainLevels (OldACarrierEdge A₀.ordered Target.toRelStructure)
      (tail.length + 1))
    (prep : CutoffTwoContraction (C := C) A₀ Target R enumerate original)
    (allowed : Fin (tail.length + 1 + 1) → Set A)
    (κ : Type v) [Fintype κ] [Nonempty κ]
    [Finite (IndexedPrivateChoice.Vertex (cutoffTwoChoices
      A₀ Target R original prep.localCopy prep.localStrong prep.localCover))]
    [LinearOrder (IndexedPrivateChoice.Vertex (cutoffTwoChoices
      A₀ Target R original prep.localCopy prep.localStrong prep.localCover))]
    (hExtends : prep.system.ExtendsOrder)
    (hSupportNonempty : Nonempty (OldACarrierEdge (cutoffTwoShortSource R.part enumerate) prep.system))
    (hSupportCovers : ∀ x, ∃ e : OldACarrierEdge
      (cutoffTwoShortSource R.part enumerate) prep.system, x ∈ e.1)
    (hAdjacent : (prep.train (List.length_pos_iff.mpr ht.nonempty)).AdjacentParameters
      Subtype.val (allowedByPredicates prep.system (cutoffTwoTailSymbols allowed)))
    (hCuts : ∀ j : Fin tail.length, LabelledGirthGT
      ((prep.train (List.length_pos_iff.mpr ht.nonempty)).wagonClassCarrier Subtype.val j.castSucc)
      (tail.get j))
    (hOrder : ProjectedOrderEverySpanningType.{v, v} tail) :
    UnrestrictedPredicateOrderWitness (cutoffTwoShortSource R.part enumerate) prep.system tail
      (prep.train (List.length_pos_iff.mpr ht.nonempty)) (cutoffTwoTailSymbols allowed)
      ({s : Set X // s ∈ supportCopies A₀.ordered R.toRelStructure} → κ) :=
  shorterOrder_of_colouredTarget ht R.part enumerate prep.system hExtends
    (prep.train (List.length_pos_iff.mpr ht.nonempty)) (cutoffTwoTailSymbols allowed)
    (supportCopies A₀.ordered R.toRelStructure) κ hSupportNonempty hSupportCovers
    hAdjacent hCuts hOrder

/-- The actual shortened ordered theorem can be used with the original
positive-cut hypotheses. The old tagged contacts keep their fine unary
predicate in the contracted auxiliary structure. -/
theorem CutoffTwoContraction.exists_shorterOrderWitness_of_originalBounds
    (ht : Admissible tail)
    (A₀ : RelStructure K A) (Target : System K.withOrder A V)
    (R : System K.withOrder A X) (enumerate : X ≃ ULift.{v} (Fin k))
    (original : EdgeTrainLevels (OldACarrierEdge A₀.ordered Target.toRelStructure)
      (tail.length + 1))
    (prep : CutoffTwoContraction (C := C) A₀ Target R enumerate original)
    (allowed : Fin (tail.length + 1 + 1) → Set A)
    (κ : Type v) [Fintype κ] [Nonempty κ]
    [Finite (IndexedPrivateChoice.Vertex (cutoffTwoChoices
      A₀ Target R original prep.localCopy prep.localStrong prep.localCover))]
    [LinearOrder (IndexedPrivateChoice.Vertex (cutoffTwoChoices
      A₀ Target R original prep.localCopy prep.localStrong prep.localCover))]
    (hExtends : prep.system.ExtendsOrder)
    (hSupportNonempty : Nonempty (OldACarrierEdge (cutoffTwoShortSource R.part enumerate) prep.system))
    (hSupportCovers : ∀ x, ∃ e : OldACarrierEdge
      (cutoffTwoShortSource R.part enumerate) prep.system, x ∈ e.1)
    (hOriginalParameters : original.AdjacentParameters Subtype.val
      (fun ν => Target.part ⁻¹' allowed ν))
    (hOriginalCuts : ∀ j : Fin tail.length, LabelledGirthGT
      (original.wagonClassCarrier Subtype.val j.castSucc.succ) (tail.get j))
    (hContact : ∀ (ν : Fin (tail.length + 1)) (c : C) (x : V),
      Target.part x ∈ allowed ν.succ →
        IndexedPrivateChoice.tagVertex (cutoffTwoChoices A₀ Target R original
          prep.localCopy prep.localStrong prep.localCover) c (Sum.inl x) ∈
            allowedByPredicates prep.system (cutoffTwoTailSymbols allowed) ν)
    (hOrder : ProjectedOrderEverySpanningType.{v, v} tail) :
    UnrestrictedPredicateOrderWitness (cutoffTwoShortSource R.part enumerate) prep.system tail
      (prep.train (List.length_pos_iff.mpr ht.nonempty)) (cutoffTwoTailSymbols allowed)
      ({s : Set X // s ∈ supportCopies A₀.ordered R.toRelStructure} → κ) := by
  let W := cutoffTwoChoices A₀ Target R original prep.localCopy prep.localStrong prep.localCover
  let hLength : 0 < tail.length := List.length_pos_iff.mpr ht.nonempty
  have hCarrier (c : C) : (W c).oldCarrier =
      original.wagonClassCarrier Subtype.val (0 : Fin (tail.length + 1)).succ := rfl
  have hLinear (c : C) (p q : original.FirstWagon) (hne : p ≠ q) :
      ((W c).oldCarrier p ∩ (W c).oldCarrier q).Subsingleton :=
    prep.firstLinear p q hne
  apply CutoffTwoContraction.exists_shorterOrderWitness ht A₀ Target R enumerate original prep allowed κ
    hExtends hSupportNonempty hSupportCovers ?_ ?_ hOrder
  · exact IndexedPrivateChoice.shortenedOriginal_adjacentParameters original hLength
      Subtype.val W hCarrier (cutoffTwoShortSource R.part enumerate) prep.system
      prep.support hLinear (fun ν => Target.part ⁻¹' allowed ν)
      (allowedByPredicates prep.system (cutoffTwoTailSymbols allowed)) hOriginalParameters hContact
  · intro j
    exact IndexedPrivateChoice.shortenedOriginal_labelledCutGirth original hLength
      Subtype.val W hCarrier (cutoffTwoShortSource R.part enumerate) prep.system
      prep.support hLinear j.castSucc (tail.get j) (hOriginalCuts j)

/-- Original tagged vertices keep their unary fine predicate in the
actual short relational presentation. -/
theorem orderedShortenedTarget_oldContact
    {P : Type v} (W : C → PrivateWagonInput V P X)
    [LinearOrder C] [LinearOrder V] [Fintype V] [LinearOrder P] [LinearOrder X]
    (oldPart : V → A) (templatePart : X → A)
    (allowed : Fin (tail.length + 1 + 1) → Set A)
    (ν : Fin (tail.length + 1)) (c : C) (x : V)
    (h : oldPart x ∈ allowed ν.succ) :
    IndexedPrivateChoice.tagVertex W c (Sum.inl x) ∈
      allowedByPredicates (IndexedPrivateChoice.orderedShortenedTarget (k := k) W oldPart templatePart)
        (cutoffTwoTailSymbols allowed) ν := by
  exact ⟨.inl (.inr (oldPart x)), ⟨oldPart x, h, rfl⟩, rfl⟩

end StructuralRamsey.Girth.TrainRecursiveWitness
