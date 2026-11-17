import Girth.TrainFillingApplyShorterOrder
import Girth.TrainFillingConditionalCutoffTwoProjected

set_option autoImplicit false
set_option Elab.async false

namespace StructuralRamsey.Girth.TrainRecursiveWitness

open StructuralRamsey.RelStructure
open StructuralRamsey.Partite (System)
open StructuralRamsey.Girth.IndexedPrivateChoice

universe u v
variable {K : RelLanguage.{u}} {A V X C : Type v} {k : ℕ} {tail : List ℕ}
variable [LinearOrder A] [Finite A] [Nontrivial A] [Finite X] [Nontrivial X] [Finite C]

/-- Realize the actual shorter order witness and keep its finite selected
indices, its original cutoff bounds, and the original fine parts. -/
theorem cutoffTwoRawLocalData_of_shorterOrderWitness
    (ht : Admissible tail)
    (A₀ : RelStructure K A) (Target : System K.withOrder A V)
    (R : System K.withOrder A X) (enumerate : X ≃ ULift.{v} (Fin k))
    (original : EdgeTrainLevels (OldACarrierEdge A₀.ordered Target.toRelStructure) (tail.length + 1))
    (prep : CutoffTwoContraction (C := C) A₀ Target R enumerate original)
    (allowed : Fin (tail.length + 1 + 1) → Set A) (κ : Type v)
    [Nonempty (C × original.FirstWagon)]
    [Finite (Vertex (cutoffTwoChoices A₀ Target R original prep.localCopy prep.localStrong prep.localCover))]
    (hSourceFine : ∀ a : Embedding A₀.ordered Target.toRelStructure, ∀ u, Target.part (a u) = u)
    (hProjection : Target.toRelStructure.IsHomomorphism A₀.ordered Target.part)
    (hTargetEdge : Nonempty (Embedding A₀.ordered Target.toRelStructure))
    (hTemplateFine : ∀ (a : Embedding A₀.ordered R.toRelStructure) x, R.part (a x) = x)
    (hLocalPart : ∀ (c : C) (p : original.FirstWagon)
      (x : {v : V // v ∈ cutoffTwoFirstCarrier original Subtype.val p}),
      R.part (prep.localCopy c p x) = Target.part x.1)
    (hTemplateLinear : ALinear A₀.ordered R.toRelStructure)
    (hFirstParameter : ∀ e f : {s : Set X // s ∈ supportCopies A₀.ordered R.toRelStructure},
      e ≠ f → e.1 ∩ f.1 ⊆ R.part ⁻¹' allowed (0 : Fin (tail.length + 1)).succ)
    (hLocalArrow : ∀ word : {s : Set X // s ∈ supportCopies A₀.ordered R.toRelStructure} → κ,
      ∃ (c : C) (colour : κ), ∀ p : original.FirstWagon,
        ∀ e : {s : Set X // s ∈ supportCopies A₀.ordered R.toRelStructure},
          e ∈ selectedCommonEdges (cutoffTwoChoices A₀ Target R original
            prep.localCopy prep.localStrong prep.localCover)
            (supportCopies A₀.ordered R.toRelStructure) (fun _ => rfl) c p →
              word e = colour)
    (r : K.Symbol) (z : Fin (K.arity r) → A)
    (hSpan : Function.Surjective z) (hz : A₀.rel r z)
    (hShorter : UnrestrictedPredicateOrderWitness (cutoffTwoShortSource R.part enumerate)
      prep.system tail (prep.train (List.length_pos_iff.mpr ht.nonempty))
      (cutoffTwoTailSymbols allowed) ({s : Set X // s ∈ supportCopies A₀.ordered R.toRelStructure} → κ)) :
    ∃ (Y I : Type v) (_ : Finite Y) (_ : Finite I),
      Nonempty (CutoffTwoRawLocalData (Y := Y) (I := I) A₀.ordered Target tail original allowed κ) := by
  obtain ⟨Base, _, D, family, ⟨lower⟩⟩ := hShorter
  let hn := List.length_pos_iff.mpr ht.nonempty
  have hCutoff (j : Fin tail.length) : 2 ≤ tail.get j := ht.two_le _ (List.get_mem _ _)
  let core := exists_projectingCutoffTwoFilledCore_of_unrestrictedOrder hn A₀ Target R enumerate
    original prep D family (allowedByPredicates D (cutoffTwoTailSymbols allowed)) lower
    hSourceFine hProjection hTargetEdge hTemplateFine hLocalPart hCutoff r z hSpan hz
  let I := {b : DesignatedCopy prep.system D lower.system family // b ∈ lower.selected} × C
  have hFiniteParent : Finite
      {b : DesignatedCopy prep.system D lower.system family // b ∈ lower.selected} := by
    apply Finite.of_injective (fun b : {b : DesignatedCopy prep.system D lower.system family //
      b ∈ lower.selected} => b.1.embedding)
    intro a b hab
    exact lower.selectedPhysicalInjective (congrArg _ hab)
  have hFiniteIndex : Finite I := inferInstance
  exact ⟨lower.Vertex, I, lower.finiteVertex, hFiniteIndex,
    cutoffTwoRawData_of_filledCore hn A₀ Target R enumerate original prep D family allowed lower
      core hTemplateLinear hFirstParameter hLocalArrow⟩

end StructuralRamsey.Girth.TrainRecursiveWitness
