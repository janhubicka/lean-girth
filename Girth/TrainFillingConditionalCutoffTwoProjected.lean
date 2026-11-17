import Girth.TrainFillingConditionalCutoffTwoCore
import Girth.TrainFillingRestoreSelectedRelations
import Girth.TrainFillingSelectedTupleOverlap

set_option autoImplicit false
set_option maxRecDepth 4000
set_option maxHeartbeats 0

namespace StructuralRamsey.Girth.TrainRecursiveWitness

open StructuralRamsey.RelStructure
open StructuralRamsey.Partite (System)
open StructuralRamsey.Girth.IndexedPrivateChoice

universe u v w

variable {K : RelLanguage.{u}} {A V X C Base : Type v} {κ : Type w}
variable [LinearOrder A] [Finite A] [Nontrivial A] [Nontrivial X]
variable {k : ℕ} {tail : List ℕ} (ht : 0 < tail.length)
variable (A₀ : RelStructure K A) (Target : System K.withOrder A V)
variable (R : System K.withOrder A X) (enumerate : X ≃ ULift.{v} (Fin k))

local notation "Small" => A₀.ordered
local notation "B" => Target.toRelStructure
local notation "Template" => R.toRelStructure
local notation "ShortLanguage" => colouredOrderedEdgeLanguage A k
local notation "ShortSource" =>
  colouredOrderedEdgeSource k (fun i => R.part (Equiv.symm enumerate (ULift.up i)))

variable (original : EdgeTrainLevels (OldACarrierEdge A₀.ordered Target.toRelStructure)
  (tail.length + 1))

variable (prep : CutoffTwoContraction (C := C) A₀ Target R enumerate original)
variable (D : RelStructure (colouredOrderedEdgeLanguage A k).withOrder Base)
variable (family : Set (Embedding prep.system D))
variable (allowed : Fin (tail.length + 1) → Set Base)
variable (lower : UnrestrictedOrderResult (cutoffTwoShortSource R.part enumerate)
  prep.system D family tail (CutoffTwoContraction.train (A₀ := A₀) (Target := Target) (R := R)
    (enumerate := enumerate) (original := original) ht prep) allowed
  ({s : Set X // s ∈ supportCopies A₀.ordered R.toRelStructure} → κ))

local notation "Carrier" => cutoffTwoFirstCarrier original (fun e : OldACarrierEdge Small B => Subtype.val e)
local notation "W" => cutoffTwoChoices A₀ Target R original prep.localCopy prep.localStrong prep.localCover
local notation "localCopy" => prep.localCopy
local notation "hLocalStrong" => prep.localStrong
local notation "hLocalCover" => prep.localCover
local notation "hTemplateCover" => prep.templateCover
local notation "hFirstLinear" => prep.firstLinear
local notation "M" => prep.system
local notation "source" => prep.source
local notation "hSource" => prep.source_apply
local notation "hSupport" => prep.support
local notation "FirstLinear" =>
  (fun (_ : C) (p q : original.FirstWagon) (h : p ≠ q) => prep.firstLinear p q h)

local notation "N" => lower.system
local notation "Parents" => {b : DesignatedCopy M D N family // b ∈ lower.selected}
local notation "Index" => Parents × C
local notation "Filling" => UniformFillingData.ofOrderedSupportCopies Small Template enumerate
  (oldACarrier_edges_inter_subsingleton_of_aLinear (RelStructure.ordered ShortSource)
    (System.toRelStructure N) lower.aLinear) hTemplateCover

local notation "FinePart" => orderedFillingPart (System.toRelStructure N) enumerate R.part lower.supportCovers

include ht in
/-- Realize the literal canonical filling over the original fine parts
with all original relations on every selected lift. -/
theorem exists_projectingCutoffTwoFilledCore_of_unrestrictedOrder
    (hSourceFine : ∀ a : Embedding Small B, ∀ u, Target.part (a u) = u)
    (hProjection : Target.toRelStructure.IsHomomorphism Small Target.part)
    (hTargetEdge : Nonempty (Embedding Small B))
    (hTemplateFine : ∀ (a : Embedding Small Template) x, R.part (a x) = x)
    (hLocalPart : ∀ (c : C) (p : original.FirstWagon) (x : {v : V // v ∈ Carrier p}),
      R.part (localCopy c p x) = Target.part x.1)
    (hCutoff : ∀ j : Fin tail.length, 2 ≤ tail.get j)
    (r : K.Symbol) (z : Fin (K.arity r) → A) (hSpan : Function.Surjective z) (hz : A₀.rel r z) :
    CutoffTwoFilledCore ht A₀ Target R enumerate original prep D family allowed lower := by
  classical
  let H := Filling
  let partY := FinePart
  let j₀ : Fin tail.length := ⟨0, ht⟩
  let hOldLinear := oldACarrier_edges_inter_subsingleton_of_aLinear
    (ShortSource).ordered (N).toRelStructure lower.aLinear
  obtain ⟨lift, hLift, hPart, hImages, hStrong, hPartOnEdge⟩ :=
    exists_cutoffTwoFillingGeometry ht A₀ Target R enumerate original prep D family allowed lower
      hTemplateFine hLocalPart
  have hFullZero : (selectedPictureOrderOneData
      (ShortSource).ordered M D N family lower.selected lower.train 0).FullSystemGirthGT
      (tail.get j₀) := lower.allCutGirth j₀
  have hAgree (i j : Index) (s : K.withOrder.Symbol) (v w : Fin (K.withOrder.arity s) → V)
      (hEq : lift i ∘ v = lift j ∘ w) (hw : Target.rel s w) : Target.rel s v :=
    (selectedOrdered_agree_targetRel W Small Template Target enumerate D N M family
      lower.selected hOldLinear hTemplateCover FirstLinear source hSource hSupport
      localCopy (fun _ _ _ => rfl) hSourceFine prep.targetCover hTargetEdge
      partY (fun b c x => (congrArg partY (hLift (b, c) x)).symm.trans (hPart (b, c) x))
      lower.train (hCutoff j₀) hFullZero i.1 j.1 i.2 j.2 s v w (fun idx =>
        (hLift i (v idx)).symm.trans ((congrFun hEq idx).trans (hLift j (w idx))))).mpr hw
  let hInj := fun e he => (hPartOnEdge e he).1
  let hOnto := fun e he => (hPartOnEdge e he).2
  let E := restoreSelectedFillingRelations A₀ Target H.generatedEdges partY lift hInj hPart
  let f := restoredFillingTarget A₀ Target H.generatedEdges partY lift hInj hPart
    hTargetEdge prep.targetCover hStrong hSourceFine hProjection hAgree
  refine ⟨E, f, ?_, rfl, hLift, ?_, ?_, finiteMixedForestThrough_one _⟩
  · exact supportCopies_restoreSelectedFillingRelations A₀ Target H.generatedEdges partY lift
      hInj hPart hOnto hTargetEdge prep.targetCover hStrong hSourceFine hProjection hAgree
      hImages r z hSpan hz
  · exact restoredFillingCore_fine A₀ Target H.generatedEdges partY lift hInj hPart
  · exact restoreSelectedFillingRelations_projects A₀ Target H.generatedEdges partY lift hInj hPart

end StructuralRamsey.Girth.TrainRecursiveWitness
