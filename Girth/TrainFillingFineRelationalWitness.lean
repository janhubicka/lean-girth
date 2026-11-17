import Girth.TrainFillingFineRelationalInputs
import Girth.TrainFillingRelationalLabelTransport
import Girth.ForestActualRecursiveSupport

set_option autoImplicit false

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure
open StructuralRamsey.Partite (System)

universe u v w
variable {L : RelLanguage.{u}} {A X V Y I : Type v} [LinearOrder A] [Finite A]

section FillingCore

variable (A₀ : RelStructure L A) (Target : System L.withOrder A V)
variable (R : RelStructure L.withOrder X) (H : UniformFillingData Y X)
variable (partX : X → A) (partY : Y → A) (lift : I → V ↪ Y)
variable (hTemplate : H.templateEdges = supportCopies A₀.ordered R)
variable (hTemplateFine : ∀ (a : Embedding A₀.ordered R) x, partX (a x) = x)
variable (hPlace : ∀ (f : H.OldEdge) x, partY (H.place f x) = partX x)

local notation "Small" => A₀.ordered

include partX hTemplate hTemplateFine hPlace in
private theorem generatedPart_inj :
    ∀ e ∈ H.generatedEdges, Set.InjOn partY e :=
  fun e he => (UniformFillingData.generatedEdge_fineParts Small R H partX partY
    hTemplate hTemplateFine hPlace e he).1

local notation "Core" => fineFillingCore A₀ Target (UniformFillingData.generatedEdges H)
  partY lift (generatedPart_inj A₀ R H partX partY hTemplate hTemplateFine hPlace)

include partX hTemplate hTemplateFine hPlace in
/-- The same fine relational core realizes every physical generated edge
and every designated original target of the filled system. -/
theorem exists_fineRelationalFillingCore
    (hPart : ∀ i x, partY (lift i x) = Target.part x)
    (hForward : PartiteOrderCompatible Target)
    (hPositive : ∀ r : L.Symbol, 0 < L.arity r)
    (hVertex : ∀ x : V, ∃ a : Embedding Small Target.toRelStructure, x ∈ copyCarrier a)
    (hFine : ∀ (a : Embedding Small Target.toRelStructure) u, Target.part (a u) = u)
    (hSupported : ∀ (r : L.Symbol) (z : Fin (L.arity r) → V),
      Target.rel (.inl r) z →
        ∃ a : Embedding Small Target.toRelStructure, ∀ k, z k ∈ copyCarrier a)
    (hImages : ∀ i (a : Embedding Small Target.toRelStructure),
      lift i '' copyCarrier a ∈ H.generatedEdges)
    (hStrong : ∀ i e, e ∈ H.generatedEdges → ∀ x y : V, x ≠ y →
      lift i x ∈ e → lift i y ∈ e →
      ∃ a : Embedding Small Target.toRelStructure, e = lift i '' copyCarrier a)
    (hAgree : ∀ (i j : I) (z w : Fin 2 → V), lift i ∘ z = lift j ∘ w →
      Target.rel (.inr ()) w → Target.rel (.inr ()) z)
    (r : L.Symbol) (z : Fin (L.arity r) → A) (hSpan : Function.Surjective z) (hz : A₀.rel r z) :
    ∃ (E : System L.withOrder A Y) (f : I → StructuralRamsey.Partite.Embedding Target E),
      E.part = partY ∧
      supportCopies Small E.toRelStructure = H.generatedEdges ∧
      (∀ i x, f i x = lift i x) ∧
      (∀ (a : Embedding Small E.toRelStructure) x, E.part (a x) = x) ∧
      FiniteMixedForestThrough (RelationalMixedSupportTest Small (fun i => (f i).toEmbedding)) 1 := by
  let hInj := generatedPart_inj A₀ R H partX partY hTemplate hTemplateFine hPlace
  have hOnto : ∀ e ∈ H.generatedEdges, ∀ a : A, ∃ y ∈ e, partY y = a :=
    fun e he => (UniformFillingData.generatedEdge_fineParts Small R H partX partY
      hTemplate hTemplateFine hPlace e he).2
  let f := fineFillingCore_lift A₀ Target H.generatedEdges partY lift hInj hPart hForward
    (finePartite_supportedRelations A₀ Target hFine hSupported)
    hPositive hVertex hFine hImages hStrong hAgree
  refine ⟨Core, f, rfl, ?_, fun _ _ => rfl, ?_, finiteMixedForestThrough_one _⟩
  · exact supportCopies_fineFillingCore A₀ Target H.generatedEdges partY lift
      hInj hOnto r z hSpan hz
  · exact fineFillingCore_fine A₀ Target H.generatedEdges partY lift hInj

end FillingCore
end StructuralRamsey.Girth
