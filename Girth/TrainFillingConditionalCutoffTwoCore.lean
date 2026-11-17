import Girth.TrainFillingFineRelationalWitness
import Girth.TrainFillingOrderedFineProjection
import Girth.TrainFillingSelectedOriginalTargets
import Girth.TrainFillingOrderedSelectedTail
import Girth.TrainFillingContractFirstTrain
import Girth.TrainFillingRawCutoffTwoData
import Girth.TrainRecursiveCompatibleOrderResult

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

abbrev cutoffTwoFirstCarrier {E X : Type v} {m : ℕ}
    (T : EdgeTrainLevels E (m + 1)) (edge : E → Set X) :
    T.FirstWagon → Set X :=
  T.wagonClassCarrier edge (0 : Fin (m + 1)).succ

noncomputable def cutoffTwoChoices
    {K : RelLanguage.{u}} {A V X C : Type v} [LinearOrder A] {tail : List ℕ}
    (A₀ : RelStructure K A) (Target : System K.withOrder A V)
    (R : System K.withOrder A X)
    (original : EdgeTrainLevels (OldACarrierEdge A₀.ordered Target.toRelStructure)
      (tail.length + 1))
    (localCopy : ∀ (_ : C) (p : original.FirstWagon),
      Embedding (Target.toRelStructure.induce (cutoffTwoFirstCarrier original Subtype.val p))
        R.toRelStructure)
    (hLocalStrong : ∀ (c : C) (p : original.FirstWagon),
      AStrong A₀.ordered R.toRelStructure (copyCarrier (localCopy c p)))
    (hLocalCover : ∀ (p : original.FirstWagon)
      (x : {v : V // v ∈ cutoffTwoFirstCarrier original Subtype.val p}),
      ∃ a : Embedding A₀.ordered
        (Target.toRelStructure.induce (cutoffTwoFirstCarrier original Subtype.val p)), x ∈ copyCarrier a) :
    C → PrivateWagonInput V original.FirstWagon X :=
  fun c => privateChoiceOfLocalCopies A₀.ordered Target.toRelStructure R.toRelStructure
    (cutoffTwoFirstCarrier original Subtype.val) (localCopy c) (hLocalStrong c) hLocalCover

abbrev cutoffTwoShortSource {A X : Type v} {k : ℕ}
    (part : X → A) (enumerate : X ≃ ULift.{v} (Fin k)) :
    RelStructure (colouredOrderedEdgeLanguage A k).withOrder (ULift.{v} (Fin k)) :=
  (colouredOrderedEdgeSource k (fun i => part (enumerate.symm (ULift.up i)))).ordered

/-- The actual shortened target and its complete contracted support.
Each edge placement comes from the chosen induced first-wagon map. -/
structure CutoffTwoContraction
    {K : RelLanguage.{u}} {A V X C : Type v} {k : ℕ} {tail : List ℕ}
    [LinearOrder A]
    (A₀ : RelStructure K A) (Target : System K.withOrder A V)
    (R : System K.withOrder A X) (enumerate : X ≃ ULift.{v} (Fin k))
    (original : EdgeTrainLevels (OldACarrierEdge A₀.ordered Target.toRelStructure)
      (tail.length + 1)) where
  localCopy : ∀ (_ : C) (p : original.FirstWagon),
    Embedding (Target.toRelStructure.induce (cutoffTwoFirstCarrier original Subtype.val p))
      R.toRelStructure
  localStrong : ∀ (c : C) (p : original.FirstWagon),
    AStrong A₀.ordered R.toRelStructure (copyCarrier (localCopy c p))
  localCover : ∀ (p : original.FirstWagon)
    (x : {v : V // v ∈ cutoffTwoFirstCarrier original Subtype.val p}),
    ∃ a : Embedding A₀.ordered
      (Target.toRelStructure.induce (cutoffTwoFirstCarrier original Subtype.val p)), x ∈ copyCarrier a
  system : RelStructure (colouredOrderedEdgeLanguage A k).withOrder
    (Vertex (cutoffTwoChoices A₀ Target R original localCopy localStrong localCover))
  source : (C × original.FirstWagon) → Embedding (cutoffTwoShortSource R.part enumerate) system
  source_apply : ∀ (c : C) (p : original.FirstWagon) (x : X),
    source (c, p) (enumerate x) =
      tagVertex (cutoffTwoChoices A₀ Target R original localCopy localStrong localCover)
        c ((cutoffTwoChoices A₀ Target R original localCopy localStrong localCover c).place p x)
  support : supportCopies (cutoffTwoShortSource R.part enumerate) system =
    Set.range (contractedCarrier
      (cutoffTwoChoices A₀ Target R original localCopy localStrong localCover))
  firstLinear : ∀ (p q : original.FirstWagon), p ≠ q →
    (cutoffTwoFirstCarrier original Subtype.val p ∩ cutoffTwoFirstCarrier original Subtype.val q).Subsingleton
  templateCover : ∀ x : X, ∃ a : Embedding A₀.ordered R.toRelStructure, x ∈ copyCarrier a
  targetCover : ∀ x : V, ∃ a : Embedding A₀.ordered Target.toRelStructure, x ∈ copyCarrier a

namespace CutoffTwoContraction

variable (prep : CutoffTwoContraction (C := C) A₀ Target R enumerate original)

noncomputable def train :
    EdgeTrainLevels (OldACarrierEdge (cutoffTwoShortSource R.part enumerate) prep.system)
      tail.length :=
  contractedPhysicalTrain
    (cutoffTwoChoices A₀ Target R original prep.localCopy prep.localStrong prep.localCover)
    (cutoffTwoShortSource R.part enumerate) prep.system original.contractFirst ht prep.support
    (fun (_ : C) (p q : original.FirstWagon) (hne : p ≠ q) => prep.firstLinear p q hne)

end CutoffTwoContraction

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
/-- The canonical physical filling has the exact selected target vertex
maps, the exact fine parts on every edge, and two-point strongness. -/
theorem exists_cutoffTwoFillingGeometry
    (hTemplateFine : ∀ (a : Embedding Small Template) x, R.part (a x) = x)
    (hLocalPart : ∀ (c : C) (p : original.FirstWagon) (x : {v : V // v ∈ Carrier p}),
      R.part (localCopy c p x) = Target.part x.1) :
    ∃ (lift : Index → V ↪ lower.Vertex),
      (∀ (i : Index) (x : V), lift i x = i.1.1.embedding (tagVertex W i.2 (Sum.inl x))) ∧
      (∀ (i : Index) (x : V), FinePart (lift i x) = Target.part x) ∧
      (∀ (i : Index) (a : Embedding Small B), lift i '' copyCarrier a ∈ (Filling).generatedEdges) ∧
      (∀ (i : Index) (e : Set lower.Vertex), e ∈ (Filling).generatedEdges →
        ∀ x y : V, x ≠ y → lift i x ∈ e → lift i y ∈ e →
          ∃ a : Embedding Small B, e = lift i '' copyCarrier a) ∧
      (∀ (e : Set lower.Vertex), e ∈ (Filling).generatedEdges →
        Set.InjOn FinePart e ∧ ∀ a : A, ∃ y ∈ e, FinePart y = a) := by
  classical
  let hOldLinear : ∀ e f : {s : Set lower.Vertex // s ∈
      supportCopies (ShortSource).ordered (N).toRelStructure}, e ≠ f → (e.1 ∩ f.1).Subsingleton :=
    oldACarrier_edges_inter_subsingleton_of_aLinear (ShortSource).ordered (N).toRelStructure lower.aLinear
  let H := UniformFillingData.ofOrderedSupportCopies Small Template enumerate hOldLinear hTemplateCover
  let j₀ : Fin tail.length := ⟨0, ht⟩
  have hTemplate : ∀ c : C, (W c).templateEdges = supportCopies Small Template := fun _ => rfl
  let F := (orderedSelectedTailRealization W Small Template enumerate M source hSource hSupport
    FirstLinear D N family lower.selected lower.aLinear hTemplateCover hTemplate
    original.contractFirst ht lower.train lower.targetRestriction j₀).toParentwiseRealization
  let lift : Index → V ↪ lower.Vertex := F.targetVertexEmbedding
  let partY := orderedFillingPart (N).toRelStructure enumerate R.part lower.supportCovers
  have hPlace (g : H.OldEdge) (x : X) : partY (H.place g x) = R.part x :=
    orderedFillingPart_place (N).toRelStructure enumerate R.part lower.supportCovers g x
  have hOldCover : ∀ (_ : C) (x : V), ∃ p : original.FirstWagon, x ∈ Carrier p :=
    fun _ x => Exists.elim (prep.targetCover x)
      (fun (a : Embedding A₀.ordered Target.toRelStructure) (ha : x ∈ copyCarrier a) =>
      ⟨original.firstWagon (actualEdge a),
        original.edge_subset_ownerWagonCarrier Subtype.val
          (0 : Fin (tail.length + 1)).succ (actualEdge a) ha⟩)
  have hOwnerCarrier (e : OldACarrierEdge Small B) : e.1 ⊆ Carrier (original.firstWagon e) :=
    original.edge_subset_ownerWagonCarrier Subtype.val (0 : Fin (tail.length + 1)).succ e
  have hPart (i : Index) (x : V) : partY (lift i x) = Target.part x :=
    selectedOrdered_originalVertex_part W Small Template enumerate hOldLinear hTemplateCover
      FirstLinear M source hSource Target.part R.part partY hPlace hLocalPart hOldCover
      i.1.1.embedding i.2 x
  have hImages (i : Index) (a : Embedding Small B) : lift i '' copyCarrier a ∈ H.generatedEdges := by
    obtain ⟨s, _, _, hs⟩ := parentwise_originalEdge_target Small B Template Carrier localCopy
      hLocalStrong hLocalCover F original.firstWagon hOwnerCarrier hFirstLinear i a
    exact hs ▸ (F.edge i.1 (tagEdge W i.2 s)).2
  have hStrong (i : Index) (e : Set lower.Vertex) (he : e ∈ H.generatedEdges) (x y : V)
      (hxy : x ≠ y) (hx : lift i x ∈ e) (hy : lift i y ∈ e) :
      ∃ a : Embedding Small B, e = lift i '' copyCarrier a := by
    let ce : H.toTrainFilling.NewEdge := ⟨e, he⟩
    have hxT : lift i x ∈ F.targetCarrier i := by
      rw [← F.targetVertexEmbedding_range i]
      exact ⟨x, rfl⟩
    have hyT : lift i y ∈ F.targetCarrier i := by
      rw [← F.targetVertexEmbedding_range i]
      exact ⟨y, rfl⟩
    have heT : ce ∈ F.targetEdges i :=
      orderedSelectedTail_strong W Small Template enumerate M source hSource hSupport
        FirstLinear D N family lower.selected lower.aLinear hTemplateCover hTemplate
        original.contractFirst ht lower.train lower.targetRestriction lower.strong j₀ i.1 i.2
        ce (lift i x) (lift i y) (fun h => hxy ((lift i).injective h)) hx hy hxT hyT
    exact parentwise_targetEdge_original Small B Template Carrier localCopy
      hLocalStrong hLocalCover F i ce heT
  have hPartOnEdge (e : Set lower.Vertex) (he : e ∈ H.generatedEdges) :=
    UniformFillingData.generatedEdge_fineParts Small Template H R.part partY
      rfl hTemplateFine hPlace e he
  exact ⟨lift, fun _ _ => rfl, hPart, hImages, hStrong, hPartOnEdge⟩

/-- What the physical tail packaging needs from relational realization.
The incidence and train data are reconstructed from the same filling. -/
abbrev CutoffTwoFilledCore : Prop :=
    ∃ (E : System K.withOrder A lower.Vertex)
      (f : Index → StructuralRamsey.Partite.Embedding Target E),
      supportCopies Small E.toRelStructure = (Filling).generatedEdges ∧
      E.part = orderedFillingPart (N).toRelStructure enumerate R.part lower.supportCovers ∧
      (∀ (i : Index) (x : V), f i x = i.1.1.embedding (tagVertex W i.2 (Sum.inl x))) ∧
      (∀ (a : Embedding Small E.toRelStructure) x, E.part (a x) = x) ∧
      E.toRelStructure.IsHomomorphism Small E.part ∧
      FiniteMixedForestThrough (RelationalMixedSupportTest Small (fun (i : Index) => (f i).toEmbedding)) 1

include ht in
/-- The conditional cutoff-two core comes from the actual shorter order
witness. Its fine parts, complete physical support and original target
embeddings are derived from the same canonical filling. -/
theorem exists_fineCutoffTwoCore_of_unrestrictedOrder
    (hForward : PartiteOrderCompatible Target)
    (hPositive : ∀ r : K.Symbol, 0 < K.arity r)
    (hSourceFine : ∀ a : Embedding Small B, ∀ u, Target.part (a u) = u)
    (hSupported : ∀ (r : K.Symbol) (z : Fin (K.arity r) → V), Target.rel (.inl r) z →
      ∃ a : Embedding Small B, ∀ j, z j ∈ copyCarrier a)
    (hTemplateFine : ∀ (a : Embedding Small Template) x, R.part (a x) = x)
    (hLocalPart : ∀ (c : C) (p : original.FirstWagon) (x : {v : V // v ∈ Carrier p}),
      R.part (localCopy c p x) = Target.part x.1)
    (hCutoff : ∀ j : Fin tail.length, 2 ≤ tail.get j)
    (r : K.Symbol) (z : Fin (K.arity r) → A) (hSpan : Function.Surjective z) (hz : A₀.rel r z) :
    ∃ (E : System K.withOrder A lower.Vertex)
      (f : Index → StructuralRamsey.Partite.Embedding Target E),
      supportCopies Small E.toRelStructure = (Filling).generatedEdges ∧
      E.part = orderedFillingPart (N).toRelStructure enumerate R.part lower.supportCovers ∧
      (∀ (i : Index) (x : V), f i x = i.1.1.embedding (tagVertex W i.2 (Sum.inl x))) ∧
      (∀ (a : Embedding Small E.toRelStructure) x, E.part (a x) = x) ∧
      E.toRelStructure.IsHomomorphism Small E.part ∧
      FiniteMixedForestThrough (RelationalMixedSupportTest Small (fun (i : Index) => (f i).toEmbedding)) 1 := by
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
  have hAgree (i j : Index) (v w : Fin 2 → V) (hEq : lift i ∘ v = lift j ∘ w)
      (hw : Target.rel (.inr ()) w) : Target.rel (.inr ()) v :=
    selectedOrdered_agree_targetOrder W Small Template Target hForward enumerate D N M family
      lower.selected hOldLinear hTemplateCover FirstLinear source hSource hSupport
      localCopy (fun _ _ _ => rfl) lower.train (hCutoff j₀) hFullZero
      i.1 j.1 i.2 j.2 v w (fun idx =>
        (hLift i (v idx)).symm.trans ((congrFun hEq idx).trans (hLift j (w idx)))) hw
  let hInj := fun e he => (hPartOnEdge e he).1
  let E := fineFillingCore A₀ Target H.generatedEdges partY lift hInj
  let f := fineFillingCore_lift A₀ Target H.generatedEdges partY lift hInj hPart hForward
    (finePartite_supportedRelations A₀ Target hSourceFine hSupported)
    hPositive prep.targetCover hSourceFine hImages hStrong hAgree
  refine ⟨E, f, ?_, rfl, hLift, ?_, ?_, finiteMixedForestThrough_one _⟩
  · exact supportCopies_fineFillingCore A₀ Target H.generatedEdges partY lift hInj
      (fun e he => (hPartOnEdge e he).2) r z hSpan hz
  · exact fineFillingCore_fine A₀ Target H.generatedEdges partY lift hInj
  · intro s w hw
    cases s with
    | inl s => exact hw.1
    | inr s =>
      cases s
      exact hw.1

end StructuralRamsey.Girth.TrainRecursiveWitness
