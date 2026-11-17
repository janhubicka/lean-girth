import Girth.TrainFillingConditionalCutoffTwoCore

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
variable (allowedFine : Fin (tail.length + 1 + 1) → Set A)

def cutoffTwoTailSymbols {A : Type v} {k m : ℕ}
    (parts : Fin (m + 1 + 1) → Set A) (ν : Fin (m + 1)) :
    Set (colouredOrderedEdgeLanguage A k).Symbol :=
  (fun a : A => Sum.inl (Sum.inr a)) '' parts ν.succ
variable (lower : UnrestrictedOrderResult (cutoffTwoShortSource R.part enumerate)
  prep.system D family tail (CutoffTwoContraction.train (A₀ := A₀) (Target := Target) (R := R)
    (enumerate := enumerate) (original := original) ht prep)
  (allowedByPredicates D (cutoffTwoTailSymbols allowedFine))
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

include ht in
/-- Recover the actual train, girth bounds and arrow from the canonical
physical filling of the literal selected target maps. -/
theorem cutoffTwoRawData_of_filledCore
    [Nonempty (C × original.FirstWagon)]
    (hCore : CutoffTwoFilledCore ht A₀ Target R enumerate original prep D family
      (allowedByPredicates D (cutoffTwoTailSymbols allowedFine)) lower)
    (hTemplateLinear : ALinear Small Template)
    (hFirstParameter : ∀ e f : {s : Set X // s ∈ supportCopies Small Template},
      e ≠ f → e.1 ∩ f.1 ⊆ R.part ⁻¹' allowedFine (0 : Fin (tail.length + 1)).succ)
    (hLocalArrow : ∀ word : {s : Set X // s ∈ supportCopies Small Template} → κ,
      ∃ (c : C) (colour : κ), ∀ p : original.FirstWagon, ∀ e : {s : Set X // s ∈ supportCopies Small Template},
        e ∈ selectedCommonEdges W (supportCopies Small Template) (fun _ => rfl) c p →
          word e = colour) :
    Nonempty (CutoffTwoRawLocalData (Y := lower.Vertex) (I := Index)
      Small Target tail original allowedFine κ) := by
  classical
  let symbols (ν : Fin (tail.length + 1)) : Set (ShortLanguage).Symbol :=
    cutoffTwoTailSymbols allowedFine ν
  obtain ⟨E, f, hSupportExact, hPart, hf, hFine, hProjection, hForest⟩ := hCore
  let H := Filling
  let filled := H.toTrainFilling.inheritedTrain lower.train
  have hFamily : supportCopies Small E.toRelStructure = H.toTrainFilling.newEdges := hSupportExact
  let U : EdgeTrainLevels (OldACarrierEdge Small E.toRelStructure) (tail.length + 1) :=
    filled.transportCarrierFamily hFamily.symm
  let g (ce : H.toTrainFilling.NewEdge) : OldACarrierEdge Small E.toRelStructure :=
    ⟨ce.1, by
      change ce.1 ∈ supportCopies Small E.toRelStructure
      rw [hFamily]
      exact ce.2⟩
  let oldLabel (a : OldACarrierEdge Small E.toRelStructure) : H.toTrainFilling.NewEdge :=
    ⟨a.1, by
      change a.1 ∈ H.toTrainFilling.newEdges
      rw [← hFamily]
      exact a.2⟩
  let j₀ : Fin tail.length := ⟨0, ht⟩
  have hTemplate : ∀ c : C, (W c).templateEdges = supportCopies Small Template := fun _ => rfl
  let F (j : Fin tail.length) :=
    (orderedSelectedTailRealization W Small Template enumerate M source hSource hSupport
      FirstLinear D N family lower.selected lower.aLinear hTemplateCover hTemplate
      original.contractFirst ht lower.train lower.targetRestriction j).toParentwiseRealization
  have hStrong (j : Fin tail.length) (i : Index) (ce : H.toTrainFilling.NewEdge)
      (x y : lower.Vertex) (hxy : x ≠ y) (hx : x ∈ ce.1) (hy : y ∈ ce.1)
      (hi : x ∈ (F j).targetCarrier i) (hj : y ∈ (F j).targetCarrier i) :
      ce ∈ (F j).targetEdges i :=
    orderedSelectedTail_strong W Small Template enumerate M source hSource hSupport
      FirstLinear D N family lower.selected lower.aLinear hTemplateCover hTemplate
      original.contractFirst ht lower.train lower.targetRestriction lower.strong j i.1 i.2
      ce x y hxy hx hy hi hj
  have hOwnerCarrier (e : OldACarrierEdge Small B) : e.1 ⊆ Carrier (original.firstWagon e) :=
    original.edge_subset_ownerWagonCarrier Subtype.val (0 : Fin (tail.length + 1)).succ e
  have hCarrier (j : Fin tail.length) (i : Index) :
      copyCarrier (f i).toEmbedding = (F j).targetCarrier i := by
    rw [← (F j).targetVertexEmbedding_range i]
    exact congrArg Set.range (funext (hf i))
  have hImage (j : Fin tail.length) (i : Index) (a : Embedding Small B) :
      ∃ e : (W i.2).Edge, e.1 = original.firstWagon (actualEdge a) ∧
        (F j).edge i.1 (tagEdge W i.2 e) ∈ (F j).targetEdges i ∧
        g ((F j).edge i.1 (tagEdge W i.2 e)) = actualEdge ((f i).toEmbedding.comp a) := by
    obtain ⟨e, he, hMem, hEq⟩ := parentwise_originalEdge_target Small B Template Carrier
      localCopy hLocalStrong hLocalCover (F j) original.firstWagon hOwnerCarrier hFirstLinear i a
    refine ⟨e, he, hMem, Subtype.ext ?_⟩
    exact hEq.trans ((congrArg (fun β : V → lower.Vertex => β '' copyCarrier a)
      (funext (fun x => (hf i x).symm))).trans
      (UniformPrivateTemplate.image_copyCarrier_comp Small B E.toRelStructure (f i).toEmbedding a))
  have hLinear : ALinear Small E.toRelStructure := by
    apply aLinear_of_oldACarrier_edges_inter_subsingleton
    intro a b hNe
    exact H.generated_linear
      (oldACarrier_edges_inter_subsingleton_of_aLinear Small Template hTemplateLinear)
      (oldLabel a) (oldLabel b)
      (fun h => hNe (Subtype.ext (congrArg (fun ce : H.toTrainFilling.NewEdge => ce.1) h)))
  refine ⟨{
    system := E
    selected := f
    train := U
    projection := hProjection
    supportNonempty := ?_
    supportCovers := ?_
    fineEdges := hFine
    aLinear := hLinear
    strong := ?_
    predecessor := hForest
    selectedTrain := ?_
    parameters := ?_
    positive := ?_
    arrow := ?_
  }⟩
  · obtain ⟨e⟩ := lower.supportNonempty
    obtain ⟨x, _, _⟩ := exists_pair_ne X
    obtain ⟨a, _⟩ := hTemplateCover x
    exact ⟨g (H.edgeEquiv (e, ⟨copyCarrier a, ⟨a, rfl⟩⟩))⟩
  · intro y
    obtain ⟨e, he⟩ := lower.supportCovers y
    obtain ⟨ce, _, hce⟩ := H.toTrainFilling.covering e y he
    exact ⟨g ce, hce⟩
  · intro i a hMeet
    obtain ⟨x, hx, y, hy, hxy⟩ := Set.not_subsingleton_iff.mp hMeet
    let ce := oldLabel (actualEdge a)
    have hxT : x ∈ (F j₀).targetCarrier i := hCarrier j₀ i ▸ hx.2
    have hyT : y ∈ (F j₀).targetCarrier i := hCarrier j₀ i ▸ hy.2
    have hMem := hStrong j₀ i ce x y hxy hx.1 hy.1 hxT hyT
    obtain ⟨b, hb⟩ := parentwise_targetEdge_original Small B Template Carrier localCopy
      hLocalStrong hLocalCover (F j₀) i ce hMem
    have hCopy : copyCarrier a = (F j₀).targetVertexEmbedding i '' copyCarrier b := hb
    rw [hCarrier j₀ i, ← (F j₀).targetVertexEmbedding_range i, hCopy]
    exact Set.image_subset_range _ _
  · intro μ i a b
    obtain ⟨e, he, _, hCopyE⟩ := hImage j₀ i a
    obtain ⟨d, hd, _, hCopyD⟩ := hImage j₀ i b
    rw [← hCopyE, ← hCopyD]
    refine (EdgeTrainLevels.transportCarrierFamily_rel hFamily.symm filled μ _ _).trans ?_
    refine Fin.cases ?_ (fun ν => ?_) μ
    · refine (filled.bottom _ _).trans (Iff.trans ?_ (original.bottom _ _).symm)
      have hE : ((F j₀).edge i.1 (tagEdge W i.2 e)).1 =
          (f i).toEmbedding.toFunctionEmbedding '' copyCarrier a :=
        (congrArg Subtype.val hCopyE).trans
          (UniformPrivateTemplate.image_copyCarrier_comp Small B E.toRelStructure (f i).toEmbedding a).symm
      have hD : ((F j₀).edge i.1 (tagEdge W i.2 d)).1 =
          (f i).toEmbedding.toFunctionEmbedding '' copyCarrier b :=
        (congrArg Subtype.val hCopyD).trans
          (UniformPrivateTemplate.image_copyCarrier_comp Small B E.toRelStructure (f i).toEmbedding b).symm
      constructor
      · intro h
        apply Subtype.ext
        apply Set.image_injective.mpr ((f i).toEmbedding.injective)
        exact hE.symm.trans ((congrArg Subtype.val h).trans hD)
      · intro h
        apply Subtype.ext
        exact hE.trans ((congrArg (fun ce : OldACarrierEdge Small B =>
          (f i).toEmbedding.toFunctionEmbedding '' ce.1) h).trans hD.symm)
    · rw [← original.contractFirst_rel_firstWagon ν, ← he, ← hd]
      exact orderedSelectedFilledEdge_rel_succ W Small Template enumerate M source hSource hSupport
        FirstLinear D N family lower.selected lower.aLinear hTemplateCover hTemplate
        original.contractFirst ht lower.train lower.targetRestriction i.1 i.2 ν e d
  · let partY := orderedFillingPart (N).toRelStructure enumerate R.part lower.supportCovers
    have hOld : lower.train.AdjacentParameters Subtype.val (fun ν => partY ⁻¹' allowedFine ν.succ) := by
      have hEq (ν : Fin (tail.length + 1)) :
          allowedByPredicates (N).toRelStructure symbols ν = partY ⁻¹' allowedFine ν.succ := by
        ext y
        constructor
        · rintro ⟨_, ⟨p, hp, rfl⟩, hpred⟩
          have hPartEq := (shortenedHasPart_iff_part_eq (N).toRelStructure enumerate R.part
            lower.supportCovers y p).mp hpred
          change partY y = p at hPartEq
          change partY y ∈ allowedFine ν.succ
          rw [hPartEq]
          exact hp
        · intro hy
          exact ⟨_, ⟨partY y, hy, rfl⟩,
            (shortenedHasPart_iff_part_eq (N).toRelStructure enumerate R.part lower.supportCovers
              y (partY y)).mpr rfl⟩
      have hParam := lower.adjacentParameters_allowedByPredicates symbols
      rw [funext hEq] at hParam
      exact hParam
    rw [hPart]
    apply (EdgeTrainLevels.transportCarrierFamily_adjacentParameters hFamily.symm filled _).mpr
    exact orderedFilling_adjacentParameters Small Template enumerate N lower.aLinear
      hTemplateCover lower.train R.part partY allowedFine
      (orderedFillingPart_place (N).toRelStructure enumerate R.part lower.supportCovers)
      hFirstParameter hOld
  · intro j
    apply (EdgeTrainLevels.transportCarrierFamily_fullSystemGirthGT hFamily.symm filled
      (fun i => copyCarrier (f i).toEmbedding) j.castSucc.succ (tail.get j)).mpr
    have hBound := orderedSelectedTail_fullSystemGirthGT W Small Template enumerate M source
      hSource hSupport FirstLinear D N family lower.selected lower.aLinear hTemplateCover hTemplate
      original.contractFirst ht lower.train lower.targetRestriction hTemplateLinear lower.allCutGirth j
    have hData : (F j).designatedFamily.target =
        filled.carrierCutData (fun i => copyCarrier (f i).toEmbedding) j.castSucc.succ := by
      have hCarriers : (F j).targetCarrier = fun i => copyCarrier (f i).toEmbedding :=
        funext (fun i => (hCarrier j i).symm)
      have hEdges : (F j).targetEdges = fun i =>
          {e : H.toTrainFilling.NewEdge | e.1 ⊆ copyCarrier (f i).toEmbedding} := by
        funext i
        rw [(F j).targetEdges_eq_contained i H.generatedEdge_has_distinct_pair (hStrong j i),
          ← hCarrier j i]
        rfl
      change ({
        edgeCarrier := Subtype.val
        copyCarrier := (F j).targetCarrier
        copyEdges := (F j).targetEdges
        parent := Quotient.mk (filled.wagonSetoid j.castSucc.succ) } :
          OrderOneData lower.Vertex H.toTrainFilling.NewEdge Index _) = _
      rw [hCarriers, hEdges] <;> rfl
    exact hData ▸ hBound
  · intro χ
    have hArrow : ∀ col : Embedding (ShortSource).ordered (N).toRelStructure →
        {s : Set X // s ∈ supportCopies Small Template} → κ,
        ∃ i : Parents, ∀ a b : Embedding (ShortSource).ordered M,
          col (i.1.embedding.comp a) = col (i.1.embedding.comp b) := by
      intro col
      obtain ⟨i, hi, hc⟩ := lower.arrow col
      exact ⟨⟨i, hi⟩, hc⟩
    obtain ⟨i, c, colour, hMono⟩ := orderedSelectedTail_ramsey W Small Template enumerate M
      source hSource hSupport FirstLinear D N family lower.selected lower.aLinear
      hTemplateCover hTemplate original.contractFirst ht lower.train lower.targetRestriction
      hArrow hLocalArrow j₀ (χ ∘ g)
    refine ⟨(i, c), fun a b => ?_⟩
    obtain ⟨e, _, he, hE⟩ := hImage j₀ (i, c) a
    obtain ⟨d, _, hd, hD⟩ := hImage j₀ (i, c) b
    rw [← hE, ← hD]
    exact (hMono _ he).trans (hMono _ hd).symm

include ht in
/-- Carry the actual shorter-order witness through the canonical filling
and into the local cutoff-two predecessor data. The local increment is
not assumed as a property of the filled witness. -/
theorem cutoffTwoRawData_of_unrestrictedOrder
    [Nonempty (C × original.FirstWagon)]
    (hForward : PartiteOrderCompatible Target)
    (hPositive : ∀ r : K.Symbol, 0 < K.arity r)
    (hSourceFine : ∀ a : Embedding Small B, ∀ u, Target.part (a u) = u)
    (hSupported : ∀ (r : K.Symbol) (z : Fin (K.arity r) → V), Target.rel (.inl r) z →
      ∃ a : Embedding Small B, ∀ j, z j ∈ copyCarrier a)
    (hTemplateFine : ∀ (a : Embedding Small Template) x, R.part (a x) = x)
    (hLocalPart : ∀ (c : C) (p : original.FirstWagon) (x : {v : V // v ∈ Carrier p}),
      R.part (localCopy c p x) = Target.part x.1)
    (hCutoff : ∀ j : Fin tail.length, 2 ≤ tail.get j)
    (r : K.Symbol) (z : Fin (K.arity r) → A) (hSpan : Function.Surjective z) (hz : A₀.rel r z)
    (hTemplateLinear : ALinear Small Template)
    (hFirstParameter : ∀ e f : {s : Set X // s ∈ supportCopies Small Template},
      e ≠ f → e.1 ∩ f.1 ⊆ R.part ⁻¹' allowedFine (0 : Fin (tail.length + 1)).succ)
    (hLocalArrow : ∀ word : {s : Set X // s ∈ supportCopies Small Template} → κ,
      ∃ (c : C) (colour : κ), ∀ p : original.FirstWagon, ∀ e : {s : Set X // s ∈ supportCopies Small Template},
        e ∈ selectedCommonEdges W (supportCopies Small Template) (fun _ => rfl) c p →
          word e = colour) :
    Nonempty (CutoffTwoRawLocalData (Y := lower.Vertex) (I := Index)
      Small Target tail original allowedFine κ) :=
  cutoffTwoRawData_of_filledCore ht A₀ Target R enumerate original prep D family allowedFine lower
    (exists_fineCutoffTwoCore_of_unrestrictedOrder ht A₀ Target R enumerate original prep D family _
      lower hForward hPositive hSourceFine hSupported hTemplateFine hLocalPart hCutoff r z hSpan hz)
    hTemplateLinear hFirstParameter hLocalArrow

end StructuralRamsey.Girth.TrainRecursiveWitness
