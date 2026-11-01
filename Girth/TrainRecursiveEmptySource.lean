import Girth.TrainRecursiveFreshRefinementPass
import Girth.ForestDisjoint

set_option Elab.async false
set_option autoImplicit false

/-!
# The actual empty-source stage and a source-unrestricted fresh pass

The disjoint initial train uses a nonempty source to recover the component
of a physical A-edge.  That argument cannot distinguish empty copies in
different components.  The covered-target hypotheses nevertheless admit
a direct empty-source case: coverage forces the target vertex type to be
empty as well.

For that case, the stage below is the target itself, projected along one
actual member of the prescribed base family.  Its selected copy is the
literal identity target copy and its train is exactly the original target
train.  It satisfies every forest bound and full simultaneous system-girth
bound, and its selected Ramsey arrow holds for any colour type.

Splitting off this constructed stage removes the source-nonemptiness
assumption from the target-cut freshness facade.  The nonempty case still
uses the existing finite pass and its explicit fresh nontrivial operator.
-/

namespace StructuralRamsey.Girth.TrainRecursiveWitness

open StructuralRamsey.RelStructure

universe u v w
variable {L : RelLanguage.{u}} {UA VB P : Type v}

/-- If the source is empty, coverage by its actual support edges forces
the target itself to be empty.  The support edge is retained, not deleted. -/
theorem isEmpty_target_of_emptySource_supportCovers
    (A : RelStructure L UA) [IsEmpty UA] (B : RelStructure L VB)
    (hCover : ∀ b : VB, ∃ e : OldACarrierEdge A B, b ∈ e.1) :
    IsEmpty VB := by
  refine ⟨?_⟩
  intro b
  obtain ⟨e, hb⟩ := hCover b
  obtain ⟨a, ha⟩ := e.2
  rw [ha] at hb
  obtain ⟨u, _⟩ := hb
  exact isEmptyElim u

private theorem fullSystemGirth_of_empty_vertices
    {V E I W : Type v} [IsEmpty V] [Subsingleton W]
    (D : OrderOneData V E I W) (q : ℕ) : D.FullSystemGirthGT q := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro _ _ _ x _ _ _
    exact isEmptyElim x
  · intro _ _ _ x _ _ _
    exact isEmptyElim x
  · intro n C _ _
    let zero : Fin n := ⟨0, by have := C.length_ge_two; omega⟩
    let one : Fin n := ⟨1, by have := C.length_ge_two; omega⟩
    have hConnector : C.connector zero = C.connector one := by
      cases hz : C.connector zero with
      | inl x => exact isEmptyElim x
      | inr p =>
        cases ho : C.connector one with
        | inl x => exact isEmptyElim x
        | inr r => exact congrArg Sum.inr (Subsingleton.elim p r)
    have hIndex := congrArg Fin.val (C.connector_injective hConnector)
    change 0 = 1 at hIndex
    exact (Nat.zero_ne_one hIndex).elim

private def targetSystemOverBase
    (B : RelStructure L VB) (D : RelStructure L P) (b : Embedding B D) :
    StructuralRamsey.Partite.System L P VB where
  toRelStructure := B
  part := b
  transversal := fun _ _ _ _ _ h => b.injective h

private def targetIdentityCopy
    (B : RelStructure L VB) (D : RelStructure L P)
    (family : Set (Embedding B D)) (b : family) :
    DesignatedCopy B D (targetSystemOverBase B D b.1) family :=
  ⟨b.1, b.2, ⟨Embedding.id B, fun _ => rfl⟩⟩

/-- A complete actual order stage for an empty source and a covered target.
Its vertices and relations are exactly the target's, its projection is the
given base-family embedding, and its sole selected copy is the identity.
No local step, girth input, admissibility, or nonempty colour type is needed. -/
noncomputable def emptySourceOrderStage
    (A : RelStructure L UA) [IsEmpty UA]
    (B : RelStructure L VB) (D : RelStructure L P)
    (family : Set (Embedding B D)) (b : family)
    (t : List ℕ)
    (targetTrain : EdgeTrainLevels (OldACarrierEdge A B) t.length)
    (allowed : Fin (t.length + 1) → Set P)
    (hSupportNonempty : Nonempty (OldACarrierEdge A B))
    (hSupportCovers : ∀ x : VB, ∃ e : OldACarrierEdge A B, x ∈ e.1) :
    OrderStage A B D family t targetTrain allowed := by
  classical
  letI : IsEmpty VB := isEmpty_target_of_emptySource_supportCovers A B hSupportCovers
  letI : Subsingleton (OldACarrierEdge A B) :=
    ⟨fun e f => Subtype.ext (Set.ext fun x => isEmptyElim x)⟩
  let C := targetSystemOverBase B D b.1
  let selectedCopy := targetIdentityCopy B D family b
  have hFull : ∀ (μ : Fin (t.length + 1)) (q : ℕ),
      (selectedPictureOrderOneData A B D C family {selectedCopy}
        targetTrain μ).FullSystemGirthGT q := by
    intro μ q
    have hClasses : Subsingleton (Quotient (targetTrain.wagonSetoid μ)) := by
      refine ⟨fun p r => Quotient.inductionOn₂ p r ?_⟩
      intro e f
      apply Quotient.sound
      change targetTrain.rel μ e f
      have hef : e = f := Subsingleton.elim e f
      subst f
      exact (targetTrain.equivalent μ).refl e
    exact @fullSystemGirth_of_empty_vertices _ _ _ _ inferInstance hClasses
      (selectedPictureOrderOneData A B D C family {selectedCopy} targetTrain μ) q
  refine {
    Vertex := VB
    finiteVertex := inferInstance
    system := C
    isPartite := b.1.isHomomorphismEmbedding
    aLinear := ?_
    supportNonempty := hSupportNonempty
    supportCovers := hSupportCovers
    selected := {selectedCopy}
    selectedPhysicalInjective := ?_
    mixedCoverage := ?_
    strong := ?_
    train := targetTrain
    targetRestriction := ?_
    parameters := ?_
    bottomForest := ?_
    tailGirth := fun j _ => hFull j.castSucc (t.get j)
    allCutGirth := fun j => hFull j.castSucc (t.get j)
  }
  · intro _ _ _ x _ _ _
    exact isEmptyElim x
  · intro a c _
    apply Subtype.ext
    exact a.2.trans c.2.symm
  · intro S _
    exact Or.inl ⟨selectedCopy, rfl, fun z => isEmptyElim z.1⟩
  · intro _ _ _ _ x _
    exact isEmptyElim x
  · intro c hc μ a₁ a₂
    have hc' : c = selectedCopy := hc
    subst c
    rfl
  · apply targetTrain.adjacentParameters_of_matching (fun edge => edge.1)
    intro e f _
    exact Set.disjoint_left.mpr (fun x _ _ => isEmptyElim x)
  · intro s _ _
    by_cases hs : Nonempty {piece : HypergraphPiece VB // piece ∈ s}
    · let := hs
      exact forestOfCopies_of_disjoint
        (fun {_ _} _ => Set.disjoint_left.mpr (fun x _ _ => isEmptyElim x))
    · have hEmpty : IsEmpty {piece : HypergraphPiece VB // piece ∈ s} :=
        ⟨fun piece => hs ⟨piece⟩⟩
      exact ⟨fun {i _} _ => (hEmpty.false i).elim, Or.inl hEmpty⟩

/-- The same actual empty-source stage has a selected monochromatic target
copy for every colouring, because two embeddings with empty domain agree. -/
theorem emptySourceOrderStage_designatedArrow
    (A : RelStructure L UA) [IsEmpty UA]
    (B : RelStructure L VB) (D : RelStructure L P)
    (family : Set (Embedding B D)) (b : family)
    (t : List ℕ)
    (targetTrain : EdgeTrainLevels (OldACarrierEdge A B) t.length)
    (allowed : Fin (t.length + 1) → Set P)
    (hSupportNonempty : Nonempty (OldACarrierEdge A B))
    (hSupportCovers : ∀ x : VB, ∃ e : OldACarrierEdge A B, x ∈ e.1)
    (κ : Type w) :
    DesignatedArrow (emptySourceOrderStage A B D family b t targetTrain allowed
      hSupportNonempty hSupportCovers).toForestTailStage κ := by
  intro χ
  refine ⟨targetIdentityCopy B D family b, rfl, ?_⟩
  intro a₁ a₂
  have hEq : a₁ = a₂ := Embedding.ext (fun u => isEmptyElim u)
  rw [hEq]

/-- The empty-source case supplies a genuine complete finite stage and its
literal selected arrow, retaining the original target train and base label. -/
theorem exists_orderStage_designatedArrow_of_emptySource
    (A : RelStructure L UA) [IsEmpty UA]
    (B : RelStructure L VB) (D : RelStructure L P)
    (family : Set (Embedding B D)) (b : family)
    (t : List ℕ)
    (targetTrain : EdgeTrainLevels (OldACarrierEdge A B) t.length)
    (allowed : Fin (t.length + 1) → Set P)
    (hSupportNonempty : Nonempty (OldACarrierEdge A B))
    (hSupportCovers : ∀ x : VB, ∃ e : OldACarrierEdge A B, x ∈ e.1)
    (κ : Type w) :
    ∃ S : OrderStage A B D family t targetTrain allowed,
      DesignatedArrow S.toForestTailStage κ := by
  exact ⟨emptySourceOrderStage A B D family b t targetTrain allowed
    hSupportNonempty hSupportCovers,
    emptySourceOrderStage_designatedArrow A B D family b t targetTrain allowed
      hSupportNonempty hSupportCovers κ⟩

section OrderedPass

variable (A₀ : RelStructure L UA) [LinearOrder UA] [Finite UA]
local notation "A" => A₀.ordered

/-- The target-cut freshness facade for every finite ordered source.  For
an empty source, construct the actual target stage above; otherwise run the
existing repetition-free pass.  Both branches return the same selected
ForestTailStage arrow, with no weakened witness or cycle predicate. -/
theorem constructFromTargetCuts_of_freshNontrivialRefiningSteps_allowEmpty
    (B : RelStructure L.withOrder VB) [Finite VB]
    (D : RelStructure L.withOrder P) [Finite P]
    (family : Set (Embedding B D))
    (t : List ℕ) (ht : Admissible t)
    (targetTrain : EdgeTrainLevels (OldACarrierEdge A B) t.length)
    (allowed : Fin (t.length + 1) → Set P)
    (hSupportNonempty : Nonempty (OldACarrierEdge A B))
    (hSupportCovers : ∀ b : VB, ∃ e : OldACarrierEdge A B, b ∈ e.1)
    (hGirth : GirthGT (supportCopies A B) (t.headD 0))
    (hTargetParameters : ∀ b : family,
      targetTrain.AdjacentParameters (fun edge => edge.1)
        (fun ν => b.1 ⁻¹' allowed ν))
    (hTargetCuts : ∀ j : Fin t.length, 0 < j.val →
      LabelledGirthGT
        (targetTrain.wagonClassCarrier (fun edge => edge.1) j.castSucc)
        (t.get j))
    (refinementBudget : ℕ) (κ : Type w) [Nonempty κ]
    (hBase : ∀ χ : Embedding A D → κ,
      ∃ b : Embedding B D, b ∈ family ∧
        ∀ a₁ a₂ : Embedding A B, χ (b.comp a₁) = χ (b.comp a₂))
    (actualStep : ∀ (e : Embedding A D) (remaining : List (UA ↪ P))
      (S : ForestTailStage A B D family t targetTrain allowed),
      e.toFunctionEmbedding ∉ remaining →
      (∃ a b : StructuralRamsey.Partite.ProjectedEmbedding A S.system
        e.toFunctionEmbedding, copyCarrier a.val ≠ copyCarrier b.val) →
      ForestTailStage.FirstRefinementReady (List.length_pos_iff.mpr ht.nonempty)
        refinementBudget (e.toFunctionEmbedding :: remaining) S →
        ∃ T : ForestTailStage A B D family t targetTrain allowed,
          ForestTailStage.FirstRefinementReady (List.length_pos_iff.mpr ht.nonempty)
            refinementBudget remaining T ∧ PictureStep S T e.toFunctionEmbedding κ) :
    ∃ T : ForestTailStage A B D family t targetTrain allowed,
      DesignatedArrow T κ := by
  classical
  by_cases hSource : Nonempty UA
  · let := hSource
    exact constructFromTargetCuts_of_freshNontrivialRefiningSteps A₀ B D family
      t ht targetTrain allowed hSupportNonempty hSupportCovers hGirth
      hTargetParameters hTargetCuts refinementBudget κ hBase actualStep
  · let : IsEmpty UA := ⟨fun u => hSource ⟨u⟩⟩
    obtain ⟨b, hb⟩ := baseFamily_nonempty_of_arrow A B D family κ hBase
    obtain ⟨S, hS⟩ := exists_orderStage_designatedArrow_of_emptySource A B D
      family ⟨b, hb⟩ t targetTrain allowed hSupportNonempty hSupportCovers κ
    exact ⟨S.toForestTailStage, hS⟩

end OrderedPass

end StructuralRamsey.Girth.TrainRecursiveWitness
