import Girth.TrainRecursiveWitnessPass
import Girth.TrainRecursiveAllowedPredicates
import Girth.LabelledWagonCutRestriction

set_option autoImplicit false
set_option Elab.async false

/-!
# The genuinely unrestricted order input needed at cutoff two

The shorter train in the manuscript is of a NEW coloured edge type X
(possibly with repeated coarse vertex predicates). It is not generally
X-partite: different X coordinates on two first-wagon edges can be
identified at an original common vertex.

Hence type- and palette-uniform PARTITE order assertions do not
supply the unrestricted RR_tail input. The critical path retains
only the genuine universal PARTITE FOREST q>2 theorem and defines
the independent unrestricted selected-order assertion below.

The order assertion allows a nonpartite target B with an extendible
order, and it takes the original unary predicates that determine the
allowed contact sets. Its output may use a new large base D supporting
a prescribed family of embeddings B to D.

The output stores the selected train and its cut bounds. The filling
construction uses these fields independently of the stronger ordered
partiteness or coverage of arbitrary irreducible subsets.
-/

namespace StructuralRamsey.Girth.TrainRecursiveWitness

open StructuralRamsey.RelStructure

universe u v w
variable {UA VB : Type v}

/-- Selected order data consumed by shorter-train filling. -/
structure UnrestrictedOrderResult
    {L : RelLanguage.{u}} {P : Type v}
    (A : RelStructure L UA) (B : RelStructure L VB)
    (D : RelStructure L P) (family : Set (Embedding B D)) (t : List ℕ)
    (targetTrain : EdgeTrainLevels (OldACarrierEdge A B) t.length)
    (allowed : Fin (t.length + 1) → Set P) (κ : Type w) where
  Vertex : Type v
  finiteVertex : Finite Vertex
  system : StructuralRamsey.Partite.System L P Vertex
  projectsACopies : ∀ a : Embedding A system.toRelStructure,
    ∃ b : Embedding A D, ∀ x : UA, b x = system.part (a x)
  aLinear : ALinear A system.toRelStructure
  supportNonempty : Nonempty (OldACarrierEdge A system.toRelStructure)
  supportCovers : ∀ x : Vertex,
    ∃ e : OldACarrierEdge A system.toRelStructure, x ∈ e.1
  selected : Set (DesignatedCopy B D system family)
  selectedPhysicalInjective : Function.Injective
    (fun b : {b : DesignatedCopy B D system family // b ∈ selected} =>
      bSupportPiece A b.1.embedding)
  strong : ∀ b : DesignatedCopy B D system family, b ∈ selected →
    AStrong A system.toRelStructure (copyCarrier b.embedding)
  train : EdgeTrainLevels (OldACarrierEdge A system.toRelStructure) t.length
  targetRestriction : ∀ b : DesignatedCopy B D system family, b ∈ selected →
    ∀ μ : Fin (t.length + 1), ∀ a₁ a₂ : Embedding A B,
      train.rel μ (actualEdge (b.embedding.comp a₁))
        (actualEdge (b.embedding.comp a₂)) ↔
      targetTrain.rel μ (actualEdge a₁) (actualEdge a₂)
  parameters : train.AdjacentParameters (fun edge => edge.1)
    (fun ν => system.part ⁻¹' allowed ν)
  allCutGirth : ∀ j : Fin t.length,
    (selectedPictureOrderOneData A B D system family selected train j.castSucc).FullSystemGirthGT
      (t.get j)
  arrow : ∀ χ : Embedding A system.toRelStructure → κ,
    ∃ b : DesignatedCopy B D system family, b ∈ selected ∧
      ∀ a₁ a₂ : Embedding A B, χ (b.embedding.comp a₁) = χ (b.embedding.comp a₂)

attribute [instance] UnrestrictedOrderResult.finiteVertex

/-- Forget the stronger partiteness and mixed-coverage fields of a complete
selected order stage while retaining its exact selected train and arrow. -/
def UnrestrictedOrderResult.ofOrderStage
    {L : RelLanguage.{u}} {P : Type v}
    {A : RelStructure L UA} {B : RelStructure L VB}
    {D : RelStructure L P} {family : Set (Embedding B D)} {t : List ℕ}
    {targetTrain : EdgeTrainLevels (OldACarrierEdge A B) t.length}
    {allowed : Fin (t.length + 1) → Set P} {κ : Type w}
    (hA : A.Irreducible)
    (S : OrderStage A B D family t targetTrain allowed)
    (hArrow : DesignatedArrow S.toForestTailStage κ) :
    UnrestrictedOrderResult A B D family t targetTrain allowed κ where
  Vertex := S.Vertex
  finiteVertex := S.finiteVertex
  system := S.system
  projectsACopies := S.isPartite.after_irreducible_embedding hA
  aLinear := S.aLinear
  supportNonempty := S.supportNonempty
  supportCovers := S.supportCovers
  selected := S.selected
  selectedPhysicalInjective := S.selectedPhysicalInjective
  strong := S.strong
  train := S.train
  targetRestriction := S.targetRestriction
  parameters := S.parameters
  allCutGirth := S.allCutGirth
  arrow := hArrow

/-- The permitted base parts pull back to the original predicates of
the actual witness, since every vertex lies in a projected source copy. -/
theorem UnrestrictedOrderResult.adjacentParameters_allowedByPredicates
    {L : RelLanguage.{u}} {P : Type v}
    {A : RelStructure L.withOrder UA} {B : RelStructure L.withOrder VB}
    {D : RelStructure L.withOrder P} {family : Set (Embedding B D)} {t : List ℕ}
    {targetTrain : EdgeTrainLevels (OldACarrierEdge A B) t.length} {κ : Type w}
    (symbols : Fin (t.length + 1) → Set L.Symbol)
    (S : UnrestrictedOrderResult A B D family t targetTrain
      (allowedByPredicates D symbols) κ) :
    S.train.AdjacentParameters (fun edge => edge.1)
      (allowedByPredicates S.system.toRelStructure symbols) := by
  have hAllowed (ν : Fin (t.length + 1)) :
      S.system.part ⁻¹' allowedByPredicates D symbols ν =
        allowedByPredicates S.system.toRelStructure symbols ν := by
    ext y
    obtain ⟨edge, hy⟩ := S.supportCovers y
    obtain ⟨a, ha⟩ := edge.2
    change edge.1 = copyCarrier a at ha
    rw [ha] at hy
    obtain ⟨x, rfl⟩ := hy
    obtain ⟨b, hb⟩ := S.projectsACopies a
    change S.system.part (a x) ∈ allowedByPredicates D symbols ν ↔
      a x ∈ allowedByPredicates S.system.toRelStructure symbols ν
    rw [← hb x]
    change x ∈ b ⁻¹' allowedByPredicates D symbols ν ↔
      x ∈ a ⁻¹' allowedByPredicates S.system.toRelStructure symbols ν
    rw [allowedByPredicates_pullback b, allowedByPredicates_pullback a]
  simpa only [hAllowed] using S.parameters

/-- A result whose contact sets are determined by the original predicates
on the witness, independently of which target copies cover a contact. -/
def UnrestrictedPredicateOrderWitness
    {L : RelLanguage.{u}} (A : RelStructure L.withOrder UA)
    (B : RelStructure L.withOrder VB) (t : List ℕ)
    (targetTrain : EdgeTrainLevels (OldACarrierEdge A B) t.length)
    (symbols : Fin (t.length + 1) → Set L.Symbol) (κ : Type w) : Prop :=
  ∃ (P : Type v) (_ : Finite P) (D : RelStructure L.withOrder P)
      (family : Set (Embedding B D)),
    Nonempty (UnrestrictedOrderResult A B D family t targetTrain
      (allowedByPredicates D symbols) κ)

/-- Arbitrary finite target B: unlike the invalid identity-base proposal,
the conclusion allows a sufficiently large finite base D and a real
prescribed family of B-embeddings. No global A-part map on B is required. -/
def UniformCompatibleUnrestrictedOrderAllInputs
    (L : RelLanguage.{u}) (t : List ℕ) : Prop :=
  ∀ {UA : Type v} [LinearOrder UA] [Finite UA] [Nonempty UA] [Nontrivial UA]
    (A₀ : RelStructure L UA)
    (κ : Type) [Fintype κ] [Nonempty κ]
    {VB : Type v} [Finite VB] [LinearOrder VB]
    (B : RelStructure L.withOrder VB)
    (hExtends : B.ExtendsOrder)
    (ht : Admissible t)
    (targetTrain : EdgeTrainLevels
      (OldACarrierEdge A₀.ordered B) t.length)
    (symbols : Fin (t.length + 1) → Set L.Symbol)
    (hSupportNonempty : Nonempty
      (OldACarrierEdge A₀.ordered B))
    (hSupportCovers : ∀ x : VB,
      ∃ a : OldACarrierEdge A₀.ordered B, x ∈ a.1)
    (hGirth : GirthGT
      (supportCopies A₀.ordered B) (t.headD 0))
    (hParameters : targetTrain.AdjacentParameters
      (fun e => e.1) (allowedByPredicates B symbols))
    (hTargetCuts : ∀ j : Fin t.length, 0 < j.val →
      LabelledGirthGT
        (targetTrain.wagonClassCarrier (fun e => e.1) j.castSucc)
        (t.get j)),
    UnrestrictedPredicateOrderWitness A₀.ordered B t targetTrain symbols κ

/-- The smaller-rank unrestricted order assertion applies to a NEW
finite edge structure and a finite power palette, without imposing
an A-partite structure on the arbitrary shorter target B. -/
theorem UniformCompatibleUnrestrictedOrderAllInputs.finPower
    (L : RelLanguage.{u}) (t : List ℕ)
    (h : UniformCompatibleUnrestrictedOrderAllInputs.{u, v} L t)
    (A₀ : RelStructure L UA)
    [LinearOrder UA] [Finite UA] [Nonempty UA] [Nontrivial UA]
    (B : RelStructure L.withOrder VB) [Finite VB] [LinearOrder VB]
    (hExtends : B.ExtendsOrder)
    (ht : Admissible t)
    (targetTrain : EdgeTrainLevels
      (OldACarrierEdge A₀.ordered B) t.length)
    (symbols : Fin (t.length + 1) → Set L.Symbol)
    (hSupportNonempty : Nonempty
      (OldACarrierEdge A₀.ordered B))
    (hSupportCovers : ∀ x : VB,
      ∃ a : OldACarrierEdge A₀.ordered B, x ∈ a.1)
    (hGirth : GirthGT
      (supportCopies A₀.ordered B) (t.headD 0))
    (hParameters : targetTrain.AdjacentParameters
      (fun e => e.1) (allowedByPredicates B symbols))
    (hTargetCuts : ∀ j : Fin t.length, 0 < j.val →
      LabelledGirthGT
        (targetTrain.wagonClassCarrier (fun e => e.1) j.castSucc)
        (t.get j))
    (r n : ℕ) (hr : 0 < r) :
    UnrestrictedPredicateOrderWitness A₀.ordered B t targetTrain symbols (Fin (r ^ n)) := by
  letI : Nonempty (Fin (r ^ n)) := ⟨⟨0, pow_pos hr n⟩⟩
  exact h A₀ (Fin (r ^ n)) B hExtends ht targetTrain symbols
    hSupportNonempty hSupportCovers hGirth hParameters hTargetCuts

/-- The literal cutoff-two colour palette of *words* of length n is
already a finite nonempty type. Unlike a cardinality-only r^n encoding,
this specialization keeps the actual complete edge-colour function:
the only extra choice in the filling proof is a finite enumeration of
the old edges of X. No numeric coding or power equivalence is needed. -/
theorem UniformCompatibleUnrestrictedOrderAllInputs.finColourWords
    (L : RelLanguage.{u}) (t : List ℕ)
    (h : UniformCompatibleUnrestrictedOrderAllInputs.{u, v} L t)
    (A₀ : RelStructure L UA)
    [LinearOrder UA] [Finite UA] [Nonempty UA] [Nontrivial UA]
    (B : RelStructure L.withOrder VB) [Finite VB] [LinearOrder VB]
    (hExtends : B.ExtendsOrder)
    (ht : Admissible t)
    (targetTrain : EdgeTrainLevels
      (OldACarrierEdge A₀.ordered B) t.length)
    (symbols : Fin (t.length + 1) → Set L.Symbol)
    (hSupportNonempty : Nonempty
      (OldACarrierEdge A₀.ordered B))
    (hSupportCovers : ∀ x : VB,
      ∃ a : OldACarrierEdge A₀.ordered B, x ∈ a.1)
    (hGirth : GirthGT
      (supportCopies A₀.ordered B) (t.headD 0))
    (hParameters : targetTrain.AdjacentParameters
      (fun e => e.1) (allowedByPredicates B symbols))
    (hTargetCuts : ∀ j : Fin t.length, 0 < j.val →
      LabelledGirthGT
        (targetTrain.wagonClassCarrier (fun e => e.1) j.castSucc)
        (t.get j))
    (r n : ℕ) (hr : 0 < r) :
    UnrestrictedPredicateOrderWitness A₀.ordered B t targetTrain symbols (Fin n → Fin r) := by
  classical
  letI : Nonempty (Fin n → Fin r) :=
    ⟨fun _ => ⟨0, hr⟩⟩
  exact h A₀ (Fin n → Fin r) B hExtends ht targetTrain symbols
    hSupportNonempty hSupportCovers hGirth hParameters hTargetCuts

end StructuralRamsey.Girth.TrainRecursiveWitness
