import Girth.TrainRecursiveGlobalAllowedCompatibility

set_option autoImplicit false
set_option Elab.async false

/-!
# Widening allowed parts without changing a selected forest/order stage

The actual ForestTailStage stores its allowed-part parameters ONLY through
the train's adjacent-sibling intersection condition. All geometric and
Ramsey data (vertices, ambient A-edges, designated labels, mixed forests,
positive system girth and selected arrows) are independent of that parameter.

Therefore the existing physical stage can be retyped with LARGER allowed
sets. This is helpful in the unrestricted same-vector conversion: if one
constructed stage has allowedD contained in the canonical coarse-predicate
allowed parts, no second Ramsey construction is needed to use canonical
allowed parts. The whole original ambient hypergraph is retained.

The result does not prove that an arbitrary stage's allowedD satisfies the
canonical containment. That is a separate parameter-compatibility gate.
-/

namespace StructuralRamsey.Girth.TrainRecursiveWitness

open StructuralRamsey.RelStructure

universe u v w
variable {L : RelLanguage.{u}} {UA VB P : Type v}

/-- Increasing the permitted sibling-intersection sets cannot invalidate
an actual adjacent-parameter bound. The train and physical edge map are
unchanged. -/
theorem EdgeTrainLevels.adjacentParameters_monoAllowed
    {E V : Type v} {m : ℕ}
    (T : EdgeTrainLevels E m)
    (edge : E → Set V)
    (oldAllowed newAllowed : Fin (m + 1) → Set V)
    (hIncl : ∀ ν, oldAllowed ν ⊆ newAllowed ν)
    (hOld : T.AdjacentParameters edge oldAllowed) :
    T.AdjacentParameters edge newAllowed := by
  intro μ ν hμν hSucc a b hNe hParent x hx
  exact hIncl ν (hOld μ ν hμν hSucc hNe hParent hx)

/-- Retype the *same* physical forest stage with weaker (larger)
permitted-intersection constraints. None of the system, train or
selected-copy fields changes. -/
def ForestTailStage.widenAllowed
    {A : RelStructure L UA} {B : RelStructure L VB}
    {D : RelStructure L P}
    {family : Set (Embedding B D)} {t : List ℕ}
    {targetTrain : EdgeTrainLevels (OldACarrierEdge A B) t.length}
    {oldAllowed : Fin (t.length + 1) → Set P}
    (S : ForestTailStage A B D family t targetTrain oldAllowed)
    (newAllowed : Fin (t.length + 1) → Set P)
    (hIncl : ∀ ν, oldAllowed ν ⊆ newAllowed ν) :
    ForestTailStage A B D family t targetTrain newAllowed where
  Vertex := S.Vertex
  finiteVertex := S.finiteVertex
  system := S.system
  isPartite := S.isPartite
  aLinear := S.aLinear
  supportNonempty := S.supportNonempty
  supportCovers := S.supportCovers
  selected := S.selected
  selectedPhysicalInjective := S.selectedPhysicalInjective
  mixedCoverage := S.mixedCoverage
  strong := S.strong
  train := S.train
  targetRestriction := S.targetRestriction
  parameters := by
    apply S.train.adjacentParameters_monoAllowed
      (fun edge => edge.1)
      (fun ν => S.system.part ⁻¹' oldAllowed ν)
      (fun ν => S.system.part ⁻¹' newAllowed ν)
    · intro ν x hx
      exact hIncl ν hx
    · exact S.parameters
  bottomForest := S.bottomForest
  tailGirth := S.tailGirth

/-- The same construction preserves the order-level system-girth
certificate at EVERY cut because it leaves the physical stage and
selected literal labels unchanged. -/
def OrderStage.widenAllowed
    {A : RelStructure L UA} {B : RelStructure L VB}
    {D : RelStructure L P}
    {family : Set (Embedding B D)} {t : List ℕ}
    {targetTrain : EdgeTrainLevels (OldACarrierEdge A B) t.length}
    {oldAllowed : Fin (t.length + 1) → Set P}
    (S : OrderStage A B D family t targetTrain oldAllowed)
    (newAllowed : Fin (t.length + 1) → Set P)
    (hIncl : ∀ ν, oldAllowed ν ⊆ newAllowed ν) :
    OrderStage A B D family t targetTrain newAllowed where
  toForestTailStage :=
    S.toForestTailStage.widenAllowed newAllowed hIncl
  allCutGirth := S.allCutGirth

/-- The existing selected Ramsey arrow is literally unchanged by
allowed-part widening. The chosen target embeddings and physical
source copy labels stay the same. -/
theorem DesignatedArrow.widenAllowed
    {A : RelStructure L UA} {B : RelStructure L VB}
    {D : RelStructure L P}
    {family : Set (Embedding B D)} {t : List ℕ}
    {targetTrain : EdgeTrainLevels (OldACarrierEdge A B) t.length}
    {oldAllowed : Fin (t.length + 1) → Set P}
    (S : ForestTailStage A B D family t targetTrain oldAllowed)
    (κ : Type w) (newAllowed : Fin (t.length + 1) → Set P)
    (hIncl : ∀ ν, oldAllowed ν ⊆ newAllowed ν)
    (hArrow : DesignatedArrow S κ) :
    DesignatedArrow (S.widenAllowed newAllowed hIncl) κ :=
  hArrow

/-- Therefore a genuinely selected order witness with allowedD lying
inside the original coarse-predicate permitted sets may be retyped to
canonical allowedD without any additional combinatorial witness.
This is conditional on actual global containment (or its derivation
from selected coverage/physical contact geometry). -/
theorem OrderStage.withCanonicalCoarseAllowed
    {A : RelStructure L UA} {B : RelStructure L VB}
    {D : RelStructure L P}
    {family : Set (Embedding B D)} {t : List ℕ}
    {targetTrain : EdgeTrainLevels (OldACarrierEdge A B) t.length}
    {oldAllowed : Fin (t.length + 1) → Set P}
    (S : OrderStage A B D family t targetTrain oldAllowed)
    (κ : Type w)
    (predD : P → Q) (permitted : Fin (t.length + 1) → Set Q)
    (hCanonical : ∀ ν,
      oldAllowed ν ⊆ canonicalCoarseAllowed predD permitted ν)
    (hArrow : DesignatedArrow S.toForestTailStage κ) :
    ∃ S' : OrderStage A B D family t targetTrain
        (canonicalCoarseAllowed predD permitted),
      DesignatedArrow S'.toForestTailStage κ := by
  refine ⟨S.widenAllowed
    (canonicalCoarseAllowed predD permitted) hCanonical, ?_⟩
  exact DesignatedArrow.widenAllowed S.toForestTailStage κ
    (canonicalCoarseAllowed predD permitted) hCanonical hArrow

end StructuralRamsey.Girth.TrainRecursiveWitness
