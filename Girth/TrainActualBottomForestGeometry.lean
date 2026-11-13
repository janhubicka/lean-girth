import Girth.TrainBottomNormalizedNoMixed
import Girth.TrainSelectedCycleGeometricOwners
import Girth.ForestToSupremeActualGeometry

set_option autoImplicit false
set_option Elab.async false

/-!
# The genuine attached-picture bottom incidence model

At the equality cut, the attached selected-copy system has the physical
BottomForestGeometry provided the full attachment A-support is linear.
The more general geometric owner relation is *definitionally identical*
to the bottom minimum-owner relation with the actual attached standard
carriers and exact shared core edge map. This is a type-level adapter;
it does not assume or conclude new system girth.
-/

namespace StructuralRamsey.Girth
open StructuralRamsey.RelStructure

universe u v

section ActualBottomGeometry

variable {L : RelLanguage.{u}} {UA VB P X Y I : Type v}
variable (A : RelStructure L UA) (hA : A.Irreducible)
variable (B : RelStructure L VB) (D : RelStructure L P)
variable (C : StructuralRamsey.Partite.System L P X)
variable (family : Set (RelStructure.Embedding B D))
variable (selected : Set (DesignatedCopy B D C family))
variable (e : RelStructure.Embedding A D) (R : RelStructure L Y)
variable (f : I → RelStructure.Embedding
  (C.toRelStructure.induce (activeCarrier A C e.toFunctionEmbedding)) R)
variable {m : ℕ}
variable (T : EdgeTrainLevels (OldACarrierEdge A C.toRelStructure) m)
variable (U : EdgeTrainLevels (OldACarrierEdge A R) m)
variable (hShared : ∀ _i : I, Nonempty
  (SharedOldACarrierEdge A C.toRelStructure
    (activeCarrier A C e.toFunctionEmbedding)))

local notation "S" => activeCarrier A C e.toFunctionEmbedding
local notation "Actual" => RelStructure.Attachment.attach C.toRelStructure S R f
local notation "ActualEdge" => OldACarrierEdge A Actual
local notation "CoreEdge" => OldACarrierEdge A R
local notation "Std" => RelStructure.Attachment.copyEmbedding C.toRelStructure S R f
local notation "Emb" => sharedOldACarrierCoreEmbedding A C.toRelStructure S R f
local notation "Eqv" => actualAPictureEdgeEquiv A hA C.toRelStructure S R f
local notation "CoreActual" => (fun (b : CoreEdge) =>
  Eqv (physicalCoreEdge (sharedOldACarrierInclusion A C.toRelStructure S) I b))
local notation "Train" => generatedActualASupportTrain
  A hA C.toRelStructure S R f T U hShared
local notation "μBottom" => (⟨0, Nat.zero_lt_succ m⟩ : Fin (m + 1))
local notation "Out" => attachedSelectedPictureOrderOneData
  A hA B D C family selected e R f T U hShared μBottom
local notation "GeomAllowed" => selectedOutputGeometricOwnerAllowed
  A hA B D C family selected e R f T U hShared μBottom

/-- The full output at bottom, with every ambient A-edge retained, has
the actual bottom forest incidence geometry. The sole hypergraph
input is output A-linearity; the wagon equality comes from Train.bottom. -/
theorem attachedSelectedPicture_bottomForestGeometry
    [Nontrivial UA] (hLinear : ALinear A Actual) :
    (Out).BottomForestGeometry where
  edge_subset := by
    intro a edge hEdge
    cases a with
    | inl q => exact hEdge
    | inr other =>
        have hEq : edge = other := hEdge
        subst other
        exact Set.Subset.rfl
  edge_nontrivial := by
    intro edge
    obtain ⟨a, ha⟩ := edge.2
    change edge.1.Nontrivial
    rw [ha]
    obtain ⟨u, v, huv⟩ := exists_pair_ne UA
    exact ⟨a u, ⟨u, rfl⟩, a v, ⟨v, rfl⟩,
      fun h => huv (a.injective h)⟩
  edge_linear := by
    intro edge edge' hne
    obtain ⟨a, ha⟩ := edge.2
    obtain ⟨b, hb⟩ := edge'.2
    have hCopies : ¬ SameCopy a b := by
      intro h
      apply hne
      exact Subtype.ext (ha.trans (h.trans hb.symm))
    change (edge.1 ∩ edge'.1).Subsingleton
    rw [ha, hb]
    exact hLinear a b hCopies
  parent_injective := by
    intro edge edge' hEq
    exact (Train.bottom edge edge').mp (Quotient.exact hEq)

/-- At the actual physical bottom cut, the generic two-sort owner
predicate is the exact already-minimized geometric owner predicate.
Designated copies may be physically carried by other standards;
no false uniqueness or provenance assumption is introduced. -/
theorem attachedSelectedPicture_bottomGeometricAllowed_iff
    {n : ℕ} (K : (Out).BigCycle n)
    (k : Fin n) (owner : I ⊕ CoreEdge) :
    K.BottomGeometricAllowed (Out)
      (fun i : I => copyCarrier (Std i))
      CoreActual k owner ↔
      GeomAllowed (K.label k) owner := by
  cases owner with
  | inl i => rfl
  | inr b => rfl


/-- The exact real-output version of the no-mixed-singleton interface.
The two remaining geometric inputs are the complete B-boundary theorem
and the fact that a genuine mixed cut has a core vertex and a *whole*
core wagon edge. It uses the already-minimized geometric owner word and
does not assume any full-system-girth conclusion. -/
theorem attachedSelectedPicture_bottom_no_mixed_singleton_of_core_boundary
    [Nontrivial UA] (hLinear : ALinear A Actual)
    {n : ℕ} (K : (Out).BigCycle n)
    (hNormalized : K.MixedNormalized Out)
    (owner : Fin n → I ⊕ CoreEdge)
    (hAllowed : ∀ j, GeomAllowed (K.label j) (owner j))
    (hMinimal : ∀ other : Fin n → I ⊕ CoreEdge,
      (∀ j, GeomAllowed (K.label j) (other j)) →
      cyclicOwnerChanges owner ≤ cyclicOwnerChanges other)
    (hBoundary : ∀ a : (I × {q : DesignatedCopy B D C family // q ∈ selected}) ⊕ ActualEdge,
      (Out).designated a →
        SmallOrWholeEdgeBoundary
          (Set.range (fun b : CoreEdge => (CoreActual b).1))
          (copyCarrier (RelStructure.Attachment.coreEmbedding C.toRelStructure S R f))
          ((Out).bottomForestPiece
            (attachedSelectedPicture_bottomForestGeometry
              A hA B D C family selected e R f T U hShared hLinear) a))
    (k : Fin n)
    (hLeftCut : owner (trainCyclicPred k) ≠ owner k)
    (hRightCut : owner k ≠ owner (cyclicSucc k))
    (hCoreMixed :
      ∃ x : RelStructure.Attachment.Vertex S (W := Y) (I := I),
      ∃ p : Quotient ((Train).wagonSetoid μBottom),
        ((K.connector (trainCyclicPred k) = Sum.inl x ∧
          K.connector k = Sum.inr p) ∨
         (K.connector (trainCyclicPred k) = Sum.inr p ∧
          K.connector k = Sum.inl x)) ∧
        x ∈ copyCarrier (RelStructure.Attachment.coreEmbedding C.toRelStructure S R f) ∧
        (∀ a : ActualEdge, (Out).parent a = p →
          a.1 ⊆ copyCarrier
            (RelStructure.Attachment.coreEmbedding C.toRelStructure S R f))) :
    False := by
  let H := attachedSelectedPicture_bottomForestGeometry
    A hA B D C family selected e R f T U hShared hLinear
  have hAllowed' : ∀ j : Fin n,
      K.BottomGeometricAllowed Out
        (fun i : I => copyCarrier (Std i))
        CoreActual j (owner j) := by
    intro j
    exact (attachedSelectedPicture_bottomGeometricAllowed_iff
      A hA B D C family selected e R f T U hShared
      K j (owner j)).2 (hAllowed j)
  have hMinimal' : ∀ other : Fin n → I ⊕ CoreEdge,
      (∀ j, K.BottomGeometricAllowed Out
        (fun i : I => copyCarrier (Std i))
        CoreActual j (other j)) →
      cyclicOwnerChanges owner ≤ cyclicOwnerChanges other := by
    intro other ho
    apply hMinimal other
    intro j
    exact (attachedSelectedPicture_bottomGeometricAllowed_iff
      A hA B D C family selected e R f T U hShared
      K j (other j)).1 (ho j)
  exact K.bottom_normalized_minimal_no_mixed_singleton_of_boundary
    Out H hNormalized
    (fun i : I => copyCarrier (Std i)) CoreActual
    owner hAllowed' hMinimal'
    (copyCarrier (RelStructure.Attachment.coreEmbedding C.toRelStructure S R f))
    (Set.range (fun b : CoreEdge => (CoreActual b).1))
    hBoundary k hLeftCut hRightCut hCoreMixed

end ActualBottomGeometry

end StructuralRamsey.Girth
