import Girth.TrainActualBottomDesignatedBoundary
import Girth.TrainActualBottomOwnerCoreSeparation
import Girth.TrainActualNormalizedMinimalOwners
import Girth.TrainDirectCyclicCutBudget

set_option autoImplicit false
set_option Elab.async false

/-!
# A genuine bottom geometric owner cut lies in the shared core

Distinct geometric owners meet only in the core. A cut vertex belongs
to both adjacent labels. At the bottom a cut wagon likewise has one
physical edge in both labels, by injectivity of the wagon parent.

Both boundary orientations of an isolated segment are covered. This
discharges the remaining physical cut input of the bottom
no-mixed-singleton theorem, using physical picture geometry.
-/

namespace StructuralRamsey.Girth
open StructuralRamsey.RelStructure

universe u v

section ActualBottomCutGeometry

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
local notation "Selected" => {q : DesignatedCopy B D C family // q ∈ selected}
local notation "Core" => RelStructure.Attachment.coreEmbedding C.toRelStructure S R f
local notation "Train" => generatedActualASupportTrain
  A hA C.toRelStructure S R f T U hShared
local notation "μBottom" => (Fin.mk 0 (Nat.zero_lt_succ m))
local notation "Out" => attachedSelectedPictureOrderOneData
  A hA B D C family selected e R f T U hShared μBottom
local notation "GeomAllowed" => selectedOutputGeometricOwnerAllowed
  A hA B D C family selected e R f T U hShared μBottom

/-- At every genuine owner cut, its vertex belongs to the shared core;
alternatively, the whole bottom wagon edge lies in the core. The two
conclusions have precisely the connector kinds needed for the
mixed-singleton argument, including cyclic wrap. -/
theorem attachedSelectedPicture_bottom_cut_connector_core_geometry
    (H : (Out).BottomForestGeometry)
    {n : ℕ} (K : (Out).BigCycle n)
    (owner : Fin n → I ⊕ CoreEdge)
    (hAllowed : ∀ j, GeomAllowed (K.label j) (owner j))
    (k : Fin n)
    (hCut : owner k ≠ owner (cyclicSucc k)) :
    (∀ x : RelStructure.Attachment.Vertex S (W := Y) (I := I),
      K.connector k = Sum.inl x → x ∈ copyCarrier Core) ∧
    (∀ p : Quotient ((Train).wagonSetoid μBottom),
      K.connector k = Sum.inr p →
      ∀ a : ActualEdge, (Out).parent a = p →
        a.1 ⊆ copyCarrier Core) := by
  have hCore := attachedSelectedPicture_bottom_distinctOwners_intersection_core
    A hA B D C family selected e R f T U hShared
    (K.label k) (K.label (cyclicSucc k))
    (owner k) (owner (cyclicSucc k))
    (hAllowed k) (hAllowed (cyclicSucc k)) hCut
  constructor
  · intro x hx
    have hLeft := K.left_incident k
    have hRight := K.right_incident k
    rw [hx] at hLeft hRight
    exact hCore ⟨hLeft, hRight⟩
  · intro p hp a ha
    have hLeft := K.left_incident k
    have hRight := K.right_incident k
    rw [hp] at hLeft hRight
    obtain ⟨l, hl, hParentLeft⟩ := hLeft
    obtain ⟨r, hr, hParentRight⟩ := hRight
    have hLeftEq : l = a := H.parent_injective (hParentLeft.trans ha.symm)
    have hRightEq : r = a := H.parent_injective (hParentRight.trans ha.symm)
    subst l
    subst r
    intro x hx
    exact hCore ⟨H.edge_subset _ a hl hx, H.edge_subset _ a hr hx⟩

/-- The two cut connectors surrounding any isolated mixed segment
have their actual physical core geometry. No abstract reduction
connector is silently substituted for the original one. -/
theorem attachedSelectedPicture_bottom_mixed_singleton_cut_core
    (H : (Out).BottomForestGeometry)
    {n : ℕ} (K : (Out).BigCycle n)
    (owner : Fin n → I ⊕ CoreEdge)
    (hAllowed : ∀ j, GeomAllowed (K.label j) (owner j))
    (k : Fin n)
    (hLeftCut : owner (trainCyclicPred k) ≠ owner k)
    (hRightCut : owner k ≠ owner (cyclicSucc k))
    (hMixed :
      ∃ x : RelStructure.Attachment.Vertex S (W := Y) (I := I),
      ∃ p : Quotient ((Train).wagonSetoid μBottom),
        (K.connector (trainCyclicPred k) = Sum.inl x ∧
          K.connector k = Sum.inr p) ∨
        (K.connector (trainCyclicPred k) = Sum.inr p ∧
          K.connector k = Sum.inl x)) :
    ∃ x : RelStructure.Attachment.Vertex S (W := Y) (I := I),
    ∃ p : Quotient ((Train).wagonSetoid μBottom),
      ((K.connector (trainCyclicPred k) = Sum.inl x ∧
          K.connector k = Sum.inr p) ∨
       (K.connector (trainCyclicPred k) = Sum.inr p ∧
          K.connector k = Sum.inl x)) ∧
      x ∈ copyCarrier Core ∧
      (∀ a : ActualEdge, (Out).parent a = p →
        a.1 ⊆ copyCarrier Core) := by
  have hPrevCut : owner (trainCyclicPred k) ≠
      owner (cyclicSucc (trainCyclicPred k)) := by
    simpa only [cyclicSucc_trainCyclicPred_of_two_le K.length_ge_two k]
      using hLeftCut
  obtain ⟨hPrevVertex, hPrevWagon⟩ :=
    attachedSelectedPicture_bottom_cut_connector_core_geometry
      A hA B D C family selected e R f T U hShared
      H K owner hAllowed (trainCyclicPred k) hPrevCut
  obtain ⟨hHereVertex, hHereWagon⟩ :=
    attachedSelectedPicture_bottom_cut_connector_core_geometry
      A hA B D C family selected e R f T U hShared
      H K owner hAllowed k hRightCut
  obtain ⟨x, p, hKinds⟩ := hMixed
  rcases hKinds with ⟨hPrev, hHere⟩ | ⟨hPrev, hHere⟩
  · exact ⟨x, p, Or.inl ⟨hPrev, hHere⟩,
      hPrevVertex x hPrev, hHereWagon p hHere⟩
  · exact ⟨x, p, Or.inr ⟨hPrev, hHere⟩,
      hHereVertex x hHere, hPrevWagon p hPrev⟩

/-- Full actual mixed-singleton exclusion, with only the standard
old/attached geometry: ordinary output A-linearity, strongly induced
base B-projections and genuine minimal geometric owner choice. -/
theorem attachedSelectedPicture_bottom_normalized_minimal_no_mixed_singleton
    [Nontrivial UA]
    (hLinear : ALinear A Actual)
    (hStrong : ∀ q : Selected, AStrong A D (copyCarrier q.1.base))
    {n : ℕ} (K : (Out).BigCycle n)
    (hNormalized : K.MixedNormalized Out)
    (owner : Fin n → I ⊕ CoreEdge)
    (hAllowed : ∀ j, GeomAllowed (K.label j) (owner j))
    (hMinimal : ∀ other : Fin n → I ⊕ CoreEdge,
      (∀ j, GeomAllowed (K.label j) (other j)) →
      cyclicOwnerChanges owner ≤ cyclicOwnerChanges other)
    (k : Fin n)
    (hLeftCut : owner (trainCyclicPred k) ≠ owner k)
    (hRightCut : owner k ≠ owner (cyclicSucc k))
    (hMixed :
      ∃ x : RelStructure.Attachment.Vertex S (W := Y) (I := I),
      ∃ p : Quotient ((Train).wagonSetoid μBottom),
        (K.connector (trainCyclicPred k) = Sum.inl x ∧
          K.connector k = Sum.inr p) ∨
        (K.connector (trainCyclicPred k) = Sum.inr p ∧
          K.connector k = Sum.inl x)) : False := by
  let H := attachedSelectedPicture_bottomForestGeometry
    A hA B D C family selected e R f T U hShared hLinear
  have hCoreMixed :=
    attachedSelectedPicture_bottom_mixed_singleton_cut_core
      A hA B D C family selected e R f T U hShared
      H K owner hAllowed k hLeftCut hRightCut hMixed
  exact attachedSelectedPicture_bottom_no_mixed_singleton_of_base_strong
    A hA B D C family selected e R f T U hShared
    hLinear hStrong K hNormalized owner hAllowed hMinimal
    k hLeftCut hRightCut hCoreMixed


/-- One actual output bottom cycle can be simultaneously short-normalized
and assigned minimum GEOMETRIC owners, with no mixed singleton segment.
Its connector word and order are unchanged; every later genuinely
supreme ORIGINAL B-label pulls back to the initial cycle. This is the
precise input to the separate finite segment-word budget theorem. -/
theorem attachedSelectedPicture_bottom_exists_normalized_minimum_no_mixed
    [Nontrivial UA]
    (hPhysical : ALinear A Actual)
    (hStrong : ∀ q : Selected, AStrong A D (copyCarrier q.1.base))
    {n : ℕ} (K : (Out).BigCycle n)
    (hAccept : K.Acceptable) (hn : 3 ≤ n) :
    ∃ Z : (Out).BigCycle n,
      Z.Acceptable ∧ Z.twiceOrder = K.twiceOrder ∧
      Z.MixedNormalized Out ∧
      (∀ j : Fin n, Z.connector j = K.connector j) ∧
      ∃ owner : Fin n → I ⊕ CoreEdge,
        (∀ j, GeomAllowed (Z.label j) (owner j)) ∧
        (∀ other : Fin n → I ⊕ CoreEdge,
          (∀ j, GeomAllowed (Z.label j) (other j)) →
          cyclicOwnerChanges owner ≤ cyclicOwnerChanges other) ∧
        (∀ k : Fin n,
          owner (trainCyclicPred k) ≠ owner k →
          owner k ≠ owner (cyclicSucc k) →
          ¬ ∃ x : RelStructure.Attachment.Vertex S (W := Y) (I := I),
            ∃ p : Quotient ((Train).wagonSetoid μBottom),
              (Z.connector (trainCyclicPred k) = Sum.inl x ∧
                Z.connector k = Sum.inr p) ∨
              (Z.connector (trainCyclicPred k) = Sum.inr p ∧
                Z.connector k = Sum.inl x)) ∧
        (∀ kZ : Fin n, Z.HasSupremeAt Out kZ →
          ∃ kK : Fin n, K.label kK = Z.label kZ ∧
            K.HasSupremeAt Out kK) := by
  let H := attachedSelectedPicture_bottomForestGeometry
    A hA B D C family selected e R f T U hShared hPhysical
  have hOutputLinear : (Out).LinearPretrain :=
    OrderOneData.BottomForestGeometry.linearPretrain Out H
  obtain ⟨Z, hZAccept, hZOrder, hZNormal, hZConnectors,
      ⟨owner, hAllowed, hMinimal⟩, hPull⟩ :=
    attachedSelectedPicture_exists_normalized_minimal_geometric_owners
      A hA B D C family selected e R f T U hShared μBottom
      K hAccept hOutputLinear hn
  refine ⟨Z, hZAccept, hZOrder, hZNormal, hZConnectors,
    owner, hAllowed, hMinimal, ?_, hPull⟩
  intro k hLeft hRight hMixed
  exact attachedSelectedPicture_bottom_normalized_minimal_no_mixed_singleton
    A hA B D C family selected e R f T U hShared
    hPhysical hStrong Z hZNormal owner hAllowed hMinimal
    k hLeft hRight hMixed


/-- An acceptable real attached bottom cycle of length at least three
admits an equally ordered normalized cycle with a MINIMUM geometric
owner word whose number of cuts is at most the requested cycle-order
cutoff. The elementary direct cyclic charging argument avoids an
artificial segment-block representation. This still does not prove
supremeness of the output; the reduced forest and transfer are separate. -/
theorem attachedSelectedPicture_bottom_exists_normalized_minimum_cut_budget
    [Nontrivial UA]
    (hPhysical : ALinear A Actual)
    (hStrong : ∀ q : Selected, AStrong A D (copyCarrier q.1.base))
    {n q : ℕ} (K : (Out).BigCycle n)
    (hAccept : K.Acceptable) (hn : 3 ≤ n)
    (hOrder : K.twiceOrder ≤ 2 * q) :
    ∃ Z : (Out).BigCycle n,
      Z.Acceptable ∧ Z.twiceOrder = K.twiceOrder ∧
      Z.MixedNormalized Out ∧
      (∀ j : Fin n, Z.connector j = K.connector j) ∧
      ∃ owner : Fin n → I ⊕ CoreEdge,
        (∀ j, GeomAllowed (Z.label j) (owner j)) ∧
        (∀ other : Fin n → I ⊕ CoreEdge,
          (∀ j, GeomAllowed (Z.label j) (other j)) →
          cyclicOwnerChanges owner ≤ cyclicOwnerChanges other) ∧
        cyclicOwnerChanges owner ≤ q ∧
        (∀ kZ : Fin n, Z.HasSupremeAt Out kZ →
          ∃ kK : Fin n, K.label kK = Z.label kZ ∧
            K.HasSupremeAt Out kK) := by
  obtain ⟨Z, hZAccept, hZOrder, hZNormal, hZConnectors,
    owner, hAllowed, hMinimal, hNoMixed, hPull⟩ :=
    attachedSelectedPicture_bottom_exists_normalized_minimum_no_mixed
      A hA B D C family selected e R f T U hShared
      hPhysical hStrong K hAccept hn
  have hKinds (k : Fin n)
      (hLeft : owner (trainCyclicPred k) ≠ owner k)
      (hRight : owner k ≠ owner (cyclicSucc k)) :
      OrderOneData.connectorKind (Z.connector (trainCyclicPred k)) =
        OrderOneData.connectorKind (Z.connector k) := by
    have hNo := hNoMixed k hLeft hRight
    cases hPrev : Z.connector (trainCyclicPred k) with
    | inl x =>
        cases hHere : Z.connector k with
        | inl y => rfl
        | inr p =>
            exact False.elim (hNo
              ⟨x, p, Or.inl ⟨hPrev, hHere⟩⟩)
    | inr p =>
        cases hHere : Z.connector k with
        | inl x =>
            exact False.elim (hNo
              ⟨x, p, Or.inr ⟨hPrev, hHere⟩⟩)
        | inr w => rfl
  have hBudget : cyclicOwnerChanges owner ≤ q :=
    Z.ownerCuts_le_cutoff_of_no_mixed Out owner hKinds
      (by rw [hZOrder]; exact hOrder)
  exact ⟨Z, hZAccept, hZOrder, hZNormal, hZConnectors,
    owner, hAllowed, hMinimal, hBudget, hPull⟩

end ActualBottomCutGeometry

end StructuralRamsey.Girth
