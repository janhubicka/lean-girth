import Girth.TrainActualBottomCutCoreGeometry
import Girth.TrainBottomForestReducedNoA1
import Girth.TrainActualCutIndexedBigCycle

set_option autoImplicit false
set_option Elab.async false

/-!
# The genuine reduced bottom witness is globally supreme under local forests

The actual bottom minimum has at most q owner cuts by the direct
charging lemma. The literal cut-indexed witness BigCycle inherits A2
and A3. Its forest supremeness holds at ANY length, including length
two with no source A1, by the independent bottom-intersection proof.

The reduced supreme witness label names a gluing copy Q, NOT an
original B-label. Transferring to an original B-copy is separate.
-/

namespace StructuralRamsey.Girth
open StructuralRamsey.RelStructure

universe u v
section BottomReducedForest

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
variable (hRel : ∀ (ν : Fin (m + 1)) (j : I)
  (p q : SharedOldACarrierEdge A C.toRelStructure
    (activeCarrier A C e.toFunctionEmbedding)),
  T.rel ν p.1 q.1 ↔
    U.rel ν (sharedOldACarrierCoreEmbedding A C.toRelStructure
      (activeCarrier A C e.toFunctionEmbedding) R f j p)
      (sharedOldACarrierCoreEmbedding A C.toRelStructure
        (activeCarrier A C e.toFunctionEmbedding) R f j q))

local notation "S" => activeCarrier A C e.toFunctionEmbedding
local notation "Actual" => RelStructure.Attachment.attach C.toRelStructure S R f
local notation "CoreEdge" => OldACarrierEdge A R
local notation "Selected" => {q : DesignatedCopy B D C family // q ∈ selected}
local notation "μBottom" => (⟨0, Nat.zero_lt_succ m⟩ : Fin (m + 1))
local notation "Out" => attachedSelectedPictureOrderOneData
  A hA B D C family selected e R f T U hShared μBottom
local notation "Wit" => sharedWitnessOrderOneData U μBottom
  (sharedOldACarrierCoreEmbedding A C.toRelStructure S R f)
  (Subtype.val : CoreEdge → Set Y)
local notation "GeomAllowed" => selectedOutputGeometricOwnerAllowed
  A hA B D C family selected e R f T U hShared μBottom

include hRel

/-- A genuine cut-indexed bottom witness has a global supreme plan
from a finite mixed-forest bound and the number-of-cuts budget. The
reduced order-one A1 obligation is NOT an input, including two cuts. -/
theorem attachedSelectedPicture_bottom_reduced_supreme_of_localForest
    (H : (Wit).BottomForestGeometry)
    (q : ℕ)
    (hLocal : LocalForestThrough ((Wit).bottomForestPiece H) q)
    {n : ℕ} (K : (Out).BigCycle n)
    (owner : Fin n → I ⊕ CoreEdge)
    (hAllowed : ∀ j, GeomAllowed (K.label j) (owner j))
    (hCuts : 2 ≤ cyclicOwnerChanges owner)
    (hBound : cyclicOwnerChanges owner ≤ q)
    (hA2 : K.A2) (hA3 : K.A3) :
    (attachedSelectedPicture_geometric_cutBigCycle
      A hA B D C family selected e R f T U hShared hRel μBottom
      K owner hAllowed hCuts).HasSimultaneousSupreme := by
  let Z := attachedSelectedPicture_geometric_cutBigCycle
    A hA B D C family selected e R f T U hShared hRel μBottom
    K owner hAllowed hCuts
  have hRestriction := attachedSelectedPicture_geometric_cut_restriction_bounds
    A hA B D C family selected e R f T U hShared hRel μBottom
    K owner hAllowed hCuts hA2 hA3
  have hZA2 : Z.A2 := hRestriction.2.2.1
  have hZA3 : Z.A3 := hRestriction.2.2.2
  exact Z.hasSimultaneousSupreme_of_bottomLocalForest_A2_A3
    Wit H q hLocal hBound hZA2 hZA3

end BottomReducedForest
end StructuralRamsey.Girth
