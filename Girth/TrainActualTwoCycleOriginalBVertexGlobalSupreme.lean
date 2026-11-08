import Girth.TrainActualTwoCycleOriginalBVertexLocalFromMinimalShadow
import Girth.TrainActualStandardPhysicalMap
import Girth.TrainPhysicalMapLocalPieces
import Girth.TrainTwoCycleOriginalLocalToGlobal
import Girth.TrainTwoCopyLocalSymmetry
import Mathlib.Tactic

set_option autoImplicit false
set_option Elab.async false

/-!
# Exact ORIGINAL source n=2 vertex/vertex two-cut GLOBAL supreme

Under genuine old selected SupremeCycleBound and lower witness
FullSystemGirthGT at q>=2, every acceptable original selected
output BigCycle of length exactly TWO, with TWO genuine core
vertex connectors and a MINIMAL exactly-two-geometric-owner
assignment, has a COMPLETE simultaneous supreme replacement,
provided the old active fibre and every actual gluing core image
are A-strong and the attached pretrain is linear.

The selected supreme label is a genuinely ORIGINAL attached
B-copy (i,q), not a synthetic lower gluing-standard index.
The true old endpoint preimages, original B-copy local
ShortPiece/LongPiece and distinct second witness shadow are
PROVED by the component theorem. The exact old-standard literal
physical map sends this specific OLD local piece to the
attached output without pulling back the OTHER original label.
The verified local-to-global theorem handles the source
length-two keep/short or keep/long plan and preserves the whole
physical labelled output word.

The chosen original target may occupy either cyclic position:
for the second orientation the checked vertex-piece reversal
converts the original x-to-y local piece to the correct
target-to-other connector orientation.

No attached-output FullSystemGirthGT, fake B-label equality,
extra preimages, owner-shadow hypotheses or edge deletion.
Only the original two-VERTEX connector case is claimed;
the original mixed vertex/wagon case remains independent.
Circulation only; no appendix.
-/

namespace StructuralRamsey.Girth
open StructuralRamsey.RelStructure

universe u v
section OriginalBTwoCycleGlobalSupreme

variable {L : RelLanguage.{u}} {UA VB P X Y I : Type v}
variable (A : RelStructure L UA) (hA : A.Irreducible)
variable (B : RelStructure L VB) (D : RelStructure L P)
variable (C : StructuralRamsey.Partite.System L P X)
variable (family : Set (Embedding B D))
variable (selected : Set (DesignatedCopy B D C family))
variable (e : Embedding A D) (R : RelStructure L Y)
variable (f : I → Embedding
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
variable (μ : Fin (m + 1))

local notation "S" => activeCarrier A C e.toFunctionEmbedding
local notation "CoreEdge" => OldACarrierEdge A R
local notation "Old" => selectedPictureOrderOneData
  A B D C family selected T μ
local notation "Wit" => sharedWitnessOrderOneData U μ
  (sharedOldACarrierCoreEmbedding A C.toRelStructure S R f)
  (Subtype.val : CoreEdge → Set Y)
local notation "Selected" =>
  {q : DesignatedCopy B D C family // q ∈ selected}
local notation "CoreEmb" => RelStructure.Attachment.coreEmbedding
  C.toRelStructure S R f
local notation "Std" => RelStructure.Attachment.copyEmbedding
  C.toRelStructure S R f
local notation "Out" => attachedSelectedPictureOrderOneData
  A hA B D C family selected e R f T U hShared μ
local notation "GeomAllowed" => selectedOutputGeometricOwnerAllowed
  A hA B D C family selected e R f T U hShared μ

include hRel

/-- FULL original n=2 source HasSimultaneousSupreme, for TWO core
vertex connectors and the actual minimum two-cut owner word, from
real old/witness cut certificates and actual standard strongness.
No independent local piece, owner shadow, or output supreme bound
is assumed. -/
theorem attachedSelectedPicture_two_cycle_original_B_vertex_full_supreme
    {qcut : ℕ} (hq : 2 ≤ qcut)
    (hOld : (Old).SupremeCycleBound qcut)
    (hWitness : (Wit).FullSystemGirthGT qcut)
    (hOldStrong : AStrong A C.toRelStructure S)
    (hCoreStrong : ∀ j : I, AStrong A R (copyCarrier (f j)))
    (hLinear : (Out).LinearPretrain)
    (K : (Out).BigCycle 2) (hAccept : K.Acceptable)
    (owner : Fin 2 → I ⊕ CoreEdge)
    (hAllowed : ∀ k, GeomAllowed (K.label k) (owner k))
    (hMinimal : ∀ other : Fin 2 → I ⊕ CoreEdge,
      (∀ k, GeomAllowed (K.label k) (other k)) →
        cyclicOwnerChanges owner ≤ cyclicOwnerChanges other)
    (hTwo : cyclicOwnerChanges owner = 2)
    (target : Fin 2) (i : I) (q : Selected)
    (hOriginal : K.label target = Sum.inl (i, q))
    (x y : Y)
    (hX : K.connector (0 : Fin 2) = Sum.inl (CoreEmb x))
    (hY : K.connector (1 : Fin 2) = Sum.inl (CoreEmb y)) :
    K.HasSimultaneousSupreme := by
  obtain ⟨x0, y0, _hQX, _hQY, hxStd, hyStd, hOldPiece⟩ :=
    attachedSelectedPicture_two_cycle_original_B_vertex_local_from_minimal_shadow
      A hA B D C family selected e R f T U hShared hRel μ
      hq hOld hWitness K owner hAllowed hMinimal hTwo
      target i q hOriginal x y hX hY
  let M := attachedSelectedPicture_standard_physicalMap
    A hA B D C family selected e R f T U hShared hRel μ
    hOldStrong hCoreStrong i
  have hMapped := M.localPiece_map
    (Sum.inl q) (Sum.inl x0) (Sum.inl y0) hOldPiece
  have hMapLabel :
      M.mapLabel (Sum.inl q) = (Sum.inl (i, q) :
        (I × Selected) ⊕
          OldACarrierEdge A
            (RelStructure.Attachment.attach C.toRelStructure S R f)) := by
    rfl
  have hMapX :
      M.mapConnector (Sum.inl x0) = Sum.inl (CoreEmb x) := by
    change Sum.inl (Std i x0) = Sum.inl (CoreEmb x)
    rw [hxStd]
  have hMapY :
      M.mapConnector (Sum.inl y0) = Sum.inl (CoreEmb y) := by
    change Sum.inl (Std i y0) = Sum.inl (CoreEmb y)
    rw [hyStd]
  rw [hMapLabel, hMapX, hMapY] at hMapped
  have hTargetPiece :
      (Out).ShortPiece (K.label target)
        (K.connector (trainCyclicPred (cyclicSucc target)))
        (K.connector (cyclicSucc target)) ∨
      (Out).LongPiece (K.label target)
        (K.connector (trainCyclicPred (cyclicSucc target)))
        (K.connector (cyclicSucc target)) := by
    have hPred : trainCyclicPred (cyclicSucc target) = target :=
      trainCyclicPred_cyclicSucc_of_two_le
        (by decide : 2 ≤ 2) target
    rw [hPred]
    have hIndex : target = (0 : Fin 2) ∨
        target = (1 : Fin 2) := by
      fin_cases target <;> simp
    rcases hIndex with hIndex | hIndex
    · subst target
      simpa [cyclicSucc, hOriginal, hX, hY] using hMapped
    · subst target
      have hReverse :
          (Out).ShortPiece (Sum.inl (i, q))
              (Sum.inl (CoreEmb y)) (Sum.inl (CoreEmb x)) ∨
          (Out).LongPiece (Sum.inl (i, q))
              (Sum.inl (CoreEmb y)) (Sum.inl (CoreEmb x)) :=
        (Out).piece_vertices_reverse
          (Sum.inl (i, q)) (CoreEmb x) (CoreEmb y) hMapped
      simpa [cyclicSucc, hOriginal, hX, hY] using hReverse
  have hDesignated : (Out).designated (K.label target) := by
    rw [hOriginal]
    trivial
  have hFullTarget : K.HasSupremeAt (Out) target :=
    K.two_hasSupremeAt_of_original_local_piece
      (Out) hAccept hLinear target hDesignated hTargetPiece
  exact K.hasSimultaneousSupreme_of_hasSupremeAt
    (Out) target hFullTarget

end OriginalBTwoCycleGlobalSupreme
end StructuralRamsey.Girth
