import Girth.TrainWitnessCopyShadowProbe
import Girth.TrainRealSharedShortOldPairProbe
import Girth.TrainRealSharedLongOldWagonProbe
import Girth.TrainOldCopyLocalProbePieces
import Mathlib.Tactic

set_option autoImplicit false
set_option Elab.async false

/-!
# Path A: genuine lower vertex pieces force an OLD original B-copy piece

The actual original selected B-copy q is NOT identified with the
lower witness gluing standard i. Instead two genuine old vertices
x0,y0 of q have standard images equal to the two lower core
vertices x,y. The lower standard i provides a real ShortPiece
or LongPiece (e.g. via its checked shadow-copy/edge probe).

The physical short trace gives a TRUE OLD pair edge through
x0,y0. The physical long trace gives EITHER an old pair edge OR
two old shared support edges through x0,y0 in one OLD wagon,
with no old pair edge. The checked OLD selected-copy order-two
probe converts either physical configuration into a real
ShortPiece or LongPiece of q, using old SupremeCycleBound qcut.

The conclusion is about the ORIGINAL selected old B-copy q,
not about lower gluing label i. Transporting this old local
piece by the actual standard LiteralPhysicalMap and then using
the length-two local-to-global theorem finishes this branch
once the real source endpoints are aligned with the core.
No bogus pullback of the other original source label.
No appendix / manuscript changes.
-/

namespace StructuralRamsey.Girth
open StructuralRamsey.RelStructure

universe u v
section OriginalBVertexLocalFromWitness

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
variable (hRel : ∀ (ν : Fin (m + 1)) (j : I)
  (p q : SharedOldACarrierEdge A C.toRelStructure
    (activeCarrier A C e.toFunctionEmbedding)),
  T.rel ν p.1 q.1 ↔
    U.rel ν
      (sharedOldACarrierCoreEmbedding A C.toRelStructure
        (activeCarrier A C e.toFunctionEmbedding) R f j p)
      (sharedOldACarrierCoreEmbedding A C.toRelStructure
        (activeCarrier A C e.toFunctionEmbedding) R f j q))
variable (μ : Fin (m + 1))

local notation "S" => activeCarrier A C e.toFunctionEmbedding
local notation "Old" => selectedPictureOrderOneData
  A B D C family selected T μ
local notation "CoreEdge" => OldACarrierEdge A R
local notation "Selected" =>
  {r : DesignatedCopy B D C family // r ∈ selected}
local notation "Std" => RelStructure.Attachment.copyEmbedding
  C.toRelStructure S R f
local notation "CoreEmb" => RelStructure.Attachment.coreEmbedding
  C.toRelStructure S R f
local notation "Wit" => sharedWitnessOrderOneData U μ
  (sharedOldACarrierCoreEmbedding A C.toRelStructure S R f)
  (Subtype.val : CoreEdge → Set Y)

/-- Old SupremeCycleBound at cutoff >=2 supplies a local piece
of the exact ORIGINAL SELECTED B-copy once its true old
boundary vertices are images of lower core vertices and
the lower gluing standard has a real short or long witness.
No original source label or whole-cycle pullback is invented. -/
theorem original_selected_B_local_piece_of_witness_piece
    {qcut : ℕ} (hq : 2 ≤ qcut)
    (hOld : (Old).SupremeCycleBound qcut)
    (q : Selected) (i : I)
    (x0 y0 : X) (x y : Y)
    (hOldXY : x0 ≠ y0)
    (hQX : x0 ∈ (Old).copyCarrier q)
    (hQY : y0 ∈ (Old).copyCarrier q)
    (hX : Std i x0 = CoreEmb x)
    (hY : Std i y0 = CoreEmb y)
    (hWitnessPiece :
      (Wit).ShortPiece (Sum.inl i) (Sum.inl x) (Sum.inl y) ∨
      (Wit).LongPiece (Sum.inl i) (Sum.inl x) (Sum.inl y)) :
    (Old).ShortPiece (Sum.inl q) (Sum.inl x0) (Sum.inl y0) ∨
    (Old).LongPiece (Sum.inl q) (Sum.inl x0) (Sum.inl y0) := by
  have hProbe :
      (Old).PairEdge x0 y0 ∨
      (¬ (Old).PairEdge x0 y0 ∧
        ∃ (p : Quotient (T.wagonSetoid μ))
          (a b : OldACarrierEdge A C.toRelStructure),
          (Old).parent a = p ∧ (Old).parent b = p ∧
          x0 ∈ a.1 ∧ y0 ∈ b.1) := by
    rcases hWitnessPiece with hShort | hLong
    · exact Or.inl <|
        sharedWitness_short_two_vertices_old_pair_probe
          A B D C family selected e R f T U μ
          i x0 y0 x y hX hY hShort
    · exact sharedWitness_long_two_vertices_old_pair_or_wagon_probe
        A B D C family selected e R f T U hRel μ
        i x0 y0 x y hX hY hLong
  exact (Old).copy_local_piece_of_pair_or_wagon_probe
    hq hOld q x0 y0 hOldXY hQX hQY hProbe


/-- The EXACT original selected-B local vertex piece follows from
true OLD SupremeCycleBound and true LOWER FullSystemGirthGT:
no separately chosen lower short or long witness is postulated.

A distinct shadow lower label (another gluing copy OR a genuine
physical core A-edge) is incident at both distinct lower core
vertices x,y. The lower system bound produces the local piece
in gluing standard i by checked two-copy/edge probe symmetry.
Exact shared core-to-old support/wagon reflection then gives
a real OLD pair-or-wagon probe; OLD selected-copy system girth
produces the local piece belonging to the ORIGINAL selected B-copy q. -/
theorem original_selected_B_vertex_local_of_lower_shadow
    {qcut : ℕ} (hq : 2 ≤ qcut)
    (hOld : (Old).SupremeCycleBound qcut)
    (hWitness : (Wit).FullSystemGirthGT qcut)
    (q : Selected) (i : I) (a : I ⊕ CoreEdge)
    (hOther : Sum.inl i ≠ a)
    (x0 y0 : X) (x y : Y)
    (hOldXY : x0 ≠ y0) (hCoreXY : x ≠ y)
    (hQX : x0 ∈ (Old).copyCarrier q)
    (hQY : y0 ∈ (Old).copyCarrier q)
    (hX : Std i x0 = CoreEmb x)
    (hY : Std i y0 = CoreEmb y)
    (hIx : x ∈ (Wit).copyCarrier i)
    (hIy : y ∈ (Wit).copyCarrier i)
    (hAx : x ∈ (Wit).carrier a)
    (hAy : y ∈ (Wit).carrier a) :
    (Old).ShortPiece (Sum.inl q) (Sum.inl x0) (Sum.inl y0) ∨
    (Old).LongPiece (Sum.inl q) (Sum.inl x0) (Sum.inl y0) := by
  have hLowerBound : (Wit).LocalPieceSystemBound 2 := by
    intro n Z hAcc hOrder
    exact (Wit).localPieceSystemBound_of_supremeCycleBound
      qcut hWitness.2 n Z hAcc (by omega)
  have hLowerPiece :=
    (Wit).copy_local_piece_of_shadow_two_vertices
      hLowerBound i a hOther x y hCoreXY
      hIx hIy hAx hAy
  exact original_selected_B_local_piece_of_witness_piece
    A B D C family selected e R f T U hRel μ
    hq hOld q i x0 y0 x y
    hOldXY hQX hQY hX hY hLowerPiece

end OriginalBVertexLocalFromWitness
end StructuralRamsey.Girth
