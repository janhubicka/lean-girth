import Girth.TrainOriginalSelectedBVertexProbe
import Girth.TrainOriginalSelectedCoreVertexPreimage
import Girth.TrainActualMinimalTwoCycleShadow
import Girth.TrainActualTwoCycleOwnerShadowCoreIncidence
import Mathlib.Tactic

set_option autoImplicit false
set_option Elab.async false

/-!
# Genuine original selected B-copy piece from a minimal two-cycle shadow

The ORIGINAL attached selected output has two occurrences and two
genuine CORE vertex connectors. One source occurrence is an ACTUAL
transported designated B-copy (i,q), NOT the selected lower
geometric-owner label.

The true old endpoint preimages of this original q are recovered
from the selected source label's core vertex incidences. The
opposite occurrence's actual minimal geometric owner is distinct
from standard i (without making it equal to any original B-label),
and its full physical carrier contains both original core vertices.
The opposite owner therefore forms a genuine second shadow label
in the lower witness, whether another gluing copy or a physical
core A-edge.

Genuine lower FullSystemGirthGT supplies the local short/long piece
at i against this shadow, and the exact lower->old physical
pair/wagon probes plus OLD selected SupremeCycleBound produce a
local short/long piece of the ORIGINAL selected B-copy q between
the REAL old endpoint preimages.

No auxiliary assumptions for old vertex preimages, vertex
distinctness, shadow incidence or shadow index inequality remain.
The result is an ORIGINAL B-local piece; the final old-standard
physical map and two-occurrence PlanValid completion to the
attached output are separate interfaces. No output system girth,
invented B-label or appendix lemma is assumed.
-/

namespace StructuralRamsey.Girth
open StructuralRamsey.RelStructure

universe u v
section OriginalBTwocycleShadow

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

/-- At any genuine original source length-two selected-output cycle
with TWO core vertex connectors and a minimal two-cut geometric
assignment, an original selected B-label (i,q) has its own literal
old-source local short or long piece. The physical old endpoints
are constructed from the original q (not postulated), and the
distinct lower shadow and its two vertex incidences are derived
from the actual other geometric owner. -/
theorem attachedSelectedPicture_two_cycle_original_B_vertex_local_from_minimal_shadow
    {qcut : ℕ} (hq : 2 ≤ qcut)
    (hOld : (Old).SupremeCycleBound qcut)
    (hWitness : (Wit).FullSystemGirthGT qcut)
    (K : (Out).BigCycle 2)
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
    ∃ x0 y0 : X,
      x0 ∈ (Old).copyCarrier q ∧
      y0 ∈ (Old).copyCarrier q ∧
      Std i x0 = CoreEmb x ∧
      Std i y0 = CoreEmb y ∧
      ((Old).ShortPiece (Sum.inl q) (Sum.inl x0) (Sum.inl y0) ∨
        (Old).LongPiece (Sum.inl q) (Sum.inl x0) (Sum.inl y0)) := by
  have hSourceX : CoreEmb x ∈ (Out).carrier (Sum.inl (i, q)) := by
    have hInc := OrderOneData.BigCycle.two_all_label_connector_incidence
      (Out) K target (0 : Fin 2)
    rw [hOriginal, hX] at hInc
    exact hInc
  have hSourceY : CoreEmb y ∈ (Out).carrier (Sum.inl (i, q)) := by
    have hInc := OrderOneData.BigCycle.two_all_label_connector_incidence
      (Out) K target (1 : Fin 2)
    rw [hOriginal, hY] at hInc
    exact hInc
  obtain ⟨x0, hxOld, hxStd, hxWit⟩ :=
    attachedSelectedPicture_original_B_core_vertex_old_preimage
      A hA B D C family selected e R f T U hShared μ
      i q x hSourceX
  obtain ⟨y0, hyOld, hyStd, hyWit⟩ :=
    attachedSelectedPicture_original_B_core_vertex_old_preimage
      A hA B D C family selected e R f T U hShared μ
      i q y hSourceY
  have hxy : x ≠ y := by
    intro heq
    have hConn : K.connector (0 : Fin 2) =
        K.connector (1 : Fin 2) := by
      calc
        K.connector (0 : Fin 2) = Sum.inl (CoreEmb x) := hX
        _ = Sum.inl (CoreEmb y) := by rw [heq]
        _ = K.connector (1 : Fin 2) := hY.symm
    exact (by decide : (0 : Fin 2) ≠ 1)
      (K.connector_injective hConn)
  have hOldXY : x0 ≠ y0 := by
    intro h
    apply hxy
    apply CoreEmb.injective
    calc
      CoreEmb x = Std i x0 := hxStd.symm
      _ = Std i y0 := congrArg (fun z => Std i z) h
      _ = CoreEmb y := hyStd
  have hOther : (Sum.inl i : I ⊕ CoreEdge) ≠
      owner (cyclicSucc target) :=
    attachedSelectedPicture_two_cycle_original_standard_diff_shadow
      A hA B D C family selected e R f T U hShared μ
      K owner hAllowed hMinimal hTwo target i q hOriginal
  have hShadow : x ∈ (Wit).carrier (owner (cyclicSucc target)) ∧
      y ∈ (Wit).carrier (owner (cyclicSucc target)) :=
    attachedSelectedPicture_two_cycle_other_owner_core_shadow
      A hA B D C family selected e R f T U hShared μ
      K owner hAllowed target x y hX hY
  have hPiece :
      (Old).ShortPiece (Sum.inl q) (Sum.inl x0) (Sum.inl y0) ∨
      (Old).LongPiece (Sum.inl q) (Sum.inl x0) (Sum.inl y0) := by
    exact original_selected_B_vertex_local_of_lower_shadow
      A B D C family selected e R f T U hRel μ
      hq hOld hWitness q i (owner (cyclicSucc target)) hOther
      x0 y0 x y hOldXY hxy hxOld hyOld hxStd hyStd
      hxWit hyWit hShadow.1 hShadow.2
  exact ⟨x0, y0, hxOld, hyOld, hxStd, hyStd, hPiece⟩

end OriginalBTwocycleShadow
end StructuralRamsey.Girth
