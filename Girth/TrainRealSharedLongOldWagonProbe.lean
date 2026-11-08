import Girth.TrainRealSharedShortOldPairProbe
import Girth.TrainSharedOldACarrierCoreEmbedding
import Girth.TrainOldCopyLocalProbePieces
import Mathlib.Tactic

set_option autoImplicit false
set_option Elab.async false

/-!
# Path A: a genuine lower shared long yields an old pair-or-wagon probe

A witness LongPiece belonging to gluing copy i consists of real
shared core edges Emb_i(s), Emb_i(t), in the SAME witness wagon.
The physical core images reflect both boundary vertex contacts
to OLD standard vertices x0,y0. The exact hRel equivalence
reflects the shared witness wagon relation to a true OLD wagon.

The physical old situation is either an old PairEdge through
x0,y0 or a no-pair, same-wagon two-edge probe. No invalid
inference that lower non-pair implies old non-pair is needed.
The checked old selected-copy order-two probe then constructs
a genuine local piece of the ORIGINAL selected B-copy.

This is only an old physical trace theorem: preimage endpoints
must still be supplied and it does not assert original n=2
output supremacy. Circulation only; no appendix or paper edits.
-/

namespace StructuralRamsey.Girth
open StructuralRamsey.RelStructure

universe u v
section RealSharedLongOldTrace

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
local notation "OldEdge" => OldACarrierEdge A C.toRelStructure
local notation "CoreEdge" => OldACarrierEdge A R
local notation "Shared" => SharedOldACarrierEdge A C.toRelStructure S
local notation "Emb" => sharedOldACarrierCoreEmbedding
  A C.toRelStructure S R f
local notation "Std" => RelStructure.Attachment.copyEmbedding
  C.toRelStructure S R f
local notation "CoreEmb" => RelStructure.Attachment.coreEmbedding
  C.toRelStructure S R f
local notation "Wit" => sharedWitnessOrderOneData U μ
  Emb (Subtype.val : CoreEdge → Set Y)

/-- A real shared old A-support edge has its witness vertex
contacts exactly reflected to the old standard carrier. -/
theorem sharedWitness_edge_vertex_old_mem
    (i : I) (s : Shared)
    (x0 : X) (x : Y)
    (hX : Std i x0 = CoreEmb x)
    (hCore : x ∈ (Emb i s).1) :
    x0 ∈ s.1.1 := by
  have hStdX : Std i x0 ∈
      (fun z : X => Std i z) '' s.1.1 := by
    rw [sharedOldACarrierCoreMap_image
      A C.toRelStructure S R f i s]
    exact ⟨x, hCore, hX.symm⟩
  obtain ⟨u, hu, hUx⟩ := hStdX
  have hUX : u = x0 := (Std i).injective hUx
  subst u
  exact hu

/-- A REAL lower witness bridge in gluing copy i has an OLD
shared physical A-support edge through the exact old vertex x0,
and its witness wagon is the actual quotient class of that edge.
This is the old-edge trace needed for the original n=2 mixed
vertex/wagon selected-copy probe. The final wagon comparison to
an OLD selected B-copy edge still uses the standard wagon embedding
and is intentionally a separate geometric obligation. -/
theorem sharedWitness_bridge_old_vertex_wagon_probe
    (i : I) (x0 : X) (x : Y)
    (hX : Std i x0 = CoreEmb x)
    (p : Quotient (U.wagonSetoid μ))
    (hBridge : (Wit).Bridge (Sum.inl i) x p) :
    ∃ s : Shared, x0 ∈ s.1.1 ∧
      Quotient.mk (U.wagonSetoid μ) (Emb i s) = p := by
  obtain ⟨b, hOwned, hParent, hAtX⟩ := hBridge
  change b ∈ Set.range (Emb i) at hOwned
  obtain ⟨s, hs⟩ := hOwned
  subst b
  have hOldVertex : x0 ∈ s.1.1 := by
    have hOldImage : Std i x0 ∈ (fun z : X => Std i z) '' s.1.1 := by
      rw [sharedOldACarrierCoreMap_image
        A C.toRelStructure S R f i s]
      exact ⟨x, hAtX, hX.symm⟩
    obtain ⟨z, hz, hEq⟩ := hOldImage
    exact (Std i).injective hEq ▸ hz
  exact ⟨s, hOldVertex, hParent⟩

/-- True lower LONG at copy i supplies an OLD pair edge or
two OLD real support edges in one wagon with NO old pair. -/
theorem sharedWitness_long_two_vertices_old_pair_or_wagon_probe
    (i : I) (x0 y0 : X) (x y : Y)
    (hX : Std i x0 = CoreEmb x)
    (hY : Std i y0 = CoreEmb y)
    (hLong : (Wit).LongPiece (Sum.inl i)
      (Sum.inl x) (Sum.inl y)) :
    (Old).PairEdge x0 y0 ∨
    (¬ (Old).PairEdge x0 y0 ∧
      ∃ (p : Quotient (T.wagonSetoid μ)) (a b : OldEdge),
        (Old).parent a = p ∧ (Old).parent b = p ∧
        x0 ∈ a.1 ∧ y0 ∈ b.1) := by
  obtain ⟨x', y', w, a, b, hLeft, hRight,
    hAE, hBE, _hNe, hAP, hBP, hAX, hBY, _hNoPair⟩ := hLong
  have hxx : x' = x := (Sum.inl.inj hLeft).symm
  have hyy : y' = y := (Sum.inl.inj hRight).symm
  subst x'
  subst y'
  change a ∈ Set.range (Emb i) at hAE
  change b ∈ Set.range (Emb i) at hBE
  obtain ⟨s, hs⟩ := hAE
  obtain ⟨t, ht⟩ := hBE
  subst a
  subst b
  have hxOld : x0 ∈ s.1.1 := by
    have hOldImage : Std i x0 ∈ (fun z : X => Std i z) '' s.1.1 := by
      rw [sharedOldACarrierCoreMap_image
        A C.toRelStructure S R f i s]
      exact ⟨x, hAX, hX.symm⟩
    obtain ⟨z, hz, hEq⟩ := hOldImage
    exact (Std i).injective hEq ▸ hz
  have hyOld : y0 ∈ t.1.1 := by
    have hOldImage : Std i y0 ∈ (fun z : X => Std i z) '' t.1.1 := by
      rw [sharedOldACarrierCoreMap_image
        A C.toRelStructure S R f i t]
      exact ⟨y, hBY, hY.symm⟩
    obtain ⟨z, hz, hEq⟩ := hOldImage
    exact (Std i).injective hEq ▸ hz
  have hSameWitness :
      Quotient.mk (U.wagonSetoid μ) (Emb i s) =
        Quotient.mk (U.wagonSetoid μ) (Emb i t) := by
    change Quotient.mk (U.wagonSetoid μ) (Emb i s) = w at hAP
    change Quotient.mk (U.wagonSetoid μ) (Emb i t) = w at hBP
    exact hAP.trans hBP.symm
  have hU : U.rel μ (Emb i s) (Emb i t) :=
    Quotient.exact hSameWitness
  have hT : T.rel μ s.1 t.1 := (hRel μ i s t).2 hU
  have hOldSame : (Old).parent t.1 = (Old).parent s.1 :=
    (Quotient.sound hT).symm
  by_cases hPair : (Old).PairEdge x0 y0
  · exact Or.inl hPair
  · exact Or.inr ⟨hPair, (Old).parent s.1, s.1, t.1,
      rfl, hOldSame, hxOld, hyOld⟩

end RealSharedLongOldTrace
end StructuralRamsey.Girth
