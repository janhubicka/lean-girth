import Girth.TrainSharedOldACarrierCoreEmbedding
import Girth.TrainActualPositiveCutShortPieceLift
import Girth.TrainOldCopyLocalProbePieces
import Mathlib.Tactic

set_option autoImplicit false
set_option Elab.async false

/-!
# Path A: a TRUE witness short through two embedded core vertices
reflects to a physical OLD A-edge through their standard preimages

The shared core-witness edges of gluing copy i are precisely the
physical images of TRUE old A-support edges whose full carrier
lies in the active old gluing subsystem. Source long/short
replacement arguments must not confuse a core witness edge
with a synthetic original B-copy edge.

This lemma first establishes only the exact OLD physical PAIR
probe: if two old vertices x0,y0 have their STANDARD images
equal to the physical core embeddings of genuine witness
vertices x,y, and the lower witness standard i has a real
ShortPiece through x,y, then one old physical A-edge
contains x0 and y0. It is the old preimage s of the REAL
witness edge Emb_i(s). This is not an assumption of original
B-copy membership, and it does not map the whole source cycle.

Once x0,y0 lie in the ORIGINAL selected old B-copy and the
old SupremeCycleBound has cutoff >=2, the independent checked
two-vertex physical edge probe gives the true original-copy
local piece, which the physical map can transport to the
original output designated source label.

No appendix, manuscript or source-label identification.
-/

namespace StructuralRamsey.Girth
open StructuralRamsey.RelStructure

universe u v
section RealSharedShortOldTrace

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
variable (μ : Fin (m + 1))

local notation "S" => activeCarrier A C e.toFunctionEmbedding
local notation "Old" => selectedPictureOrderOneData
  A B D C family selected T μ
local notation "CoreEdge" => OldACarrierEdge A R
local notation "Emb" => sharedOldACarrierCoreEmbedding
  A C.toRelStructure S R f
local notation "Std" => RelStructure.Attachment.copyEmbedding
  C.toRelStructure S R f
local notation "CoreEmb" => RelStructure.Attachment.coreEmbedding
  C.toRelStructure S R f
local notation "Wit" => sharedWitnessOrderOneData U μ
  Emb (Subtype.val : CoreEdge → Set Y)

/-- The genuine support edge chosen by a lower gluing standard
through two actual core vertices has one OLD support preimage
through their exact old standard-vertex preimages. -/
theorem sharedWitness_short_two_vertices_old_pair_probe
    (i : I) (x0 y0 : X) (x y : Y)
    (hX : Std i x0 = CoreEmb x)
    (hY : Std i y0 = CoreEmb y)
    (hShort : (Wit).ShortPiece (Sum.inl i)
      (Sum.inl x) (Sum.inl y)) :
    (Old).PairEdge x0 y0 := by
  obtain ⟨b, hOwned, hAtX, hAtY⟩ := hShort
  change b ∈ Set.range (Emb i) at hOwned
  obtain ⟨s, hs⟩ := hOwned
  subst b
  have hCoreX : x ∈ (Emb i s).1 := by
    exact hAtX
  have hCoreY : y ∈ (Emb i s).1 := by
    exact hAtY
  have hStdX : Std i x0 ∈
      (fun z : X => Std i z) '' s.1.1 := by
    rw [sharedOldACarrierCoreMap_image
      A C.toRelStructure S R f i s]
    exact ⟨x, hCoreX, hX.symm⟩
  have hStdY : Std i y0 ∈
      (fun z : X => Std i z) '' s.1.1 := by
    rw [sharedOldACarrierCoreMap_image
      A C.toRelStructure S R f i s]
    exact ⟨y, hCoreY, hY.symm⟩
  obtain ⟨u, hu, hUx⟩ := hStdX
  obtain ⟨v, hv, hVy⟩ := hStdY
  have hUX : u = x0 := (Std i).injective hUx
  have hVY : v = y0 := (Std i).injective hVy
  subst u
  subst v
  exact ⟨s.1, hu, hv⟩

end RealSharedShortOldTrace
end StructuralRamsey.Girth
