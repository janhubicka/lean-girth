import Girth.TrainSelectedPictureWagonPairGeometry
import Girth.TrainSelectedPictureCorePairGeometry
import Girth.TrainTwoCopyLongProbe

/-!
# A standard block and a core block through the same pair

The missing core/standard case uses the existing three-occurrence long probe
inside the core witness. If its two vertices have no common core A-edge, the
probe is acceptable and its only designated label supplies two shared edges
through those vertices in the specified core wagon. These edges are genuine
old edges in the standard, so old wagon linearity identifies the two output
parents. If a core pair edge exists, whole-standard strongness absorbs it and
the checked pair-absorption theorem applies.

Only the no-pair branch invokes an acceptable three-cycle. The auxiliary
three-edge cycle with a common ambient pair edge is never called acceptable.
Neither output wagon linearity nor the general cycle-transfer theorem is an
input. The two endpoint edges of each block must still lie in one piece.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v

/-- The checked long probe supplies genuine shared representatives of a
core wagon inside any witness copy containing its two distinct vertices.
The output retains the specified wagon, rather than merely some long piece. -/
theorem sharedWitness_copy_wagon_pair_shared_edges
    {V E Shared I : Type v} {m : ℕ}
    (U : EdgeTrainLevels E m) (μ : Fin (m + 1))
    (emb : I → Shared ↪ E) (carrier : E → Set V)
    (hLinear : (sharedWitnessOrderOneData U μ emb carrier).LinearPretrain)
    (hBound : (sharedWitnessOrderOneData U μ emb carrier).LocalPieceSystemBound 2)
    (i : I) (w : Quotient (U.wagonSetoid μ)) (x y : V) (hxy : x ≠ y)
    (hxCopy : x ∈ (sharedWitnessOrderOneData U μ emb carrier).copyCarrier i)
    (hyCopy : y ∈ (sharedWitnessOrderOneData U μ emb carrier).copyCarrier i)
    (hxW : (sharedWitnessOrderOneData U μ emb carrier).WagonVertex w x)
    (hyW : (sharedWitnessOrderOneData U μ emb carrier).WagonVertex w y)
    (hNoPair : ¬ (sharedWitnessOrderOneData U μ emb carrier).PairEdge x y) :
    ∃ s t : Shared,
      Quotient.mk (U.wagonSetoid μ) (emb i s) = w ∧
      Quotient.mk (U.wagonSetoid μ) (emb i t) = w ∧
      x ∈ carrier (emb i s) ∧ y ∈ carrier (emb i t) := by
  let D := sharedWitnessOrderOneData U μ emb carrier
  obtain ⟨a, haw, hxa⟩ := hxW
  obtain ⟨b, hbw, hyb⟩ := hyW
  have hab : a ≠ b := by
    intro h
    exact hNoPair ⟨a, hxa, h.symm ▸ hyb⟩
  have hLong : D.LongPiece (.inl i) (.inl x) (.inl y) :=
    D.copy_long_piece_of_two_edge_probe hBound i a b w x y
      hab hxy hxCopy hyCopy haw hbw hxa hyb hNoPair
  obtain ⟨c, d, hc, hd, _, hcw, hdw, hxc, hyd, _⟩ :=
    D.longPiece_edges_in_given_wagon hLinear (.inl i) w x y
      ⟨a, haw, hxa⟩ ⟨b, hbw, hyb⟩ hxy hLong
  change c ∈ Set.range (emb i) at hc
  change d ∈ Set.range (emb i) at hd
  obtain ⟨s, hs⟩ := hc
  obtain ⟨t, ht⟩ := hd
  refine ⟨s, t, ?_, ?_, ?_, ?_⟩
  · rw [hs]
    exact hcw
  · rw [ht]
    exact hdw
  · rw [hs]
    exact hxc
  · rw [ht]
    exact hyd

section Attachment

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
variable (hShared : ∀ _i : I, Nonempty (SharedOldACarrierEdge A C.toRelStructure
  (activeCarrier A C e.toFunctionEmbedding)))
variable (μ : Fin (m + 1))

local notation "S" => activeCarrier A C e.toFunctionEmbedding
local notation "Vertex" => RelStructure.Attachment.Vertex S (W := Y) (I := I)
local notation "OldEdge" => OldACarrierEdge A C.toRelStructure
local notation "CoreEdge" => OldACarrierEdge A R
local notation "Actual" => RelStructure.Attachment.attach C.toRelStructure S R f
local notation "ActualEdge" => OldACarrierEdge A Actual
local notation "Std" => RelStructure.Attachment.copyEmbedding C.toRelStructure S R f
local notation "CoreEmb" => RelStructure.Attachment.coreEmbedding C.toRelStructure S R f
local notation "Emb" => sharedOldACarrierCoreEmbedding A C.toRelStructure S R f
local notation "CoreCar" => attachedCoreAEdgeCarrier A C.toRelStructure S R f
local notation "StdEdge" => (fun (i : I) (a : OldEdge) =>
  actualAPictureEdgeEquiv A hA C.toRelStructure S R f
    (physicalStandardEdge (sharedOldACarrierInclusion A C.toRelStructure S) Emb i a))
local notation "CoreActual" => (fun (a : CoreEdge) =>
  actualAPictureEdgeEquiv A hA C.toRelStructure S R f
    (physicalCoreEdge (sharedOldACarrierInclusion A C.toRelStructure S) I a))
local notation "Train" => generatedActualASupportTrain A hA C.toRelStructure S R f T U hShared
local notation "Old" => selectedPictureOrderOneData A B D C family selected T μ
local notation "Witness" => sharedWitnessOrderOneData U μ Emb CoreCar
local notation "Out" => attachedSelectedPictureOrderOneData
  A hA B D C family selected e R f T U hShared μ

variable (hRel : ∀ (ν : Fin (m + 1)) (k : I)
  (p q : SharedOldACarrierEdge A C.toRelStructure S),
  T.rel ν p.1 q.1 ↔ U.rel ν (Emb k p) (Emb k q))

include hRel

/-- A standard-local physical block and a core-local physical block through
the same distinct pair have equal output parents. Only core system-girth at
order two is used; the old input is wagon linearity, not old system-girth. -/
theorem attachedSelectedPicture_standard_core_blocks_parent_eq
    (hOld : (Old).LinearPretrain) (hCore : (Witness).FullSystemGirthGT 2)
    (i : I) (hStdStrong : AStrong A Actual (copyCarrier (Std i)))
    (a b c d : ActualEdge) (x y : Vertex)
    (W₁ W₂ : Quotient ((Train).wagonSetoid μ)) (hxy : x ≠ y)
    (haSub : a.1 ⊆ copyCarrier (Std i)) (hbSub : b.1 ⊆ copyCarrier (Std i))
    (hcSub : c.1 ⊆ copyCarrier CoreEmb) (hdSub : d.1 ⊆ copyCarrier CoreEmb)
    (ha : (Out).parent a = W₁) (hb : (Out).parent b = W₁)
    (hc : (Out).parent c = W₂) (hd : (Out).parent d = W₂)
    (hxa : x ∈ a.1) (hyb : y ∈ b.1) (hxc : x ∈ c.1) (hyd : y ∈ d.1) :
    W₁ = W₂ := by
  classical
  let preserve := fun (ν : Fin (m + 1)) (k : I)
      (s t : SharedOldACarrierEdge A C.toRelStructure S) => (hRel ν k s t).mp
  by_cases hPair : (Witness).PairEdge x y
  · obtain ⟨p, hxp, hyp⟩ := hPair
    have hpSub : (CoreActual p).1 ⊆ copyCarrier CoreEmb := by
      intro z hz
      obtain ⟨u, _, huz⟩ := hz
      exact ⟨u, huz⟩
    have hFirst : (Out).parent (CoreActual p) = W₁ :=
      attachedSelectedPicture_parent_eq_of_standard_pair
        A hA B D C family selected e R f T U hShared μ hRel hOld
        i hStdStrong a b (CoreActual p) x y W₁ hxy
        haSub hbSub ha hb hxa hyb hxp hyp
    have hSecond : W₂ = (Out).parent (CoreActual p) :=
      generatedActualASupportTrain_core_blocks_parent_eq
        A hA C.toRelStructure S R f T U hShared preserve μ hCore.1
        c d (CoreActual p) (CoreActual p) W₂ ((Out).parent (CoreActual p))
        x y hxy hcSub hdSub hpSub hpSub hc hd rfl rfl hxc hyd hxp hyp
    exact hFirst.symm.trans hSecond.symm
  · obtain ⟨c₀, hc₀⟩ := actualASupport_core_edge_pullback
      A hA C.toRelStructure S R f c hcSub
    obtain ⟨d₀, hd₀⟩ := actualASupport_core_edge_pullback
      A hA C.toRelStructure S R f d hdSub
    have hDC : (Witness).parent d₀ = (Witness).parent c₀ := by
      apply Quotient.sound
      apply (generatedActualASupportTrain_restrict_core
        A hA C.toRelStructure S R f T U preserve hShared μ d₀ c₀).mp
      apply Quotient.exact
      change (Out).parent (CoreActual d₀) = (Out).parent (CoreActual c₀)
      rw [hc₀, hd₀]
      exact hd.trans hc.symm
    have hxc₀ : x ∈ CoreCar c₀ := by
      rw [← actualAPictureEdgeEquiv_core_carrier A hA C.toRelStructure S R f c₀, hc₀]
      exact hxc
    have hyd₀ : y ∈ CoreCar d₀ := by
      rw [← actualAPictureEdgeEquiv_core_carrier A hA C.toRelStructure S R f d₀, hd₀]
      exact hyd
    have hxCopy : x ∈ (Witness).copyCarrier i :=
      activeAttached_mem_sharedWitness_of_standard_core
        A C e.toFunctionEmbedding R f U μ i x (haSub hxa) (hcSub hxc)
    have hyCopy : y ∈ (Witness).copyCarrier i :=
      activeAttached_mem_sharedWitness_of_standard_core
        A C e.toFunctionEmbedding R f U μ i y (hbSub hyb) (hdSub hyd)
    obtain ⟨s, t, hs, ht, hxs, hyt⟩ := sharedWitness_copy_wagon_pair_shared_edges
      U μ Emb CoreCar hCore.1
      ((Witness).localPieceSystemBound_of_supremeCycleBound 2 hCore.2)
      i ((Witness).parent c₀) x y hxy hxCopy hyCopy
      ⟨c₀, rfl, hxc₀⟩ ⟨d₀, hDC, hyd₀⟩ hPair
    have sharedImage (r : SharedOldACarrierEdge A C.toRelStructure S) :
        StdEdge i r.1 = CoreActual (Emb i r) := by
      change actualAPictureEdgeEquiv A hA C.toRelStructure S R f
          (physicalStandardEdge (sharedOldACarrierInclusion A C.toRelStructure S)
            Emb i ((sharedOldACarrierInclusion A C.toRelStructure S) r)) = _
      rw [physicalStandardEdge_shared]
    have parentW (r : SharedOldACarrierEdge A C.toRelStructure S)
        (hr : (Witness).parent (Emb i r) = (Witness).parent c₀) :
        (Out).parent (StdEdge i r.1) = W₂ := by
      rw [sharedImage r]
      have hSource : U.rel μ (Emb i r) c₀ := Quotient.exact hr
      have hOut : (Out).parent (CoreActual (Emb i r)) =
          (Out).parent (CoreActual c₀) :=
        Quotient.sound ((generatedActualASupportTrain_restrict_core
          A hA C.toRelStructure S R f T U preserve hShared μ (Emb i r) c₀).mpr hSource)
      rw [hc₀] at hOut
      exact hOut.trans hc
    have hxs' : x ∈ (StdEdge i s.1).1 := by
      rw [sharedImage s]
      exact hxs
    have hyt' : y ∈ (StdEdge i t.1).1 := by
      rw [sharedImage t]
      exact hyt
    obtain ⟨a₀, rfl⟩ := attachedSelectedPicture_geometric_edge_pullback
      A hA D C e R f i a haSub
    obtain ⟨b₀, rfl⟩ := attachedSelectedPicture_geometric_edge_pullback
      A hA D C e R f i b hbSub
    exact attachedSelectedPicture_same_standard_blocks_parent_eq
      A hA B D C family selected e R f T U hShared μ hRel hOld
      i a₀ b₀ s.1 t.1 x y W₁ W₂ hxy
      ha hb (parentW s hs) (parentW t ht) hxa hyb hxs' hyt'

end Attachment

end StructuralRamsey.Girth
