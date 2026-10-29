import Girth.TrainSelectedPictureContainedBlocks
import Girth.TrainSelectedCycleGeometricWagon
import Girth.TrainActualStandardStrongFromBase
import Girth.TrainActualStandardWagonMap
import Girth.TrainWagonPairUniqueness

-- Elaborate these dependent attachment interfaces synchronously on the pinned
-- Lean release candidate, retaining ordinary kernel checking and diagnostics.
set_option Elab.async false

/-!
# Noncircular wagon geometry for two standard-local edge blocks

The old and core trains are linear; linearity of the generated output train
is not assumed. A physical edge meeting two vertices of one old wagon block
in a strong attached standard belongs to that same generated wagon. The
pair edge is first absorbed into the whole standard and pulled back as a
physical A-edge. Only old wagon linearity is then used.

For two blocks carried by distinct standards, the existing mixed contained
block obstruction supplies an actual core pair edge. Applying the preceding
argument in both standards identifies their output wagon classes. The case
of a single standard uses exact train restriction and old wagon linearity.

The result concerns blocks whose two witnessing edges lie in one standard.
It does not assert that an arbitrary pair of output wagon vertices has such
a localization. Whole gluing-image strongness remains explicit, and no
acceptability assertion is made for an auxiliary cycle.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v

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
local notation "Actual" => RelStructure.Attachment.attach C.toRelStructure S R f
local notation "ActualEdge" => OldACarrierEdge A Actual
local notation "Std" => RelStructure.Attachment.copyEmbedding C.toRelStructure S R f
local notation "Emb" => sharedOldACarrierCoreEmbedding A C.toRelStructure S R f
local notation "CoreCar" => attachedCoreAEdgeCarrier A C.toRelStructure S R f
local notation "StdEdge" => (fun (i : I) (a : OldEdge) =>
  actualAPictureEdgeEquiv A hA C.toRelStructure S R f
    (physicalStandardEdge (sharedOldACarrierInclusion A C.toRelStructure S) Emb i a))
local notation "CoreActual" => (fun (a : OldACarrierEdge A R) =>
  actualAPictureEdgeEquiv A hA C.toRelStructure S R f
    (physicalCoreEdge (sharedOldACarrierInclusion A C.toRelStructure S) I a))
local notation "Train" => generatedActualASupportTrain A hA C.toRelStructure S R f T U hShared
local notation "Old" => selectedPictureOrderOneData A B D C family selected T μ
local notation "Witness" => sharedWitnessOrderOneData U μ Emb CoreCar
local notation "Out" => attachedSelectedPictureOrderOneData
  A hA B D C family selected e R f T U hShared μ

variable (hRel : ∀ (ν : Fin (m + 1)) (k : I)
  (p q : SharedOldACarrierEdge A C.toRelStructure
    (activeCarrier A C e.toFunctionEmbedding)),
  T.rel ν p.1 q.1 ↔
    U.rel ν
      (sharedOldACarrierCoreEmbedding A C.toRelStructure
        (activeCarrier A C e.toFunctionEmbedding) R f k p)
      (sharedOldACarrierCoreEmbedding A C.toRelStructure
        (activeCarrier A C e.toFunctionEmbedding) R f k q))

include hRel

local notation "StdWagon" => generatedActualASupportTrain_standardWagonEmbedding
  A hA C.toRelStructure S R f T U hRel hShared μ

/-- Two source-edge blocks in the same standard and through the same distinct
vertices have the same generated parent. The output wagon partition is used
only through its exact restriction to that standard. -/
theorem attachedSelectedPicture_same_standard_blocks_parent_eq
    (hOld : (Old).LinearPretrain)
    (i : I) (a b c d : OldEdge) (x y : Vertex)
    (W₁ W₂ : Quotient ((Train).wagonSetoid μ)) (hxy : x ≠ y)
    (ha : (Out).parent (StdEdge i a) = W₁)
    (hb : (Out).parent (StdEdge i b) = W₁)
    (hc : (Out).parent (StdEdge i c) = W₂)
    (hd : (Out).parent (StdEdge i d) = W₂)
    (hxa : x ∈ (StdEdge i a).1) (hyb : y ∈ (StdEdge i b).1)
    (hxc : x ∈ (StdEdge i c).1) (hyd : y ∈ (StdEdge i d).1) :
    W₁ = W₂ := by
  let σ : Quotient (T.wagonSetoid μ) ↪ Quotient ((Train).wagonSetoid μ) := StdWagon i
  have hMap (r : OldEdge) : σ ((Old).parent r) = (Out).parent (StdEdge i r) := rfl
  have hMem (r : OldEdge) (z : Vertex) (hz : z ∈ (StdEdge i r).1) :
      z ∈ (fun t : X => Std i t) '' r.1 := by
    exact Eq.mp (congrArg (fun Z : Set Vertex => z ∈ Z)
      (actualAPictureEdgeEquiv_standard_carrier A hA C.toRelStructure S R f i r)) hz
  obtain ⟨x₀, hxA, hxx⟩ := hMem a x hxa
  obtain ⟨y₀, hyB, hyy⟩ := hMem b y hyb
  have hxC : x₀ ∈ c.1 := by
    obtain ⟨z, hz, hzx⟩ := hMem c x hxc
    have hzx₀ : z = x₀ := (Std i).injective (hzx.trans hxx.symm)
    exact Eq.mp (congrArg (fun t : X => t ∈ c.1) hzx₀) hz
  have hyD : y₀ ∈ d.1 := by
    obtain ⟨z, hz, hzy⟩ := hMem d y hyd
    have hzy₀ : z = y₀ := (Std i).injective (hzy.trans hyy.symm)
    exact Eq.mp (congrArg (fun t : X => t ∈ d.1) hzy₀) hz
  have hxy₀ : x₀ ≠ y₀ := by
    intro h
    exact hxy (hxx.symm.trans ((congrArg (fun z : X => Std i z) h).trans hyy))
  have hBA : (Old).parent b = (Old).parent a :=
    σ.injective ((hMap b).trans (hb.trans (ha.symm.trans (hMap a).symm)))
  have hDC : (Old).parent d = (Old).parent c :=
    σ.injective ((hMap d).trans (hd.trans (hc.symm.trans (hMap c).symm)))
  have hAC : (Old).parent a = (Old).parent c :=
    OrderOneData.wagon_eq_of_common_vertex_pair Old hOld
      ((Old).parent a) ((Old).parent c) x₀ y₀
      ⟨a, rfl, hxA⟩ ⟨b, hBA, hyB⟩ ⟨c, rfl, hxC⟩ ⟨d, hDC, hyD⟩ hxy₀
  have hOut : (Out).parent (StdEdge i a) = (Out).parent (StdEdge i c) :=
    (hMap a).symm.trans
      ((congrArg (fun p : Quotient (T.wagonSetoid μ) => σ p) hAC).trans (hMap c))
  exact ha.symm.trans (hOut.trans hc)

/-- An ambient pair edge through a standard-local physical wagon block has
the block's generated parent. Strongness is required of the whole standard;
the linearity argument takes place entirely in the old train. -/
theorem attachedSelectedPicture_parent_eq_of_standard_pair
    (hOld : (Old).LinearPretrain)
    (i : I) (hStdStrong : AStrong A Actual (copyCarrier (Std i)))
    (a b g : ActualEdge) (x y : Vertex)
    (W : Quotient ((Train).wagonSetoid μ)) (hxy : x ≠ y)
    (haSub : a.1 ⊆ copyCarrier (Std i))
    (hbSub : b.1 ⊆ copyCarrier (Std i))
    (ha : (Out).parent a = W) (hb : (Out).parent b = W)
    (hxa : x ∈ a.1) (hyb : y ∈ b.1)
    (hxg : x ∈ g.1) (hyg : y ∈ g.1) :
    (Out).parent g = W := by
  have hgSub : g.1 ⊆ copyCarrier (Std i) :=
    oldACarrier_subset_of_two_mem_aStrong A Actual (copyCarrier (Std i))
      hStdStrong g x y hxy hxg hyg (haSub hxa) (hbSub hyb)
  obtain ⟨a₀, rfl⟩ := attachedSelectedPicture_geometric_edge_pullback
    A hA D C e R f i a haSub
  obtain ⟨b₀, rfl⟩ := attachedSelectedPicture_geometric_edge_pullback
    A hA D C e R f i b hbSub
  obtain ⟨g₀, rfl⟩ := attachedSelectedPicture_geometric_edge_pullback
    A hA D C e R f i g hgSub
  exact (attachedSelectedPicture_same_standard_blocks_parent_eq
    A hA B D C family selected e R f T U hShared μ hRel hOld
    i a₀ b₀ g₀ g₀ x y W ((Out).parent (StdEdge i g₀)) hxy
    ha hb rfl rfl hxa hyb hxg hyg).symm

/-- Actual two-standard physical edge blocks through two distinct vertices
have equal generated parent wagons. The standards may coincide, and each
block may repeat its edge. The old/core bounds and strong whole gluing images
are inputs; output `LinearPretrain` and output system-girth are not. -/
theorem attachedSelectedPicture_standard_blocks_parent_eq [Finite UA]
    (hPartite : C.IsPartiteOver D) (hBaseLinear : ALinear A D)
    (hRigid : ∀ b : RelStructure.Embedding A D, SameCopy b e → b = e)
    (hStrong : ∀ b : RelStructure.Embedding B D, b ∈ family → AStrong A D (copyCarrier b))
    (hFull : (Old).FullSystemGirthGT 2) (hCore : (Witness).FullSystemGirthGT 2)
    (hCoreStrong : ∀ i : I, AStrong A R (copyCarrier (f i)))
    (i j : I) (a b c d : ActualEdge) (x y : Vertex)
    (W₁ W₂ : Quotient ((Train).wagonSetoid μ)) (hxy : x ≠ y)
    (haSub : a.1 ⊆ copyCarrier (Std i))
    (hbSub : b.1 ⊆ copyCarrier (Std i))
    (hcSub : c.1 ⊆ copyCarrier (Std j))
    (hdSub : d.1 ⊆ copyCarrier (Std j))
    (ha : (Out).parent a = W₁) (hb : (Out).parent b = W₁)
    (hc : (Out).parent c = W₂) (hd : (Out).parent d = W₂)
    (hxa : x ∈ a.1) (hyb : y ∈ b.1) (hxc : x ∈ c.1) (hyd : y ∈ d.1) :
    W₁ = W₂ := by
  classical
  by_cases hij : i = j
  · subst j
    obtain ⟨a₀, rfl⟩ := attachedSelectedPicture_geometric_edge_pullback
      A hA D C e R f i a haSub
    obtain ⟨b₀, rfl⟩ := attachedSelectedPicture_geometric_edge_pullback
      A hA D C e R f i b hbSub
    obtain ⟨c₀, rfl⟩ := attachedSelectedPicture_geometric_edge_pullback
      A hA D C e R f i c hcSub
    obtain ⟨d₀, rfl⟩ := attachedSelectedPicture_geometric_edge_pullback
      A hA D C e R f i d hdSub
    exact attachedSelectedPicture_same_standard_blocks_parent_eq
      A hA B D C family selected e R f T U hShared μ hRel hFull.1
      i a₀ b₀ c₀ d₀ x y W₁ W₂ hxy ha hb hc hd hxa hyb hxc hyd
  · by_contra hW
    have hPair : (Witness).PairEdge x y :=
      attachedSelectedPicture_containedBlocks_force_core_pairEdge
        A hA B D C family selected e R f T U hShared μ
        hPartite hBaseLinear hRigid hStrong hFull hCore hRel
        i j (.inr b) (.inr a) (.inr d) (.inr c) x y W₁ W₂ hij hxy hW
        hbSub haSub hdSub hcSub
        ⟨b, rfl, hb⟩ ⟨a, rfl, ha⟩ ⟨d, rfl, hd⟩ ⟨c, rfl, hc⟩
        hyb hxa hyd hxc
    obtain ⟨g, hxg, hyg⟩ := hPair
    have hxActual : x ∈ (CoreActual g).1 := hxg
    have hyActual : y ∈ (CoreActual g).1 := hyg
    have hStdStrong (k : I) : AStrong A Actual (copyCarrier (Std k)) :=
      activeAttached_standard_aStrong_of_base_aLinear
        A hA D C hPartite hBaseLinear e hRigid R f hCoreStrong k
    have hFirst : (Out).parent (CoreActual g) = W₁ :=
      attachedSelectedPicture_parent_eq_of_standard_pair
        A hA B D C family selected e R f T U hShared μ hRel hFull.1
        i (hStdStrong i) a b (CoreActual g) x y W₁ hxy
        haSub hbSub ha hb hxa hyb hxActual hyActual
    have hSecond : (Out).parent (CoreActual g) = W₂ :=
      attachedSelectedPicture_parent_eq_of_standard_pair
        A hA B D C family selected e R f T U hShared μ hRel hFull.1
        j (hStdStrong j) c d (CoreActual g) x y W₂ hxy
        hcSub hdSub hc hd hxc hyd hxActual hyActual
    exact hW (hFirst.symm.trans hSecond)

/-- Full source-wagon carriers from any two standards have at most one
common vertex when their actual generated output wagon labels are distinct.
The labels are compared by the checked quotient embeddings, not by equality
of vertex carriers. This is the source-wagon intersection form of the
physical block theorem. -/
theorem attachedSelectedPicture_standard_wagon_carriers_inter_subsingleton [Finite UA]
    (hPartite : C.IsPartiteOver D) (hBaseLinear : ALinear A D)
    (hRigid : ∀ b : RelStructure.Embedding A D, SameCopy b e → b = e)
    (hStrong : ∀ b : RelStructure.Embedding B D, b ∈ family → AStrong A D (copyCarrier b))
    (hFull : (Old).FullSystemGirthGT 2) (hCore : (Witness).FullSystemGirthGT 2)
    (hCoreStrong : ∀ i : I, AStrong A R (copyCarrier (f i)))
    (i j : I) (p q : Quotient (T.wagonSetoid μ))
    (hWagons : StdWagon i p ≠ StdWagon j q) :
    (T.wagonClassCarrier (attachedOldAEdgeCarrier A C.toRelStructure S R f i) μ p ∩
      T.wagonClassCarrier (attachedOldAEdgeCarrier A C.toRelStructure S R f j) μ q).Subsingleton := by
  intro x hx y hy
  by_contra hxy
  obtain ⟨a, ha, hxa⟩ := T.exists_incident_representative
    (attachedOldAEdgeCarrier A C.toRelStructure S R f i) μ p x hx.1
  obtain ⟨b, hb, hyb⟩ := T.exists_incident_representative
    (attachedOldAEdgeCarrier A C.toRelStructure S R f i) μ p y hy.1
  obtain ⟨c, hc, hxc⟩ := T.exists_incident_representative
    (attachedOldAEdgeCarrier A C.toRelStructure S R f j) μ q x hx.2
  obtain ⟨d, hd, hyd⟩ := T.exists_incident_representative
    (attachedOldAEdgeCarrier A C.toRelStructure S R f j) μ q y hy.2
  have hSub (k : I) (a : OldEdge) : (StdEdge k a).1 ⊆ copyCarrier (Std k) := by
    rw [actualAPictureEdgeEquiv_standard_carrier]
    rintro z ⟨u, _hu, rfl⟩
    exact ⟨u, rfl⟩
  have hParent (k : I) (a : OldEdge) (w : Quotient (T.wagonSetoid μ))
      (ha : Quotient.mk (T.wagonSetoid μ) a = w) :
      (Out).parent (StdEdge k a) = StdWagon k w := by
    change StdWagon k (Quotient.mk (T.wagonSetoid μ) a) = StdWagon k w
    exact congrArg (StdWagon k) ha
  have hMem (k : I) (a : OldEdge) (z : Vertex)
      (hz : z ∈ attachedOldAEdgeCarrier A C.toRelStructure S R f k a) :
      z ∈ (StdEdge k a).1 := by
    rw [actualAPictureEdgeEquiv_standard_carrier]
    exact hz
  exact hWagons (attachedSelectedPicture_standard_blocks_parent_eq
    A hA B D C family selected e R f T U hShared μ hRel
    hPartite hBaseLinear hRigid hStrong hFull hCore hCoreStrong
    i j (StdEdge i a) (StdEdge i b) (StdEdge j c) (StdEdge j d)
    x y (StdWagon i p) (StdWagon j q) hxy
    (hSub i a) (hSub i b) (hSub j c) (hSub j d)
    (hParent i a p ha) (hParent i b p hb) (hParent j c q hc) (hParent j d q hd)
    (hMem i a x hxa) (hMem i b y hyb) (hMem j c x hxc) (hMem j d y hyd))

end Attachment
end StructuralRamsey.Girth
