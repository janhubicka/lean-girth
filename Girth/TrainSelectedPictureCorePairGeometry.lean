import Girth.TrainSelectedPictureOutputIncidence
import Girth.TrainCoreWagonEmbedding
import Girth.TrainWagonPairUniqueness
import Girth.AttachmentStrongness

set_option Elab.async false

/-!
# Core-block absorption in the actual generated picture

An ambient A-edge through two distinct vertices of one CORE wagon belongs to
that wagon's generated output class. The whole core is A-strong because the
gluing subsystem is A-strong in the old picture. Factoring the ambient edge
back through the core then reduces the assertion to core wagon linearity.

The second interface starts with two actual output edges contained in the
core and sharing an arbitrary output parent. Exact generated-train restriction
recovers their common core wagon. These results do not assume output wagon
linearity or an output system-girth bound, and shared-relation preservation
suffices; reflection inside the standards is not needed.

Core linearity is a predicate on the original core-edge type and the original
core train U, with its carriers embedded in the attachment. The final two-block
equality theorem needs only that source linearity and exact core restriction;
it does not assume a pair edge or active strongness.

These are core-local blocks. They do not assert that an arbitrary generated
wagon can have both of its endpoint witnesses localized to the core.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v

section CorePair

variable {L : RelLanguage.{u}} {UA Old Core I : Type v}
variable (A : RelStructure L UA) (hA : A.Irreducible)
variable (B : RelStructure L Old) (S : Set Old) (R : RelStructure L Core)
variable (f : I → RelStructure.Embedding (B.induce S) R)

local notation "Vertex" => RelStructure.Attachment.Vertex S (W := Core) (I := I)
local notation "Attached" => RelStructure.Attachment.attach B S R f
local notation "CoreEmb" => RelStructure.Attachment.coreEmbedding B S R f
local notation "CoreEdge" => OldACarrierEdge A R
local notation "ActualEdge" => OldACarrierEdge A Attached
local notation "Emb" => sharedOldACarrierCoreEmbedding A B S R f
local notation "CoreCar" => attachedCoreAEdgeCarrier A B S R f
local notation "CoreActual" => (fun (b : CoreEdge) =>
  actualAPictureEdgeEquiv A hA B S R f
    (physicalCoreEdge (sharedOldACarrierInclusion A B S) I b))

/-- A genuine ambient A-support edge wholly in the actual core is precisely
the canonical physical image of a core support edge. -/
theorem actualASupport_core_edge_pullback
    (a : ActualEdge) (hSub : a.1 ⊆ copyCarrier CoreEmb) :
    ∃ b : CoreEdge, CoreActual b = a := by
  have hImage : a.1 ⊆ (fun x : Core => CoreEmb x) '' (Set.univ : Set Core) := by
    intro x hx
    obtain ⟨y, hy⟩ := hSub hx
    exact ⟨y, Set.mem_univ y, hy⟩
  obtain ⟨b, _, hCarrier⟩ := oldACarrierEdge_pullback_of_subset_image
    A R Attached CoreEmb Set.univ a hImage
  refine ⟨b, Subtype.ext ?_⟩
  exact (actualAPictureEdgeEquiv_core_carrier A hA B S R f b).trans hCarrier

variable {m : ℕ}
variable (T : EdgeTrainLevels (OldACarrierEdge A B) m)
variable (U : EdgeTrainLevels (OldACarrierEdge A R) m)
variable (hShared : ∀ _i : I, Nonempty (SharedOldACarrierEdge A B S))
variable (hPreserve : ∀ (ν : Fin (m + 1)) (i : I)
  (a b : SharedOldACarrierEdge A B S),
  T.rel ν a.1 b.1 →
    U.rel ν (sharedOldACarrierCoreEmbedding A B S R f i a)
      (sharedOldACarrierCoreEmbedding A B S R f i b))
variable (μ : Fin (m + 1))

local notation "Train" => generatedActualASupportTrain A hA B S R f T U hShared
local notation "Witness" => sharedWitnessOrderOneData U μ Emb CoreCar
local notation "Parent" => Quotient.mk (EdgeTrainLevels.wagonSetoid
  (generatedActualASupportTrain A hA B S R f T U hShared) μ)
local notation "CoreWagon" => generatedActualASupportTrain_coreWagonEmbedding
  A hA B S R f T U hPreserve hShared μ

include hPreserve

/-- Core wagon strongness in the entire attachment, without output linearity.
The source core's physical carrier is used, so isolated core vertices do not
create any implicit wagon incidence. -/
theorem generatedActualASupportTrain_coreWagon_pair_absorbs_edge
    (hActive : AStrong A B S) (hLinear : (Witness).LinearPretrain)
    (w : Quotient (U.wagonSetoid μ)) (p : ActualEdge) (x y : Vertex)
    (hxy : x ≠ y) (hx : x ∈ p.1) (hy : y ∈ p.1)
    (hxw : (Witness).WagonVertex w x) (hyw : (Witness).WagonVertex w y) :
    Parent p = CoreWagon w := by
  have hCore : AStrong A Attached (copyCarrier CoreEmb) :=
    attachment_core_aStrong B S R f hA hActive
  have vertexInCore (z : Vertex) (hz : (Witness).WagonVertex w z) :
      z ∈ copyCarrier CoreEmb := by
    obtain ⟨a, _, u, _, huz⟩ := hz
    exact ⟨u, huz⟩
  have hSub : p.1 ⊆ copyCarrier CoreEmb :=
    oldACarrier_subset_of_two_mem_aStrong A Attached (copyCarrier CoreEmb)
      hCore p x y hxy hx hy (vertexInCore x hxw) (vertexInCore y hyw)
  obtain ⟨a, ha⟩ := actualASupport_core_edge_pullback A hA B S R f p hSub
  have hxa : x ∈ (Witness).edgeCarrier a := by
    change x ∈ CoreCar a
    rw [← actualAPictureEdgeEquiv_core_carrier A hA B S R f a, ha]
    exact hx
  have hya : y ∈ (Witness).edgeCarrier a := by
    change y ∈ CoreCar a
    rw [← actualAPictureEdgeEquiv_core_carrier A hA B S R f a, ha]
    exact hy
  have hParent : (Witness).parent a = w :=
    OrderOneData.parent_eq_of_two_vertices_in_wagon
      (Witness) hLinear a w x y hxa hya hxw hyw hxy
  calc
    Parent p = Parent (CoreActual a) := congrArg Parent ha.symm
    _ = CoreWagon ((Witness).parent a) :=
      (generatedActualASupportTrain_coreWagonEmbedding_mk
        A hA B S R f T U hPreserve hShared μ a).symm
    _ = CoreWagon w := congrArg CoreWagon hParent

/-- An arbitrary output parent witnessed at both endpoints by actual edges
contained in the core absorbs every ambient A-edge through that pair. -/
theorem generatedActualASupportTrain_parent_eq_of_core_pair
    (hActive : AStrong A B S) (hLinear : (Witness).LinearPretrain)
    (a b p : ActualEdge) (W : Quotient ((Train).wagonSetoid μ))
    (x y : Vertex) (hxy : x ≠ y)
    (haSub : a.1 ⊆ copyCarrier CoreEmb) (hbSub : b.1 ⊆ copyCarrier CoreEmb)
    (haW : Parent a = W) (hbW : Parent b = W)
    (hxa : x ∈ a.1) (hyb : y ∈ b.1) (hxp : x ∈ p.1) (hyp : y ∈ p.1) :
    Parent p = W := by
  obtain ⟨a₀, ha⟩ := actualASupport_core_edge_pullback A hA B S R f a haSub
  obtain ⟨b₀, hb⟩ := actualASupport_core_edge_pullback A hA B S R f b hbSub
  have hOut : (Train).rel μ (CoreActual b₀) (CoreActual a₀) := by
    apply Quotient.exact
    change Parent (CoreActual b₀) = Parent (CoreActual a₀)
    rw [ha, hb]
    exact hbW.trans haW.symm
  have hSource : U.rel μ b₀ a₀ :=
    (generatedActualASupportTrain_restrict_core
      A hA B S R f T U hPreserve hShared μ b₀ a₀).mp hOut
  have hxa₀ : x ∈ CoreCar a₀ := by
    rw [← actualAPictureEdgeEquiv_core_carrier A hA B S R f a₀, ha]
    exact hxa
  have hyb₀ : y ∈ CoreCar b₀ := by
    rw [← actualAPictureEdgeEquiv_core_carrier A hA B S R f b₀, hb]
    exact hyb
  have hxW : (Witness).WagonVertex ((Witness).parent a₀) x :=
    ⟨a₀, rfl, hxa₀⟩
  have hyW : (Witness).WagonVertex ((Witness).parent a₀) y :=
    ⟨b₀, Quotient.sound hSource, hyb₀⟩
  calc
    Parent p = CoreWagon ((Witness).parent a₀) :=
      generatedActualASupportTrain_coreWagon_pair_absorbs_edge
        A hA B S R f T U hShared hPreserve μ hActive hLinear
        ((Witness).parent a₀) p x y hxy hxp hyp hxW hyW
    _ = Parent (CoreActual a₀) :=
      generatedActualASupportTrain_coreWagonEmbedding_mk
        A hA B S R f T U hPreserve hShared μ a₀
    _ = Parent a := congrArg Parent ha
    _ = W := haW

/-- Two core-local physical blocks through the same distinct pair have equal
output parents. This needs no ambient pair edge and no strongness hypothesis. -/
theorem generatedActualASupportTrain_core_blocks_parent_eq
    (hLinear : (Witness).LinearPretrain)
    (a b c d : ActualEdge) (W₁ W₂ : Quotient ((Train).wagonSetoid μ))
    (x y : Vertex) (hxy : x ≠ y)
    (haSub : a.1 ⊆ copyCarrier CoreEmb) (hbSub : b.1 ⊆ copyCarrier CoreEmb)
    (hcSub : c.1 ⊆ copyCarrier CoreEmb) (hdSub : d.1 ⊆ copyCarrier CoreEmb)
    (haW : Parent a = W₁) (hbW : Parent b = W₁)
    (hcW : Parent c = W₂) (hdW : Parent d = W₂)
    (hxa : x ∈ a.1) (hyb : y ∈ b.1) (hxc : x ∈ c.1) (hyd : y ∈ d.1) :
    W₁ = W₂ := by
  obtain ⟨a₀, ha⟩ := actualASupport_core_edge_pullback A hA B S R f a haSub
  obtain ⟨b₀, hb⟩ := actualASupport_core_edge_pullback A hA B S R f b hbSub
  obtain ⟨c₀, hc⟩ := actualASupport_core_edge_pullback A hA B S R f c hcSub
  obtain ⟨d₀, hd⟩ := actualASupport_core_edge_pullback A hA B S R f d hdSub
  have hBA : (Witness).parent b₀ = (Witness).parent a₀ := by
    apply Quotient.sound
    apply (generatedActualASupportTrain_restrict_core
      A hA B S R f T U hPreserve hShared μ b₀ a₀).mp
    apply Quotient.exact
    change Parent (CoreActual b₀) = Parent (CoreActual a₀)
    rw [ha, hb]
    exact hbW.trans haW.symm
  have hDC : (Witness).parent d₀ = (Witness).parent c₀ := by
    apply Quotient.sound
    apply (generatedActualASupportTrain_restrict_core
      A hA B S R f T U hPreserve hShared μ d₀ c₀).mp
    apply Quotient.exact
    change Parent (CoreActual d₀) = Parent (CoreActual c₀)
    rw [hc, hd]
    exact hdW.trans hcW.symm
  have hxa₀ : x ∈ CoreCar a₀ := by
    rw [← actualAPictureEdgeEquiv_core_carrier A hA B S R f a₀, ha]
    exact hxa
  have hyb₀ : y ∈ CoreCar b₀ := by
    rw [← actualAPictureEdgeEquiv_core_carrier A hA B S R f b₀, hb]
    exact hyb
  have hxc₀ : x ∈ CoreCar c₀ := by
    rw [← actualAPictureEdgeEquiv_core_carrier A hA B S R f c₀, hc]
    exact hxc
  have hyd₀ : y ∈ CoreCar d₀ := by
    rw [← actualAPictureEdgeEquiv_core_carrier A hA B S R f d₀, hd]
    exact hyd
  have hAC : (Witness).parent a₀ = (Witness).parent c₀ :=
    OrderOneData.wagon_eq_of_common_vertex_pair
      (Witness) hLinear ((Witness).parent a₀) ((Witness).parent c₀) x y
      ⟨a₀, rfl, hxa₀⟩ ⟨b₀, hBA, hyb₀⟩ ⟨c₀, rfl, hxc₀⟩ ⟨d₀, hDC, hyd₀⟩ hxy
  have hOut : Parent (CoreActual a₀) = Parent (CoreActual c₀) :=
    Quotient.sound ((generatedActualASupportTrain_restrict_core
      A hA B S R f T U hPreserve hShared μ a₀ c₀).mpr (Quotient.exact hAC))
  rw [ha, hc] at hOut
  exact haW.symm.trans (hOut.trans hcW)

end CorePair

end StructuralRamsey.Girth
