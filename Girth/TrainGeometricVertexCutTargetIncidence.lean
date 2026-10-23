import Girth.TrainSelectedCycleGeometricCutIncidence
import Girth.TrainCoreCopyVertexCoverage

/-!
# Genuine vertex-cut incidences in the reduced witness cycle

At a geometric owner cut with a vertex connector, the previously verified
four-case geometry identifies an actual core vertex in both local pieces.
The A-generated active-copy lemma upgrades the vertex's membership in a
local embedded copy to membership in the witness's genuine SHARED-edge
designated carrier. Core-edge owners retain literal edge-carrier membership.

Thus both target incidences are proved for the actual owner names and
the exact preimage of the physical source connector. No foreign designated
output label is relabelled. Wagon-cut incidences, the entire target BigCycle
and order-one acceptability remain separate.
-/

namespace StructuralRamsey.Girth
open StructuralRamsey.RelStructure

universe u v
section GeometricVertexCutIncidence

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
local notation "CoreEdge" => OldACarrierEdge A R
local notation "CoreEmb" =>
  RelStructure.Attachment.coreEmbedding C.toRelStructure S R f
local notation "Out" => attachedSelectedPictureOrderOneData
  A hA B D C family selected e R f T U hShared μ
local notation "GeomAllowed" => selectedOutputGeometricOwnerAllowed
  A hA B D C family selected e R f T U hShared μ
local notation "Wit" => sharedWitnessOrderOneData U μ
  (sharedOldACarrierCoreEmbedding A C.toRelStructure S R f)
  (Subtype.val : CoreEdge → Set Y)

/-- Each actual physical vertex cut is incident to both geometric
owner labels in the genuine shared-edge witness, at its unique core
preimage. This strengthens the four geometric cases by identifying
the precise source label incidences rather than just copy membership. -/
theorem attachedSelectedPicture_geometric_vertex_cut_target_incidence
    {n : ℕ} (K : (Out).BigCycle n)
    (owner : Fin n → I ⊕ CoreEdge)
    (hAllowed : ∀ k : Fin n, GeomAllowed (K.label k) (owner k))
    (k : Fin n) (y : Y)
    (hVertex : K.connector k = Sum.inl (CoreEmb y))
    (hCut : owner k ≠ owner (cyclicSucc k)) :
    (Wit).Incident (owner k) (Sum.inl y) ∧
      (Wit).Incident (owner (cyclicSucc k)) (Sum.inl y) := by
  have hStandard (i : I) (hy : y ∈ copyCarrier (f i)) :
      (Wit).Incident (Sum.inl i) (Sum.inl y) := by
    change y ∈ (Wit).copyCarrier i
    exact activeCoreWitness_vertex_mem_sharedCopy
      A C e.toFunctionEmbedding R f U μ i y hy
  have hEdge (b : CoreEdge) (hy : y ∈ b.1) :
      (Wit).Incident (Sum.inr b) (Sum.inl y) := by
    change y ∈ b.1
    exact hy
  have hFour :=
    attachedSelectedPicture_geometric_vertex_cut_incidence
      A hA B D C family selected e R f T U hShared μ
      K owner hAllowed k (CoreEmb y) hVertex hCut
  rcases hFour with h | h | h | h
  · obtain ⟨i, j, _hij, hi, hj, z, hz, hzi, hzj⟩ := h
    have hzy : z = y :=
      (RelStructure.Attachment.coreEmbedding
        C.toRelStructure S R f).injective hz
    subst z
    constructor
    · rw [hi]
      exact hStandard i hzi
    · rw [hj]
      exact hStandard j hzj
  · obtain ⟨i, b, hi, hb, z, hz, hzi, hzb⟩ := h
    have hzy : z = y :=
      (RelStructure.Attachment.coreEmbedding
        C.toRelStructure S R f).injective hz
    subst z
    constructor
    · rw [hi]
      exact hStandard i hzi
    · rw [hb]
      exact hEdge b hzb
  · obtain ⟨b, i, hb, hi, z, hz, hzi, hzb⟩ := h
    have hzy : z = y :=
      (RelStructure.Attachment.coreEmbedding
        C.toRelStructure S R f).injective hz
    subst z
    constructor
    · rw [hb]
      exact hEdge b hzb
    · rw [hi]
      exact hStandard i hzi
  · obtain ⟨b, c, _hbc, hb, hc, z, hz, hzb, hzc⟩ := h
    have hzy : z = y :=
      (RelStructure.Attachment.coreEmbedding
        C.toRelStructure S R f).injective hz
    subst z
    constructor
    · rw [hb]
      exact hEdge b hzb
    · rw [hc]
      exact hEdge c hzc

end GeometricVertexCutIncidence
end StructuralRamsey.Girth
