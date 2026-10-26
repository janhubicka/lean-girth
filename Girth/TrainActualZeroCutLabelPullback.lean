import Girth.TrainCyclicOwnerRuns
import Girth.TrainSelectedCycleGeometricWagon
import Girth.TrainForeignDesignatedSupport

/-!
# Zero geometric cuts: one actual standard with faithful selected labels

The absence of owner cuts is already known for a *minimum* owner
assignment to imply geometric containment in one standard. Here the
forward direction is proved for ANY geometrically admissible
assignment, with no minimization premise.

Geometric containment alone does not identify the designated label:
a designated output label initially belongs to its attached source
standard, potentially different from the containing standard. Under
the actual two-support-edge and A-strong hypotheses, foreign
designated labels are excluded by the previously checked support
uniqueness theorem. Every ambient A-edge label pulls back through
the chosen standard by the physical edge factorization theorem.

The result constructs faithful SOURCE LABELS for every occurrence of
a zero-cut output BigCycle. It does not yet construct the old-cycle
wagon quotient and connector word, nor transfer its acceptance or
supreme-copy witnesses. No appendix.
-/

namespace StructuralRamsey.Girth
open StructuralRamsey.RelStructure

universe u v
section ZeroCutSelectedPicture

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
local notation "OldEdge" => OldACarrierEdge A C.toRelStructure
local notation "ActualEdge" =>
  OldACarrierEdge A (RelStructure.Attachment.attach C.toRelStructure S R f)
local notation "Selected" => {q : DesignatedCopy B D C family // q ∈ selected}
local notation "Label" => Selected ⊕ OldEdge
local notation "Std" =>
  RelStructure.Attachment.copyEmbedding C.toRelStructure S R f
local notation "Out" => attachedSelectedPictureOrderOneData
  A hA B D C family selected e R f T U hShared μ
local notation "GeomAllowed" => selectedOutputGeometricOwnerAllowed
  A hA B D C family selected e R f T U hShared μ
local notation "LabelMap" => attachedSelectedPictureLabel
  A hA B D C family selected e R f

/-- ANY geometrically admissible owner assignment with no cuts names
one actual standard at all occurrences. The old minimum-owner
hypothesis is unnecessary in this forward direction. A repeated
core-edge owner is impossible by adjacent-label distinctness. -/
theorem attachedSelectedPicture_zero_cut_standard
    {n : ℕ} (K : (Out).BigCycle n)
    (owner : Fin n → I ⊕ CoreEdge)
    (hAllowed : ∀ k : Fin n, GeomAllowed (K.label k) (owner k))
    (hZero : cyclicOwnerChanges owner = 0) :
    ∃ i : I, ∀ k : Fin n,
      owner k = Sum.inl i ∧
      (Out).carrier (K.label k) ⊆ copyCarrier (Std i) := by
  have hn : 0 < n := by
    have h := K.length_ge_two
    omega
  obtain ⟨o, ho⟩ :=
    (cyclicOwnerChanges_zero_iff_constant hn owner).mp hZero
  cases hO : o with
  | inl i =>
      refine ⟨i, ?_⟩
      intro k
      have hk : owner k = Sum.inl i := (ho k).trans hO
      refine ⟨hk, ?_⟩
      have h := hAllowed k
      rw [hk] at h
      exact h
  | inr b =>
      let k : Fin n := ⟨0, hn⟩
      have hk : owner k = Sum.inr b := (ho k).trans hO
      have hnext : owner (cyclicSucc k) = Sum.inr b :=
        (ho (cyclicSucc k)).trans hO
      exact False.elim
        ((attachedSelectedPicture_geometric_core_owner_isolated
          A hA B D C family selected e R f T U hShared μ
          K owner hAllowed k b hk).2 hnext)

/-- Under the two-distinct-support-edge condition, ANY designated
output occurrence geometrically contained in a standard must carry
that standard's ORIGINAL designated label. A physical edge output
occurrence likewise has its literal preimage edge label.
Neither inclusion of carriers nor equality of carriers is substituted
for equality of labels. -/
theorem attachedSelectedPicture_standard_label_pullback [Finite UA]
    (hStrong : ∀ b : RelStructure.Embedding B D, b ∈ family →
      AStrong A D (copyCarrier b))
    (hTwo : ∀ q : Selected, ∃ r s : OldEdge,
      r ≠ s ∧ r.1 ⊆ copyCarrier q.1.embedding ∧
        s.1 ⊆ copyCarrier q.1.embedding)
    (i : I) (a : (I × Selected) ⊕ ActualEdge)
    (hContained : (Out).carrier a ⊆ copyCarrier (Std i)) :
    ∃ old : Label, LabelMap i old = a := by
  cases a with
  | inl iq =>
      obtain ⟨j, q⟩ := iq
      have hji : j = i := by
        by_contra hne
        obtain ⟨r, s, hrs, hr, hs⟩ := hTwo q
        have hNo := foreign_designated_two_edges_not_contained
          A B D C family e R f q.1 j i hne
          (hStrong q.1.base q.1.base_mem) r s hr hs hrs
        exact hNo hContained
      subst j
      exact ⟨Sum.inl q, rfl⟩
  | inr edge =>
      have hSub : edge.1 ⊆ copyCarrier (Std i) := hContained
      obtain ⟨old, hEq⟩ :=
        attachedSelectedPicture_geometric_edge_pullback
          A hA D C e R f i edge hSub
      exact ⟨Sum.inr old, congrArg Sum.inr hEq⟩

/-- A zero-cut selected-picture BigCycle with nontrivial strong
designated target support has faithful old LABELS at every position
inside ONE attached standard. No old wagon cycle is claimed yet. -/
theorem attachedSelectedPicture_zero_cut_source_labels [Finite UA]
    (hStrong : ∀ b : RelStructure.Embedding B D, b ∈ family →
      AStrong A D (copyCarrier b))
    (hTwo : ∀ q : Selected, ∃ r s : OldEdge,
      r ≠ s ∧ r.1 ⊆ copyCarrier q.1.embedding ∧
        s.1 ⊆ copyCarrier q.1.embedding)
    {n : ℕ} (K : (Out).BigCycle n)
    (owner : Fin n → I ⊕ CoreEdge)
    (hAllowed : ∀ k : Fin n, GeomAllowed (K.label k) (owner k))
    (hZero : cyclicOwnerChanges owner = 0) :
    ∃ i : I, ∀ k : Fin n,
      ∃ old : Label, LabelMap i old = K.label k := by
  obtain ⟨i, hOwner⟩ :=
    attachedSelectedPicture_zero_cut_standard
      A hA B D C family selected e R f T U hShared μ
      K owner hAllowed hZero
  refine ⟨i, ?_⟩
  intro k
  exact attachedSelectedPicture_standard_label_pullback
    A hA B D C family selected e R f T U hShared μ
    hStrong hTwo i (K.label k) (hOwner k).2

end ZeroCutSelectedPicture
end StructuralRamsey.Girth
