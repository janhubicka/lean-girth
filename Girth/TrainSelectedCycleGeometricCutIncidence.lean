import Girth.TrainCyclicOwnerFourCases
import Girth.TrainSelectedCycleGeometricVertex
import Girth.TrainSelectedCycleGeometricWagon

/-!
# Circulation: all actual geometric cut incidences

An owner cut of a selected-picture BigCycle has exactly one of the four
standard/core types. The local physical incidence theorems are here
assembled AT EVERY genuine cyclic cut, without changing an occurrence's
source label. The result supplies a witness-core vertex or witness-core
wagon incidence appropriate to the cut and its actual connector.

It does not choose or contract maximal owner runs, identify distinct
connectors, construct a legal reduced BigCycle or prove A1--A3.
No appendix theorem is used.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v

section GeometricCutIncidence

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
local notation "OldEdge" => OldACarrierEdge A C.toRelStructure
local notation "CoreEdge" => OldACarrierEdge A R
local notation "SharedEdge" => SharedOldACarrierEdge A C.toRelStructure S
local notation "Vertex" => RelStructure.Attachment.Vertex S (W := Y) (I := I)
local notation "CoreEmb" => RelStructure.Attachment.coreEmbedding C.toRelStructure S R f
local notation "Out" => attachedSelectedPictureOrderOneData
  A hA B D C family selected e R f T U hShared μ
local notation "GeomAllowed" => selectedOutputGeometricOwnerAllowed
  A hA B D C family selected e R f T U hShared μ
local notation "Emb" => sharedOldACarrierCoreEmbedding A C.toRelStructure S R f

/-- At EVERY genuine vertex cut, the two adjacent geometric owners have
the required actual common core vertex. In particular, a foreign source
label geometrically contained in a standard is not relabelled. -/
theorem attachedSelectedPicture_geometric_vertex_cut_incidence
    {n : ℕ} (K : (Out).BigCycle n)
    (owner : Fin n → I ⊕ CoreEdge)
    (hAllowed : ∀ k : Fin n, GeomAllowed (K.label k) (owner k))
    (k : Fin n) (x : Vertex)
    (hV : K.connector k = Sum.inl x)
    (hCut : owner k ≠ owner (cyclicSucc k)) :
    (∃ (i j : I), i ≠ j ∧
      owner k = Sum.inl i ∧ owner (cyclicSucc k) = Sum.inl j ∧
      ∃ y : Y, CoreEmb y = x ∧
        y ∈ copyCarrier (f i) ∧ y ∈ copyCarrier (f j)) ∨
    (∃ (i : I) (b : CoreEdge),
      owner k = Sum.inl i ∧ owner (cyclicSucc k) = Sum.inr b ∧
      ∃ y : Y, CoreEmb y = x ∧
        y ∈ copyCarrier (f i) ∧ y ∈ b.1) ∨
    (∃ (b : CoreEdge) (i : I),
      owner k = Sum.inr b ∧ owner (cyclicSucc k) = Sum.inl i ∧
      ∃ y : Y, CoreEmb y = x ∧
        y ∈ copyCarrier (f i) ∧ y ∈ b.1) ∨
    (∃ (b c : CoreEdge), b ≠ c ∧
      owner k = Sum.inr b ∧ owner (cyclicSucc k) = Sum.inr c ∧
      ∃ y : Y, CoreEmb y = x ∧ y ∈ b.1 ∧ y ∈ c.1) := by
  rcases cyclicOwnerCut_four_cases owner k hCut with
    ⟨i, j, hij, hi, hj⟩ | ⟨i, b, hi, hb⟩ |
    ⟨b, i, hb, hi⟩ | ⟨b, c, hbc, hb, hc⟩
  · exact Or.inl ⟨i, j, hij, hi, hj,
      attachedSelectedPicture_geometric_vertex_two_standards
        A hA B D C family selected e R f T U hShared μ
        K owner hAllowed k x i j hij hV hi hj⟩
  · exact Or.inr (Or.inl ⟨i, b, hi, hb,
      attachedSelectedPicture_geometric_vertex_standard_core
        A hA B D C family selected e R f T U hShared μ
        K owner hAllowed k x i b hV hi hb⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨b, i, hb, hi,
      attachedSelectedPicture_geometric_vertex_core_standard
        A hA B D C family selected e R f T U hShared μ
        K owner hAllowed k x i b hV hb hi⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨b, c, hbc, hb, hc,
      attachedSelectedPicture_geometric_vertex_core_core
        A hA B D C family selected e R f T U hShared μ
        K owner hAllowed k x b c hV hb hc⟩))

include hRel

/-- At EVERY genuine wagon cut, actual physical edges give one of the
four witness-core wagon contacts. The old support witnesses are local
to the appropriate copies; hShared and hRel are explicit assumptions. -/
theorem attachedSelectedPicture_geometric_wagon_cut_incidence
    {n : ℕ} (K : (Out).BigCycle n)
    (owner : Fin n → I ⊕ CoreEdge)
    (hAllowed : ∀ k : Fin n, GeomAllowed (K.label k) (owner k))
    (k : Fin n)
    (W : Quotient ((generatedActualASupportTrain
      A hA C.toRelStructure S R f T U hShared).wagonSetoid μ))
    (hW : K.connector k = Sum.inr W)
    (hCut : owner k ≠ owner (cyclicSucc k)) :
    (∃ (i j : I), i ≠ j ∧
      owner k = Sum.inl i ∧ owner (cyclicSucc k) = Sum.inl j ∧
      ∃ (oldA oldB : OldEdge)
        (c : Quotient (U.wagonSetoid μ)) (s t : SharedEdge),
        T.rel μ (sharedOldACarrierInclusion A C.toRelStructure S s) oldA ∧
        T.rel μ (sharedOldACarrierInclusion A C.toRelStructure S t) oldB ∧
        Quotient.mk (U.wagonSetoid μ) (Emb i s) = c ∧
        Quotient.mk (U.wagonSetoid μ) (Emb j t) = c ∧
        (Emb i s).1 ⊆ Set.range (f i) ∧
        (Emb j t).1 ⊆ Set.range (f j)) ∨
    (∃ (i : I) (b : CoreEdge),
      owner k = Sum.inl i ∧ owner (cyclicSucc k) = Sum.inr b ∧
      ∃ (old : OldEdge) (s : SharedEdge),
        T.rel μ (sharedOldACarrierInclusion A C.toRelStructure S s) old ∧
        U.rel μ (Emb i s) b ∧
        (Emb i s).1 ⊆ Set.range (f i)) ∨
    (∃ (b : CoreEdge) (i : I),
      owner k = Sum.inr b ∧ owner (cyclicSucc k) = Sum.inl i ∧
      ∃ (old : OldEdge) (s : SharedEdge),
        T.rel μ (sharedOldACarrierInclusion A C.toRelStructure S s) old ∧
        U.rel μ (Emb i s) b ∧
        (Emb i s).1 ⊆ Set.range (f i)) ∨
    (∃ (b c : CoreEdge), b ≠ c ∧
      owner k = Sum.inr b ∧ owner (cyclicSucc k) = Sum.inr c ∧
      U.rel μ b c) := by
  rcases cyclicOwnerCut_four_cases owner k hCut with
    ⟨i, j, hij, hi, hj⟩ | ⟨i, b, hi, hb⟩ |
    ⟨b, i, hb, hi⟩ | ⟨b, c, hbc, hb, hc⟩
  · exact Or.inl ⟨i, j, hij, hi, hj,
      attachedSelectedPicture_geometric_wagon_two_standards
        A hA B D C family selected e R f T U hShared hRel μ
        K owner hAllowed k W i j hij hW hi hj⟩
  · exact Or.inr (Or.inl ⟨i, b, hi, hb,
      attachedSelectedPicture_geometric_wagon_standard_core
        A hA B D C family selected e R f T U hShared hRel μ
        K owner hAllowed k W i b hW hi hb⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨b, i, hb, hi,
      attachedSelectedPicture_geometric_wagon_core_standard
        A hA B D C family selected e R f T U hShared hRel μ
        K owner hAllowed k W i b hW hb hi⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨b, c, hbc, hb, hc,
      attachedSelectedPicture_geometric_wagon_core_core
        A hA B D C family selected e R f T U hShared hRel μ
        K owner hAllowed k W b c hW hb hc⟩))

end GeometricCutIncidence
end StructuralRamsey.Girth
