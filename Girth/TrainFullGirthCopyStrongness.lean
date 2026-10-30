import Girth.TrainActiveGluingWitness
import Girth.TrainTwoCopyVertexProbe
import Girth.TrainSimultaneousSupreme

set_option Elab.async false

/-!
# Whole designated-copy strongness from system girth greater than two

The acceptable two-occurrence cycle consisting of a designated copy and
an ambient pair edge has order two.  Its only possible supreme label is
the designated copy.  A long replacement is impossible because the pair
edge is present.  The resulting short replacement is a source edge through
the same distinct vertex pair; physical edge linearity identifies it with
the original ambient edge.

Thus the local order-two consequence of full system girth already forces
pair-edge ownership in each designated copy.  For the literal whole-image
active gluing witness, ownership means complete carrier containment and
therefore supplies A-strongness of every whole gluing image.  It is not
necessary to assume that strongness a second time.  No output geometry,
global cycle transfer, finite support or gluing-image coverage is used.
-/

namespace StructuralRamsey.Girth

universe u v

namespace OrderOneData

variable {V E I P : Type v} (D : OrderOneData V E I P)

/-- A physical edge through two distinct vertices of a designated copy
belongs to that copy, under edge linearity and the necessary local
order-two supreme-piece condition. -/
theorem copy_edge_of_pair_of_local_bound
    (hEdges : ∀ e f : E, e ≠ f →
      (D.edgeCarrier e ∩ D.edgeCarrier f).Subsingleton)
    (hLocal : D.LocalPieceSystemBound 2)
    (i : I) (e : E) (x y : V) (hxy : x ≠ y)
    (hix : x ∈ D.copyCarrier i) (hiy : y ∈ D.copyCarrier i)
    (hex : x ∈ D.edgeCarrier e) (hey : y ∈ D.edgeCarrier e) :
    e ∈ D.copyEdges i := by
  obtain hShort | hLong :=
    D.copy_piece_of_incident_edge hLocal i e x y hxy hix hiy hex hey
  · obtain ⟨f, hf, hfx, hfy⟩ := hShort
    have hfe : f = e := by
      by_contra hne
      exact hxy (hEdges f e hne ⟨hfx, hex⟩ ⟨hfy, hey⟩)
    subst f
    exact hf
  · obtain ⟨x', y', _p, _a, _b, hx', hy', _, _, _, _, _, _, _, hNoPair⟩ := hLong
    have hxx' : x = x' := Sum.inl.inj hx'
    have hyy' : y = y' := Sum.inl.inj hy'
    subst x'
    subst y'
    exact (hNoPair ⟨e, hex, hey⟩).elim

/-- Full system girth at any cutoff at least two supplies the pair-edge
ownership conclusion with no separate linearity or local-piece premise. -/
theorem copy_edge_of_pair_of_fullSystemGirth
    (q : ℕ) (hq : 2 ≤ q) (hFull : D.FullSystemGirthGT q)
    (i : I) (e : E) (x y : V) (hxy : x ≠ y)
    (hix : x ∈ D.copyCarrier i) (hiy : y ∈ D.copyCarrier i)
    (hex : x ∈ D.edgeCarrier e) (hey : y ∈ D.edgeCarrier e) :
    e ∈ D.copyEdges i := by
  have hLocal : D.LocalPieceSystemBound 2 := by
    intro n C hAccept hOrder
    exact D.localPieceSystemBound_of_supremeCycleBound q hFull.2
      n C hAccept (hOrder.trans (Nat.mul_le_mul_left 2 hq))
  exact D.copy_edge_of_pair_of_local_bound hFull.1.1 hLocal
    i e x y hxy hix hiy hex hey

end OrderOneData

open StructuralRamsey.RelStructure

/-- The full intrinsic system-girth bound of the literal active gluing
witness makes every entire prescribed image A-strong in the core.  This
does not assume any geometry of the eventual output attachment. -/
theorem activeGluingWitness_images_aStrong_of_fullSystemGirth
    {L : RelLanguage.{u}} {UA P X Y I : Type v}
    (A : RelStructure L UA) (C : StructuralRamsey.Partite.System L P X)
    (α : UA → P) (R : RelStructure L Y)
    (f : I → RelStructure.Embedding
      (C.toRelStructure.induce (activeCarrier A C α)) R)
    {m : ℕ} (U : EdgeTrainLevels (OldACarrierEdge A R) m)
    (μ : Fin (m + 1)) (q : ℕ) (hq : 2 ≤ q)
    (hFull : (activeGluingWitnessOrderOneData A C α R f U μ).FullSystemGirthGT q) :
    ∀ i : I, AStrong A R (copyCarrier (f i)) := by
  intro i a hMeet
  obtain ⟨x, hx, y, hy, hxy⟩ := Set.not_subsingleton_iff.mp hMeet
  let edge : OldACarrierEdge A R := ⟨copyCarrier a, ⟨a, rfl⟩⟩
  exact (activeGluingWitnessOrderOneData A C α R f U μ).copy_edge_of_pair_of_fullSystemGirth
    q hq hFull i edge x y hxy hx.2 hy.2 hx.1 hy.1

end StructuralRamsey.Girth
