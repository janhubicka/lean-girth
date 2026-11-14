import Girth.TrainUniversalTopOrderTwoClassification
import Girth.TrainActiveGluingWitness
import Girth.ForestRecursiveOutputGirth
import Girth.ForestActualRecursiveSupport
import Girth.TrainRecursiveBottomEqualityBridge
import Mathlib.Tactic

set_option autoImplicit false
set_option Elab.async false

/-!
# F_(2) gives a genuine local FULL system-girth witness at the TOP

The genuine mixed finite-set forest property through two does NOT
by itself give bottom FullSystemGirthGT 2: four different strongly
induced two-edge supports can form an acceptable order-two
vertex/wagon alternating cycle even though EVERY pair of pieces
is an allowed forest. Thus one cannot select the bottom cut for
the cutoff-two full-system witness without extra information.

At the universal top, however, all physical A-edges have exactly
one wagon parent. From the same F_(2) mixed-set hypothesis we get
ordinary A-linearity and A-strong selected image copies. The true
active subsystem has complete A-support coverage of every vertex
of each gluing image. The abstract universal-top order-two theorem
then gives genuine FullSystemGirthGT 2 (not merely the old order-one
Bound property).

This is the missing actual cutoff-two witness of
ActiveAttachmentBounds.cutoffTwo: choose the universal top cut.
No new Ramsey principle or lower-rank full witness bound.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {UA P X Y I : Type v}

/-- One genuine same-q=2 finite mixed local forest witness has full
system girth >2 at its universal top cut, with all original
designated local gluing copies and all ambient A-support edges. -/
theorem activeGluingWitness_top_fullSystemGirth_two_of_finiteMixed
    (A : RelStructure L UA)
    (C : StructuralRamsey.Partite.System L P X)
    (α : UA ↪ P) (R : RelStructure L Y)
    (f : I → RelStructure.Embedding
      (C.toRelStructure.induce (activeCarrier A C α)) R)
    {m : ℕ}
    (U : EdgeTrainLevels (OldACarrierEdge A R) m)
    (hMixed : FiniteMixedForestThrough
      (RelationalMixedSupportTest A f) 2) :
    (activeGluingWitnessOrderOneData A C α R f U
      (⟨m, Nat.lt_succ_self m⟩ : Fin (m + 1))).FullSystemGirthGT 2 := by
  let μTop : Fin (m + 1) := ⟨m, Nat.lt_succ_self m⟩
  let D := activeGluingWitnessOrderOneData A C α R f U μTop
  have hCoreGirth : GirthGT (supportCopies A R) 2 := by
    apply girthGT_of_finiteMixedForestThrough
      (supportCopies A R) (RelationalMixedSupportTest A f) 2 hMixed
    rintro edge ⟨e, rfl⟩
    exact Or.inr ⟨e, rfl⟩
  have hCoreLinear : ALinear A R :=
    aLinear_of_girthGT_two A R hCoreGirth
  have hCopyStrong : ∀ i : I,
      AStrong A R (copyCarrier (f i)) := by
    intro i
    exact aStrong_of_finiteMixedForestThrough
      A (f i) (RelationalMixedSupportTest A f) 2
      (by omega) hMixed (Or.inl ⟨i, rfl⟩)
      (fun a => Or.inr ⟨a, rfl⟩)
  have hConst : ∀ e g : OldACarrierEdge A R, D.parent e = D.parent g := by
    intro e g
    change Quotient.mk (U.wagonSetoid μTop) e =
      Quotient.mk (U.wagonSetoid μTop) g
    exact Quotient.sound (U.top e g)
  have hLinear : D.LinearPretrain := by
    constructor
    · intro e g hne
      obtain ⟨a, ha⟩ := e.2
      obtain ⟨b, hb⟩ := g.2
      have hab : ¬ SameCopy a b := by
        intro h
        apply hne
        exact Subtype.ext (ha.trans (h.trans hb.symm))
      change (e.1 ∩ g.1).Subsingleton
      rw [ha, hb]
      exact hCoreLinear a b hab
    · intro p q hpq x hx y hy
      obtain ⟨e, hep, _hxe⟩ := hx.1
      obtain ⟨g, hgq, _hxg⟩ := hx.2
      have hpqEq : p = q := hep.symm.trans ((hConst e g).trans hgq)
      exact (hpq hpqEq).elim
  have hCover :
      ∀ i : I, ∀ x ∈ D.copyCarrier i,
        ∃ e : OldACarrierEdge A R,
          e ∈ D.copyEdges i ∧ x ∈ D.edgeCarrier e := by
    intro i x hx
    change x ∈ copyCarrier (f i) at hx
    obtain ⟨t, ht⟩ := hx
    obtain ⟨edge, he, hVertex⟩ :=
      actualRecursiveActiveSupport_cover A C α t
    obtain ⟨a, ha⟩ := he
    rw [ha] at hVertex
    obtain ⟨u, hu⟩ := hVertex
    let e : OldACarrierEdge A R :=
      ⟨copyCarrier ((f i).comp a), ⟨(f i).comp a, rfl⟩⟩
    refine ⟨e, ?_, ?_⟩
    · change e.1 ⊆ copyCarrier (f i)
      rintro z ⟨v, rfl⟩
      exact ⟨a v, rfl⟩
    · change x ∈ e.1
      refine ⟨u, ?_⟩
      calc
        ((f i).comp a) u = (f i) (a u) := rfl
        _ = (f i) t := congrArg (f i) hu
        _ = x := ht
  have hStrong : ∀ i : I, ∀ e : OldACarrierEdge A R,
      ¬ (D.edgeCarrier e ∩ D.copyCarrier i).Subsingleton →
        e ∈ D.copyEdges i := by
    intro i edge hBig
    obtain ⟨a, ha⟩ := edge.2
    have hMeet :
        ¬ (copyCarrier a ∩ copyCarrier (f i)).Subsingleton := by
      rw [← ha]
      exact hBig
    have hSub : copyCarrier a ⊆ copyCarrier (f i) :=
      (hCopyStrong i) a hMeet
    change edge.1 ⊆ copyCarrier (f i)
    rw [ha]
    exact hSub
  exact OrderOneData.fullSystemGirth_two_of_constant_parent
    D hLinear hConst hCover hStrong

end StructuralRamsey.Girth
