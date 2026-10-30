import Girth.TrainWagonClassRestriction
import Girth.TrainSimultaneousSupreme
import Girth.TrainActualSharedACarrierSubfamily
import Girth.ActiveBoundary

set_option Elab.async false

/-!
# Train endpoint geometry without cycle hypotheses

The bottom train relation is equality of physical edge labels, and the top
relation is universal.  Consequently physical edge linearity supplies full
pretrain linearity at both endpoint cuts.  Bottom wagons are individual
physical edges; the top wagon is the union of all physical support edges.

For a train on the complete actual A-support, ambient A-linearity therefore
makes every bottom wagon A-strong, while the top wagon is automatically
A-strong.  No vertex-coverage assumption is needed: vertices outside the
support do not belong to any ambient A-copy.  These facts handle the endpoint
cases of all-level picture geometry without imposing a spurious system-girth
bound at the universal top.  Empty supports and height zero are included.
-/

namespace StructuralRamsey.Girth

universe u v

namespace EdgeTrainLevels

variable {E V : Type v} {m : ℕ} (T : EdgeTrainLevels E m)

/-- At the bottom cut quotient labels retain the complete physical edge
identity.  No nonemptiness or edge-cardinality premise is needed. -/
theorem bottom_parent_injective :
    Function.Injective
      (Quotient.mk (T.wagonSetoid ⟨0, Nat.zero_lt_succ m⟩)) := by
  intro a b hab
  exact (T.bottom a b).mp (Quotient.exact hab)

/-- Every physical edge has the same universal-top parent. -/
theorem top_parent_eq (a b : E) :
    Quotient.mk (T.wagonSetoid ⟨m, Nat.lt_succ_self m⟩) a =
      Quotient.mk (T.wagonSetoid ⟨m, Nat.lt_succ_self m⟩) b :=
  Quotient.sound (T.top a b)

/-- The complete bottom wagon represented by an edge has exactly that
edge's vertex carrier. -/
theorem wagonClassCarrier_bottom (edge : E → Set V) (a : E) :
    T.wagonClassCarrier edge ⟨0, Nat.zero_lt_succ m⟩
        (Quotient.mk (T.wagonSetoid ⟨0, Nat.zero_lt_succ m⟩) a) =
      edge a := by
  ext x
  change (∃ b : E, T.rel ⟨0, Nat.zero_lt_succ m⟩ a b ∧ x ∈ edge b) ↔
    x ∈ edge a
  constructor
  · rintro ⟨b, hab, hx⟩
    have hab' : a = b := (T.bottom a b).mp hab
    subst b
    exact hx
  · intro hx
    exact ⟨a, (T.bottom a a).mpr rfl, hx⟩

/-- Every top wagon is the full union of physical edge carriers.  This
does not identify that support with the whole ambient vertex type. -/
theorem wagonClassCarrier_top (edge : E → Set V)
    (p : Quotient (T.wagonSetoid ⟨m, Nat.lt_succ_self m⟩)) :
    T.wagonClassCarrier edge ⟨m, Nat.lt_succ_self m⟩ p =
      {x | ∃ a : E, x ∈ edge a} := by
  induction p using Quotient.inductionOn with
  | h a =>
      ext x
      change (∃ b : E, T.rel ⟨m, Nat.lt_succ_self m⟩ a b ∧ x ∈ edge b) ↔
        ∃ b : E, x ∈ edge b
      constructor
      · rintro ⟨b, _, hx⟩
        exact ⟨b, hx⟩
      · rintro ⟨b, hx⟩
        exact ⟨b, T.top a b, hx⟩

end EdgeTrainLevels

namespace OrderOneData

variable {V E I P : Type v} (D : OrderOneData V E I P)

/-- Physical edge linearity supplies wagon linearity whenever distinct
physical edges have distinct parents, as at the bottom train cut. -/
theorem linearPretrain_of_injective_parent
    (hEdges : ∀ e f : E, e ≠ f →
      (D.edgeCarrier e ∩ D.edgeCarrier f).Subsingleton)
    (hParent : Function.Injective D.parent) : D.LinearPretrain := by
  refine ⟨hEdges, ?_⟩
  intro p q hpq x hx y hy
  obtain ⟨a, hap, hxa⟩ := hx.1
  obtain ⟨b, hbq, hxb⟩ := hx.2
  obtain ⟨c, hcp, hyc⟩ := hy.1
  obtain ⟨d, hdq, hyd⟩ := hy.2
  have hac : a = c := hParent (hap.trans hcp.symm)
  have hbd : b = d := hParent (hbq.trans hdq.symm)
  subst c
  subst d
  have hab : a ≠ b := by
    intro hab
    exact hpq (hap.symm.trans ((congrArg D.parent hab).trans hbq))
  exact hEdges a b hab ⟨hxa, hxb⟩ ⟨hyc, hyd⟩

/-- Physical edge linearity supplies full pretrain linearity when all
edges have the same parent.  Unused parent labels may remain in the type;
their empty wagon carriers cannot cause an intersection. -/
theorem linearPretrain_of_constant_parent
    (hEdges : ∀ e f : E, e ≠ f →
      (D.edgeCarrier e ∩ D.edgeCarrier f).Subsingleton)
    (hParent : ∀ e f : E, D.parent e = D.parent f) :
    D.LinearPretrain := by
  refine ⟨hEdges, ?_⟩
  intro p q hpq x hx y _hy
  obtain ⟨a, hap, _hxa⟩ := hx.1
  obtain ⟨b, hbq, _hxb⟩ := hx.2
  exact (hpq (hap.symm.trans ((hParent a b).trans hbq))).elim

end OrderOneData

open StructuralRamsey.RelStructure

variable {L : RelLanguage.{u}} {UA V : Type v}
variable (A : RelStructure L UA) (R : RelStructure L V)

/-- Relational A-linearity is physical edge linearity on the complete
carrier-labelled A-support.  Multiple embeddings of one image are already
represented by the same physical edge label. -/
theorem oldACarrier_edges_inter_subsingleton_of_aLinear
    (hLinear : ALinear A R) :
    ∀ a b : OldACarrierEdge A R, a ≠ b → (a.1 ∩ b.1).Subsingleton := by
  intro a b hab
  obtain ⟨f, hf⟩ := a.2
  obtain ⟨g, hg⟩ := b.2
  have hCopies : ¬ SameCopy f g := by
    intro hfg
    exact hab (Subtype.ext (hf.trans (hfg.trans hg.symm)))
  rw [hf, hg]
  exact hLinear f g hCopies

/-- Conversely, physical edge linearity on the complete actual support
supplies relational A-linearity.  No embedding labels are identified
unless their whole carriers are equal. -/
theorem aLinear_of_oldACarrier_edges_inter_subsingleton
    (hEdges : ∀ a b : OldACarrierEdge A R,
      a ≠ b → (a.1 ∩ b.1).Subsingleton) : ALinear A R := by
  intro f g hCopies
  apply hEdges ⟨copyCarrier f, ⟨f, rfl⟩⟩ ⟨copyCarrier g, ⟨g, rfl⟩⟩
  intro h
  exact hCopies (congrArg Subtype.val h)

/-- A complete bottom wagon of an actual A-support train is A-strong in
an A-linear ambient structure, with no nontriviality or cycle premise. -/
theorem actualASupport_bottom_wagon_aStrong
    {m : ℕ} (T : EdgeTrainLevels (OldACarrierEdge A R) m)
    (hLinear : ALinear A R)
    (p : Quotient (T.wagonSetoid ⟨0, Nat.zero_lt_succ m⟩)) :
    AStrong A R
      (T.wagonClassCarrier (fun a => a.1) ⟨0, Nat.zero_lt_succ m⟩ p) := by
  induction p using Quotient.inductionOn with
  | h a =>
      rw [T.wagonClassCarrier_bottom]
      obtain ⟨f, hf⟩ := a.2
      rw [hf]
      exact aStrong_copyCarrier_of_aLinear hLinear f

/-- The top support wagon contains every ambient A-copy, even when the
ambient structure has uncovered vertices.  Hence its A-strongness is
automatic and needs neither linearity nor any system-girth bound. -/
theorem actualASupport_top_wagon_aStrong
    {m : ℕ} (T : EdgeTrainLevels (OldACarrierEdge A R) m)
    (p : Quotient (T.wagonSetoid ⟨m, Nat.lt_succ_self m⟩)) :
    AStrong A R
      (T.wagonClassCarrier (fun a => a.1) ⟨m, Nat.lt_succ_self m⟩ p) := by
  rw [T.wagonClassCarrier_top]
  intro f _hMeet x hx
  exact ⟨⟨copyCarrier f, ⟨f, rfl⟩⟩, hx⟩

end StructuralRamsey.Girth
