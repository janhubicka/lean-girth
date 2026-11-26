import Mathlib.Tactic

/-! Shared carrier incidence data, independent of cycle words. -/
namespace StructuralRamsey.Girth
universe v

/-- Incidence data needed by the order-one fragment of a pretrain system.
No vertex-carrier injectivity is imposed on either sort of labels. -/
structure OrderOneData (V E I P : Type v) where
  edgeCarrier : E → Set V
  copyCarrier : I → Set V
  copyEdges : I → Set E
  parent : E → P

namespace OrderOneData

variable {V E I P : Type v} (D : OrderOneData V E I P)

def carrier : I ⊕ E → Set V
  | .inl i => D.copyCarrier i
  | .inr e => D.edgeCarrier e

def edges : I ⊕ E → Set E
  | .inl i => D.copyEdges i
  | .inr e => {e}

def designated (_ : OrderOneData V E I P) : I ⊕ E → Prop
  | .inl _ => True
  | .inr _ => False

def Meets (a : I ⊕ E) (p : P) : Prop :=
  ∃ e, e ∈ D.edges a ∧ D.parent e = p

/-- Exactly a short piece with mixed boundary connectors x and p. -/
def Bridge (a : I ⊕ E) (x : V) (p : P) : Prop :=
  ∃ e, e ∈ D.edges a ∧ D.parent e = p ∧ x ∈ D.edgeCarrier e

end OrderOneData
end StructuralRamsey.Girth
