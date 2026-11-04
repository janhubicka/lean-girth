import Girth.TrainFillingIndexedChoiceCore
import Girth.TrainFillingIndexedChoiceRelational

set_option Elab.async false

/-!
# Flatten heterogeneous G0 physical edge indices to filling coordinates

The real choice-indexed G0 has physical edges of type
  Sigma c, (P × {a : Set X // a ∈ (U c).templateEdges}).
The uniform filling uses
  (C × P) × {a : Set X // a ∈ E}.
For the selected EHN family, all local ambient template edge sets are the
same E = E(X), though the selected W* subfamilies may vary with c.

We build an ACTUAL equivalence of these two physical edge types. It keeps
the first-wagon/choice index and the literal physical carrier of every
template edge; no different edge occurrence is identified or discarded.
We also transport each selected W* edge family to the one fixed E(X) type.

This is a representation bridge, not the construction of the final global
selected M-copy embedding or the prescribed first Ramsey parameter.
-/

namespace StructuralRamsey.Girth.IndexedPrivateChoice

universe v
variable {C V P X : Type v} (U : C → PrivateWagonInput V P X)
variable (E : Set (Set X))
variable (hTemplate : ∀ c : C, (U c).templateEdges = E)

abbrev CommonTemplateEdge (_U : C → PrivateWagonInput V P X)
    (E : Set (Set X)) := {a : Set X // a ∈ E}
abbrev OldChoiceEdge (_U : C → PrivateWagonInput V P X) := C × P

/-- Every local edge type is literally the same physical template family
after transporting the membership proof; no equality of choice-specific
selected W* families is assumed. -/
noncomputable def choiceTemplateEquiv (c : C) :
    (U c).LocalEdge ≃ CommonTemplateEdge U E where
  toFun a := ⟨a.1, by
    rw [← hTemplate c]
    exact a.2⟩
  invFun a := ⟨a.1, by
    rw [hTemplate c]
    exact a.2⟩
  left_inv := by
    intro a
    apply Subtype.ext
    rfl
  right_inv := by
    intro a
    apply Subtype.ext
    rfl

/-- The complete heterogeneous G0 edge type is in bijection with
(contracted first-wagon edge, fixed local X-edge). -/
noncomputable def edgeIndexEquiv :
    Edge U ≃ (OldChoiceEdge U × CommonTemplateEdge U E) where
  toFun a :=
    ((a.1, a.2.1), choiceTemplateEquiv U E hTemplate a.1 a.2.2)
  invFun a :=
    ⟨a.1.1, (a.1.2,
      (choiceTemplateEquiv U E hTemplate a.1.1).symm a.2)⟩
  left_inv := by
    rintro ⟨c, ⟨p, a⟩⟩
    apply Sigma.ext rfl
    apply Prod.ext rfl
    exact (choiceTemplateEquiv U E hTemplate c).symm_apply_apply a
  right_inv := by
    rintro ⟨⟨c, p⟩, a⟩
    change ((c, p),
      (choiceTemplateEquiv U E hTemplate c)
        ((choiceTemplateEquiv U E hTemplate c).symm a)) = ((c, p), a)
    rw [Equiv.apply_symm_apply]

/-- The quotient-free physical old-edge owner is just the actual
(choice, first wagon) pair. -/
@[simp] theorem edgeIndexEquiv_old (a : Edge U) :
    (edgeIndexEquiv U E hTemplate a).1 = (a.1, a.2.1) := rfl

/-- The local physical edge carrier is NOT modified by edge flattening. -/
@[simp] theorem edgeIndexEquiv_template_carrier (a : Edge U) :
    (edgeIndexEquiv U E hTemplate a).2.1 = a.2.2.1 := rfl

/-- Selected W* edge membership may depend on c and p. We transfer it
to the same common E(X) coordinate used for the final colour-word arrow. -/
def selectedCommonEdges (c : C) (p : P) :
    Set (CommonTemplateEdge U E) :=
  (choiceTemplateEquiv U E hTemplate c) '' (U c).selectedEdges p

theorem selectedCommonEdges_iff (a : Edge U) :
    a.2.2 ∈ (U a.1).selectedEdges a.2.1 ↔
      (edgeIndexEquiv U E hTemplate a).2 ∈
        selectedCommonEdges U E hTemplate a.1 a.2.1 := by
  constructor
  · intro ha
    exact ⟨a.2.2, ha, rfl⟩
  · rintro ⟨b, hb, heq⟩
    have hab : b = a.2.2 :=
      (choiceTemplateEquiv U E hTemplate a.1).injective heq
    rw [← hab]
    exact hb

end StructuralRamsey.Girth.IndexedPrivateChoice
