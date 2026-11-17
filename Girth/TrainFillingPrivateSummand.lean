import Girth.TrainFillingPrivateUniform

set_option Elab.async false

/-!
# Private extensions of different first-wagon summands

In the direct cutoff-two construction the first-wagon template is the
DISJOINT UNION W = \coprod_p F_p. A selected W-copy in X restricts to
embeddings F_p -> X, but F_p is not in general isomorphic to W or to
any other F_q.

UniformPrivateTemplate.toPrivateWagonInput asks for an equivalence
from EVERY old wagon carrier to one fixed W. That convenient special
case is therefore insufficient for the actual cutoff-two application.

The adapter here instead takes one local strong template per summand,
all inside the same X and sharing the same complete physical template
edge family. It constructs the precise heterogeneous PrivateWagonInput:
original first-wagon edges, not the whole W support, are the selected
edges for each p.

The remaining application obligation is to construct these local
strong templates from the SAME selected embedding W -> X. No Ramsey
arrow or selected M-copy is assumed or claimed by this module.
-/

namespace StructuralRamsey.Girth

universe v

/-- Strong local templates on the individual first wagons. The local
vertex types may differ, including in cardinality. The physical
template edge family in X is common to every summand. -/
structure SummandPrivateTemplate (V P X : Type v) where
  oldCarrier : P → Set V
  templateEdges : Set (Set X)
  piece : (p : P) →
    UniformPrivateTemplate {x : V // x ∈ oldCarrier p} X
  templateEdges_eq : ∀ p : P, (piece p).templateEdges = templateEdges

namespace SummandPrivateTemplate

variable {V P X : Type v} (T : SummandPrivateTemplate V P X)

/-- The selected X-edges of one first wagon are exactly the images of
that wagon's OWN old support edges, rather than all edges of W. -/
def selectedEdges (p : P) : Set {a : Set X // a ∈ T.templateEdges} :=
  {a | ∃ e : {e : Set {x : V // x ∈ T.oldCarrier p} //
                 e ∈ (T.piece p).localEdges},
       a.1 = (T.piece p).star '' e.1}

/-- A genuine private-extension input for a heterogeneous family.
No identification of the different first-wagon carriers is needed. -/
noncomputable def toPrivateWagonInput : PrivateWagonInput V P X where
  oldCarrier := T.oldCarrier
  coordinate := fun p => (T.piece p).star
  templateEdges := T.templateEdges
  selectedEdges := T.selectedEdges
  selected_inside := by
    intro p a ha
    obtain ⟨e, he⟩ := ha
    rw [he]
    rintro z ⟨x, hx, rfl⟩
    exact ⟨x, rfl⟩
  local_strong := by
    intro p a x y hxy hx hy hxRange hyRange
    have hTemplate : a.1 ∈ (T.piece p).templateEdges := by
      rw [T.templateEdges_eq p]
      exact a.2
    obtain ⟨e, he⟩ :=
      (T.piece p).strong ⟨a.1, hTemplate⟩
        x y hxy hx hy hxRange hyRange
    exact ⟨e, he⟩
  local_cover := by
    intro p x
    obtain ⟨e, hx⟩ := (T.piece p).local_cover x
    have hTemplate :
        (T.piece p).star '' e.1 ∈ T.templateEdges := by
      rw [← T.templateEdges_eq p]
      exact (T.piece p).map_edge e
    let a : {a : Set X // a ∈ T.templateEdges} :=
      ⟨(T.piece p).star '' e.1, hTemplate⟩
    refine ⟨a, ?_, ?_⟩
    · exact ⟨e, rfl⟩
    · exact ⟨x, hx, rfl⟩

/-- In the constructed input, the local target edge sets really are
the image edge sets of the individual summands. -/
theorem selectedEdges_iff (p : P)
    (a : {a : Set X // a ∈ T.templateEdges}) :
    a ∈ T.toPrivateWagonInput.selectedEdges p ↔
      ∃ e : {e : Set {x : V // x ∈ T.oldCarrier p} //
                 e ∈ (T.piece p).localEdges},
        a.1 = (T.piece p).star '' e.1 := Iff.rfl

end SummandPrivateTemplate
end StructuralRamsey.Girth
