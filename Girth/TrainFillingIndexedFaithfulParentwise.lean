import Girth.TrainFillingIndexedProperWagonReconstruction
import Girth.TrainFillingIndexedParentwiseRealization

set_option Elab.async false

/-!
# Heterogeneous scattering from faithfully realized physical edges

The existing indexed parentwise scattering theorem asks for three
injections (vertices, physical edges, proper-cut wagons). The wagon
injection is determined by the physical edge injection and reflected
proper-parent equality once every genuine source wagon has an edge.

This interface accepts only actual vertex/edge embeddings, exact
physical carrier/copy identities, the SOURCE quotient's surjectivity
and the selected embedding's faithful wagon-parent relation.
It CONSTRUCTS the wagon embedding and its exact parent equation and
then invokes the already checked global scattering theorem.

The selected shortened-train M-copy, its carrier identifications,
the faithful parent relation, and the final Ramsey arrow are still
application obligations. No full cutoff-two theorem is claimed.
-/

namespace StructuralRamsey.Girth.IndexedPrivateChoice

universe v
variable {C V P X Q GV GE I GQ : Type v}
variable (U : C → PrivateWagonInput V P X) (parent : P → Q)
variable (D : OrderOneData GV GE I GQ)

/-- A full physical selected-copy realization with NO independently
postulated output wagon injection or parent-commutation field. -/
structure FaithfulParentwisePhysicalRealization where
  vertex : I → IndexedPrivateChoice.Vertex U ↪ GV
  edge : I → IndexedPrivateChoice.Edge U ↪ GE
  parent_surjective : Function.Surjective parent
  template_nonempty : ∀ c : C, Nonempty (U c).LocalEdge
  edge_parent_faithful : ∀ i : I, ∀ a b : IndexedPrivateChoice.Edge U,
    IndexedPrivateChoice.properParentOf U parent a =
      IndexedPrivateChoice.properParentOf U parent b ↔
        D.parent (edge i a) = D.parent (edge i b)
  edgeCarrier_eq : ∀ i e,
    D.edgeCarrier (edge i e) =
      vertex i '' IndexedPrivateChoice.edgeCarrier U e
  copyCarrier_eq : ∀ i,
    D.copyCarrier i = Set.range (vertex i)
  copyEdges_eq : ∀ i,
    D.copyEdges i = Set.range (edge i)

namespace FaithfulParentwisePhysicalRealization

variable {U parent D}
variable (R : FaithfulParentwisePhysicalRealization U parent D)

/-- The ambient proper-wagon map and its physical-parent equation
are THEOREMS of the faithful physical embedding data. -/
noncomputable def toParentwiseRealization :
    ParentwiseRealization U parent D where
  vertex := R.vertex
  edge := R.edge
  wagon := fun i =>
    reconstructedProperWagonEmbedding U parent (R.edge i) D.parent
      R.parent_surjective R.template_nonempty (R.edge_parent_faithful i)
  edgeCarrier_eq := R.edgeCarrier_eq
  parent_eq := by
    intro i e
    exact (reconstructedProperWagonEmbedding_parent U parent
      (R.edge i) D.parent R.parent_surjective R.template_nonempty
      (R.edge_parent_faithful i) e).symm
  copyCarrier_eq := R.copyCarrier_eq
  copyEdges_eq := R.copyEdges_eq

/-- The checked global scattering proof applies with no independently
assumed proper-wagon injection, to the FULL unchanged ambient system. -/
theorem target_fullSystemGirthGT {g : ℕ}
    (hGirth : D.FullSystemGirthGT g) :
    (R.toParentwiseRealization.designatedFamily.target).FullSystemGirthGT g := by
  exact R.toParentwiseRealization.target_fullSystemGirthGT hGirth

end FaithfulParentwisePhysicalRealization
end StructuralRamsey.Girth.IndexedPrivateChoice
