import Girth.TrainFillingIndexedChoiceCore
import Girth.TrainFillingFaithfulWagonMap

set_option Elab.async false

/-!
# Reconstruct proper-cut wagon maps for the entire indexed choice union

The abstract heterogeneous scattering theorem expects an injective map on
the RAW proper-wagon names C × Q. A faithful physical-edge embedding only
supplies a map on wagons ACTUALLY represented by edges.

For the intended cutoff-two application Q is a genuine quotient of the old
first-wagon edge labels P, so parent : P → Q is surjective. Each selected
choice uses a nonempty uniform X-edge family. Under precisely these
hypotheses EVERY tagged proper-wagon name has a physical edge representative.

The checked faithful-wagon-map theorem now constructs the required injective
ambient wagon map and its literal parent-commutation equation. We do not
assume an output wagon embedding, prune ambient edges, or require the ambient
wagon-parent map to be surjective. Proving that the chosen shorter-train
M-copy reflects the physical proper-cut parent relation remains separate.
-/

namespace StructuralRamsey.Girth.IndexedPrivateChoice

universe v
variable {C V P X Q : Type v}
variable (U : C → PrivateWagonInput V P X) (parent : P → Q)

/-- Every tagged proper wagon has a physical-edge representative when
the old wagon quotient is covered by P and each choice has a local edge. -/
theorem properParentOf_surjective
    (hParent : Function.Surjective parent)
    (hLocal : ∀ c : C, Nonempty (U c).LocalEdge) :
    Function.Surjective (properParentOf U parent) := by
  rintro ⟨c, q⟩
  obtain ⟨p, hp⟩ := hParent q
  obtain ⟨a⟩ := hLocal c
  refine ⟨⟨c, (p, a)⟩, ?_⟩
  exact congrArg (Prod.mk c) hp

/-- A faithful physical edge embedding determines the COMPLETE map of
genuine tagged proper-wagon labels, without taking that map as an input. -/
def faithfulProperWagonMap
    {GE GQ : Type v}
    (edge : Edge U ↪ GE)
    (ambientParent : GE → GQ)
    (hParent : Function.Surjective parent)
    (hLocal : ∀ c : C, Nonempty (U c).LocalEdge)
    (hFaithful : ∀ a b : Edge U,
      properParentOf U parent a = properParentOf U parent b ↔
        ambientParent (edge a) = ambientParent (edge b)) :
    FaithfulPhysicalWagonMap (Edge U) GE (ProperWagon (Q := Q) U) GQ where
  localParent := properParentOf U parent
  ambientParent := ambientParent
  edge := edge
  local_surjective := properParentOf_surjective U parent hParent hLocal
  parent_iff := hFaithful

/-- The actual proper-wagon injection is reconstructed from faithful
edge-parent equality and source quotient coverage. -/
noncomputable def reconstructedProperWagonEmbedding
    {GE GQ : Type v}
    (edge : Edge U ↪ GE)
    (ambientParent : GE → GQ)
    (hParent : Function.Surjective parent)
    (hLocal : ∀ c : C, Nonempty (U c).LocalEdge)
    (hFaithful : ∀ a b : Edge U,
      properParentOf U parent a = properParentOf U parent b ↔
        ambientParent (edge a) = ambientParent (edge b)) :
    ProperWagon (Q := Q) U ↪ GQ :=
  (faithfulProperWagonMap U parent edge ambientParent
    hParent hLocal hFaithful).wagonEmbedding

/-- The reconstructed map commutes literally with every actual filled
physical edge parent. No target-wagon surjectivity is required. -/
theorem reconstructedProperWagonEmbedding_parent
    {GE GQ : Type v}
    (edge : Edge U ↪ GE)
    (ambientParent : GE → GQ)
    (hParent : Function.Surjective parent)
    (hLocal : ∀ c : C, Nonempty (U c).LocalEdge)
    (hFaithful : ∀ a b : Edge U,
      properParentOf U parent a = properParentOf U parent b ↔
        ambientParent (edge a) = ambientParent (edge b))
    (a : Edge U) :
    reconstructedProperWagonEmbedding U parent edge ambientParent
      hParent hLocal hFaithful (properParentOf U parent a) =
        ambientParent (edge a) := by
  exact (faithfulProperWagonMap U parent edge ambientParent
    hParent hLocal hFaithful).wagonEmbedding_parent a

end StructuralRamsey.Girth.IndexedPrivateChoice
