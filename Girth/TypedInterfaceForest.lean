import Girth.CoherentPortJoinTree

/-!
# Join trees with a parametrized interface policy

The old ForestOfCopies hardcodes two intersection types: singleton or one
whole common support edge. A gluing lemma for coloured configurations made of
several support edges must not silently assert that those intersections are
one support edge.

This file separates:
* running-intersection geometry (JoinTree),
* admissibility of the FULL intersection (an arbitrary compatibility relation),
* the separate combinatorial proof that a replacement actually preserves that
  compatibility relation.

Everything here is a conservative generalization of the checked single-edge
binary glue: with compatibility = AllowedIntersection it recovers
ForestOfCopies for a nonempty family.

No closure reflection, no-new-A-copy theorem, or Ramsey arrow follows from
these definitions alone.
-/

namespace StructuralRamsey.Girth
namespace CoherentPort

universe v
variable {W I J : Type v}

/-- Generalized forest certificate for a nonempty indexed family. There is
one global join tree, and every pair of distinct labelled members has the
chosen admissible overlap relation. -/
structure TypedInterfaceForest
    (compatible : HypergraphPiece W → HypergraphPiece W → Prop)
    (F : I → HypergraphPiece W) where
  pairwise : ∀ ⦃i j : I⦄, i ≠ j → compatible (F i) (F j)
  joinTree : JoinTree F

/-- Binary gluing of forests for ANY symmetric compatibility policy.
The single-node port hypothesis gives the join tree; admissibility of
cross pairs must be supplied separately. -/
theorem TypedInterfaceForest.sumPort
    [Fintype I] [Fintype J]
    {compatible : HypergraphPiece W → HypergraphPiece W → Prop}
    (hSymm : ∀ (A B : HypergraphPiece W),
      compatible A B → compatible B A)
    {F : I → HypergraphPiece W} {G : J → HypergraphPiece W}
    {i₀ : I} {j₀ : J}
    (D : BridgeData F G i₀ j₀)
    (HF : TypedInterfaceForest compatible F)
    (HG : TypedInterfaceForest compatible G)
    (hCross : ∀ i j, compatible (F i) (G j)) :
    TypedInterfaceForest compatible (sumPieces F G) := by
  refine ⟨?_, D.joinTree HF.joinTree HG.joinTree⟩
  intro a b hab
  cases a with
  | inl i =>
      cases b with
      | inl k =>
          apply HF.pairwise
          intro hik
          apply hab
          simpa [hik]
      | inr j =>
          exact hCross i j
  | inr j =>
      cases b with
      | inl i =>
          exact hSymm _ _ (hCross i j)
      | inr k =>
          apply HG.pairwise
          intro hjk
          apply hab
          simpa [hjk]

/-- The original forest lemma is a specialization of the parametrized
interface certificate. -/
theorem TypedInterfaceForest.toForestOfCopies
    {F : I → HypergraphPiece W}
    (H : TypedInterfaceForest AllowedIntersection F) :
    ForestOfCopies F := by
  exact ⟨H.pairwise, Or.inr ⟨H.joinTree⟩⟩

/-- Conversely, every NONEMPTY original forest yields a typed certificate
with the legacy AllowedIntersection policy. -/
theorem TypedInterfaceForest.ofForestOfCopies
    [Nonempty I]
    {F : I → HypergraphPiece W}
    (hF : ForestOfCopies F) :
    Nonempty (TypedInterfaceForest AllowedIntersection F) := by
  obtain ⟨J⟩ := hF.joinTree_of_nonempty
  exact ⟨⟨hF.pairwiseAllowed, J⟩⟩

/-- A policy specified by the set of exact permitted carrier intersections.
For closure applications the permitted sets must later be certified to be
closed induced substructures, with coherent identifications. -/
def PermittedContact
    (interfaces : Set (Set W))
    (A B : HypergraphPiece W) : Prop :=
  A.carrier ∩ B.carrier ∈ interfaces

theorem permittedContact_symm
    (interfaces : Set (Set W))
    (A B : HypergraphPiece W)
    (h : PermittedContact interfaces A B) :
    PermittedContact interfaces B A := by
  simpa only [PermittedContact, Set.inter_comm] using h

/-- Concrete gluing theorem parametrized by the exact interface family.
Unlike ForestOfCopies this allows a contact consisting of several edges,
provided the corresponding connector geometry and contact certificates
really exist. -/
theorem permittedContact_sumPort
    [Fintype I] [Fintype J]
    (interfaces : Set (Set W))
    {F : I → HypergraphPiece W} {G : J → HypergraphPiece W}
    {i₀ : I} {j₀ : J}
    (D : BridgeData F G i₀ j₀)
    (HF : TypedInterfaceForest (PermittedContact interfaces) F)
    (HG : TypedInterfaceForest (PermittedContact interfaces) G)
    (hCross : ∀ i j, PermittedContact interfaces (F i) (G j)) :
    TypedInterfaceForest (PermittedContact interfaces) (sumPieces F G) :=
  TypedInterfaceForest.sumPort
    (permittedContact_symm interfaces) D HF HG hCross

end CoherentPort
end StructuralRamsey.Girth
