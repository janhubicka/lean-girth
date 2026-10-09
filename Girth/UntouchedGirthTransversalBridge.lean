import Girth.UntouchedGirthAllParts
import Girth.LocalForestPieces

/-!
# From transversal local support to untouched-fibre girth

The conditional untouched-fibre theorem uses a fine-part
EdgesMeetPartAtMostOne condition for its designated gluing pieces.
A structural local partite witness gives that condition automatically:
each of its support edges is transversal with respect to the small
A-parts, and the actual base fine-part map is the injective image of
that small part map under the processed base copy.

This eliminates a separately postulated fine-part hypothesis in the
untouched-subsystem girth application. The result is still conditional
on the bounded local forest, old beta-fibre girth, and the actual
carrier correspondence with the designated local embeddings. It is
not the full circulation preservation proposition.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {UA P X Y I Z : Type v}

/-- Transversality of support edges over the small A-parts implies the
at-most-one-vertex condition in every actual base fine part, when
the latter is the image of the former under an injective base map. -/
theorem strongSupportPieces_meet_baseFinePartAtMostOne
    {H : Set (Set Z)} {K : Set (Set Y)}
    (α : UA ↪ P)
    (part : Y → UA)
    (fine : Y → P)
    (hFine : ∀ y, fine y = α (part y))
    (family : I → StrongSupportEmbedding H K)
    (hTransK : EdgeTransversal K part)
    (p : P) :
    EdgesMeetPartAtMostOne
      (fun i : I => (family i).supportPiece)
      {y : Y | fine y = p} := by
  intro i e he x hx y hy
  have heK : e ∈ K :=
    (family i).supportPiece_edges_in_target he
  have hPartEq : part x = part y := by
    apply α.injective
    calc
      α (part x) = fine x := (hFine x).symm
      _ = p := hx.2
      _ = fine y := hy.2.symm
      _ = α (part y) := hFine y
  obtain ⟨z, _hz, hUnique⟩ := hTransK e heK (part x)
  exact (hUnique x ⟨hx.1, rfl⟩).trans
    (hUnique y ⟨hy.1, hPartEq.symm⟩).symm

/-- The bounded-forest untouched-fibre girth contradiction can be
instantiated for genuine transversal support pieces without a separate
core-fine-part or part-intersection premise. The processed base-copy
map supplies the core projection automatically. -/
theorem no_short_untouched_cycle_of_transversal_local_support
    (A : RelStructure L UA)
    (C : StructuralRamsey.Partite.System L P X)
    (S : Set X)
    (E : StructuralRamsey.Partite.System L P Y)
    (f : I → StructuralRamsey.Partite.Embedding (C.induce S) E)
    (α β : UA ↪ P)
    (hA : A.Irreducible)
    (hInter : (Set.range α ∩ Set.range β).Subsingleton)
    (u v : UA) (huv : u ≠ v)
    [Nonempty I]
    (part : Y → UA)
    (hFine : ∀ y, E.part y = α (part y))
    {H : Set (Set Z)} {K : Set (Set Y)}
    (family : I → StrongSupportEmbedding H K)
    (hTransK : EdgeTransversal K part)
    (g : ℕ)
    (hLocalForest :
      LocalForestThrough (fun i : I => (family i).supportPiece) g)
    (hCarrier :
      ∀ i : I,
        Set.range (family i) = copyCarrier ((f i).toEmbedding))
    (hOldBeta :
      GirthGT
        (supportCopies A
          (C.induce (activeCarrier A C β)).toRelStructure) g)
    (c : BergeCycle (supportCopies A
      (StructuralRamsey.Partite.Attachment.attach C S E f).toRelStructure))
    (hLen : c.length ≤ g)
    (hProjected : ∀ j : Fin c.length,
      ∃ a : StructuralRamsey.Partite.ProjectedEmbedding A
        (StructuralRamsey.Partite.Attachment.attach C S E f) β,
        c.edge j = copyCarrier a.val) :
    False := by
  have hCoreSupport : ∀ y : Y, E.part y ∈ Set.range α := by
    intro y
    exact ⟨part y, (hFine y).symm⟩
  have hCarrierPiece :
      ∀ i : I,
        ((family i).supportPiece).carrier =
          copyCarrier ((f i).toEmbedding) := by
    intro i
    exact hCarrier i
  have hPart :
      ∀ p : P,
        EdgesMeetPartAtMostOne
          (fun i : I => (family i).supportPiece)
          {y : Y | E.part y = p} := by
    intro p
    exact strongSupportPieces_meet_baseFinePartAtMostOne
      α part E.part hFine family hTransK p
  exact no_short_untouched_projected_cycle_all_parts
    A C S E f α β hA hCoreSupport hInter u v huv
    (fun i : I => (family i).supportPiece)
    g hLocalForest hCarrierPiece hPart
    hOldBeta c hLen hProjected

end StructuralRamsey.Girth
