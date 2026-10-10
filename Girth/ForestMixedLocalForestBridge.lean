import Girth.ForestMixedSetBound
import Girth.ForestReindex
import Girth.ForestUsedOwnerLocalForest
import Girth.ForestMixedOneEdgeOwners

/-!
# Transport the genuine set-valued mixed forest property to a mixed owner family

The manuscript's local forest invariant quantifies over SUBFAMILIES of
actual designated copies and ambient one-edge members, not a list in
which one physical multi-edge copy can be repeated under two names.

For an injective labelled family of permitted pieces, the honest
finite-set statement implies LocalForestThrough on its labels.
This is the precise missing passage in the one-edge-owner repair:
regular gluing owners and exceptional core-edge owners are indexed
by a disjoint sum, with distinct physical support pieces.

The injectivity premise must be checked for the actual selected owner
family. In particular this theorem never assumes that an arbitrary
multiset of duplicate multi-edge copies is a forest.
-/

namespace StructuralRamsey.Girth

universe v
variable {W I Q E : Type v}

/-- From the genuine finite-SET mixed forest bound to the indexed
finite SUBFAMILY bound, provided the index-to-piece map is injective. -/
theorem FiniteMixedForestThrough.toLocalForestThrough
    (F : I → HypergraphPiece W)
    (hInj : Function.Injective F)
    (tested : HypergraphPiece W → Prop)
    (m : ℕ) (hTest : ∀ i, tested (F i))
    (hFinite : FiniteMixedForestThrough tested m) :
    LocalForestThrough F m := by
  classical
  intro J _ idx hCard
  let G : J → HypergraphPiece W := fun j => F (idx j)
  have hGInj : Function.Injective G := hInj.comp idx.injective
  have hImageForest :
      ForestOfCopies
        (fun z : {P : HypergraphPiece W //
            P ∈ finitePieceImage G} => z.1) :=
    hFinite.image tested m G (fun j => hTest (idx j)) hCard
  let label : J → {P : HypergraphPiece W //
      P ∈ finitePieceImage G} := fun j =>
    ⟨G j, by
      change G j ∈ Finset.univ.image G
      exact Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩⟩
  have hLabelInj : Function.Injective label := by
    intro j k heq
    apply hGInj
    exact congrArg Subtype.val heq
  have hLabelSurj : Function.Surjective label := by
    intro z
    have hz : z.1 ∈ Finset.univ.image G := by
      simpa [finitePieceImage] using z.2
    obtain ⟨j, _hj, hjEq⟩ := Finset.mem_image.mp hz
    refine ⟨j, ?_⟩
    exact Subtype.ext hjEq
  let equiv : J ≃ {P : HypergraphPiece W //
      P ∈ finitePieceImage G} :=
    Equiv.ofBijective label ⟨hLabelInj, hLabelSurj⟩
  have hRest := hImageForest.reindex equiv
  change ForestOfCopies (fun j : J => G j) at hRest
  exact hRest

/-- Mixed owner supports are injectively labelled if the designated
gluing copies are distinct, the exceptional physical edges are
distinct, and no designated support piece consists of only one edge.

The last assumption is automatic when the source target has at least
two edges (the one-edge target is handled separately by the induction). -/
theorem mixedOwnerSmall_injective
    (small : Q → HypergraphPiece W)
    (coreEdge : E → Set W)
    (hRegularInj : Function.Injective small)
    (hEdgeInj : Function.Injective coreEdge)
    (hRegularNotOneEdge : ∀ q, ¬(small q).IsOneEdge) :
    Function.Injective (mixedOwnerSmall small coreEdge) := by
  intro a b hab
  cases a with
  | inl i =>
      cases b with
      | inl j =>
          apply congrArg Sum.inl
          apply hRegularInj
          exact hab
      | inr j =>
          exfalso
          apply hRegularNotOneEdge i
          rw [show small i = HypergraphPiece.oneEdge (coreEdge j) from hab]
          exact HypergraphPiece.oneEdge_isOneEdge (coreEdge j)
  | inr i =>
      cases b with
      | inl j =>
          exfalso
          apply hRegularNotOneEdge j
          rw [show small j = HypergraphPiece.oneEdge (coreEdge i) from hab.symm]
          exact HypergraphPiece.oneEdge_isOneEdge (coreEdge i)
      | inr j =>
          apply congrArg Sum.inr
          apply hEdgeInj
          exact congrArg HypergraphPiece.carrier hab

/-- The honest local mixed finite-set forest bound implies the
previous-cutoff hypothesis of the direct mixed-owner increment. -/
theorem localForestThrough_mixedOwners_of_finiteMixed
    (small : Q → HypergraphPiece W)
    (coreEdge : E → Set W)
    (hRegularInj : Function.Injective small)
    (hEdgeInj : Function.Injective coreEdge)
    (hRegularNotOneEdge : ∀ q, ¬(small q).IsOneEdge)
    (tested : HypergraphPiece W → Prop)
    (m : ℕ)
    (hRegularTest : ∀ q, tested (small q))
    (hCoreTest : ∀ e, tested (HypergraphPiece.oneEdge (coreEdge e)))
    (hFinite : FiniteMixedForestThrough tested m) :
    LocalForestThrough (mixedOwnerSmall small coreEdge) m := by
  apply hFinite.toLocalForestThrough
    (mixedOwnerSmall small coreEdge)
    (mixedOwnerSmall_injective small coreEdge
      hRegularInj hEdgeInj hRegularNotOneEdge)
    tested m
  · intro i
    cases i with
    | inl q => exact hRegularTest q
    | inr e => exact hCoreTest e

end StructuralRamsey.Girth
