import Girth.ForestToSupremeOwned
import Girth.ForestUsedOwnerLocalForest

/-!
# A bottom cycle carried by a forest has a supreme copy

This is the circulation forest-cycle lemma with literal global simultaneous
supremeness.  The supporting family consists of the distinct labels which
actually occur; nonadjacent repeated occurrences are retained.  The proof
uses no assumed local pieces, global replacement plan, or order bound.
-/

namespace StructuralRamsey.Girth.OrderOneData

universe v
variable {V E I P : Type v} (D : OrderOneData V E I P)

/-- The forest condition on distinct members actually occurring on a cycle. -/
def BigCycle.BottomForest {n : ℕ} (C : D.BigCycle n)
    (H : D.BottomForestGeometry) : Prop :=
  ForestOfCopies (fun a : Set.range C.label => D.bottomForestPiece H a.1)

/-- The manuscript's forest-cycle lemma, including length two, cyclic wrap,
actual edge labels, and repeated designated occurrences. -/
theorem BigCycle.hasSimultaneousSupreme_of_bottomForest
    {n : ℕ} (C : D.BigCycle n)
    (H : D.BottomForestGeometry) (hAccept : C.Acceptable)
    (hForest : C.BottomForest D H) : C.HasSimultaneousSupreme := by
  classical
  by_cases hn : n = 2
  · subst n
    apply C.hasSimultaneousSupreme_of_two_bottom_forest D H
    let a : Set.range C.label := ⟨C.label 0, ⟨0, rfl⟩⟩
    let b : Set.range C.label := ⟨C.label 1, ⟨1, rfl⟩⟩
    have hab : a ≠ b := by
      intro h
      have hVal := congrArg Subtype.val h
      exact C.adjacent_ne 0 (by simpa [a, b, cyclicSucc] using hVal)
    exact hForest.pairwiseAllowed hab
  · have hn3 : 3 ≤ n := by have := C.length_ge_two; omega
    letI : Fintype (Set.range C.label) := Fintype.ofFinite _
    let j0 : Fin n := ⟨0, by omega⟩
    letI : Nonempty (Set.range C.label) := ⟨⟨C.label j0, ⟨j0, rfl⟩⟩⟩
    obtain ⟨J⟩ := hForest.joinTree_of_nonempty
    let O : D.BottomForestOwnership C (fun a : Set.range C.label => a.1) := {
      owner := fun j => ⟨C.label j, ⟨j, rfl⟩⟩
      carrier_subset := fun _ => Set.Subset.rfl
      edges_subset := fun _ => Set.Subset.rfl
      designated_eq := fun _ _ => rfl
      member_occurs := by
        intro a
        obtain ⟨j, hj⟩ := a.2
        exact ⟨j, Subtype.ext hj, hj⟩ }
    exact C.hasSimultaneousSupreme_of_owned_bottom_joinTree
      H hAccept hn3 (fun a : Set.range C.label => a.1) J hForest.pairwiseAllowed O

/-- The local witness's finite-family forest hypothesis applies to the
distinct labels of a cycle within the same occurrence budget. -/
theorem BigCycle.bottomForest_of_localForest
    {n : ℕ} (C : D.BigCycle n)
    (H : D.BottomForestGeometry) (q : ℕ)
    (hLocal : LocalForestThrough (D.bottomForestPiece H) q)
    (hLength : n ≤ q) : C.BottomForest D H := by
  classical
  letI : Fintype (Set.range C.label) := Fintype.ofFinite _
  let idx : Set.range C.label ↪ I ⊕ E := ⟨Subtype.val, Subtype.val_injective⟩
  have hCard : Fintype.card (Set.range C.label) ≤ n := by
    let onto : Fin n → Set.range C.label := fun j => ⟨C.label j, ⟨j, rfl⟩⟩
    have hSurj : Function.Surjective onto := by
      intro a
      obtain ⟨j, hj⟩ := a.2
      exact ⟨j, Subtype.ext hj⟩
    simpa using Fintype.card_le_of_surjective onto hSurj
  exact hLocal (Set.range C.label) idx (hCard.trans hLength)

/-- The precise conversion used after segmentation has reduced the cycle to
at most `q` occurrences.  The full order-to-length reduction belongs to the
picture-step argument and is not assumed to follow from order alone. -/
theorem BigCycle.hasSimultaneousSupreme_of_bottomLocalForest
    {n : ℕ} (C : D.BigCycle n)
    (H : D.BottomForestGeometry) (hAccept : C.Acceptable) (q : ℕ)
    (hLocal : LocalForestThrough (D.bottomForestPiece H) q)
    (hLength : n ≤ q) : C.HasSimultaneousSupreme :=
  C.hasSimultaneousSupreme_of_bottomForest D H hAccept
    (C.bottomForest_of_localForest D H q hLocal hLength)

end StructuralRamsey.Girth.OrderOneData
