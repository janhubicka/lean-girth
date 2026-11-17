import Girth.ForestCompletionProperty
import Girth.ForestMixedSetBound

/-!
# From finite sets of PHYSICAL copies to indexed support completion

The manuscript quantifies over finite sets of physical A- and B-copies,
not over arbitrary finite sets of EMBEDDINGS presenting those copies.

A physical copy may admit several embedding labels; different physical
copies may also have the same support piece. Consequently the correct
intermediate object is the finite IMAGE of physical copies under the
complete support-piece map.

This theorem turns the faithful set-of-physical-copies extension
property directly into the existing indexed ForestCompletionProperty,
with neither injectivity assumption nor deletion of duplicated
multi-edge B-support members.

Source candidate: requires exact-head Lean compilation and axiom audit.
-/

namespace StructuralRamsey.Girth

universe v
variable {W Phys : Type v}

/-- Faithful physical-copy formulation of forest completion.

For each finite SET of eligible physical copies of size at most m,
there is a finite SET of physical copies containing all selected ones,
with only designated extra copies. Foresthood is tested on the
distinct complete support pieces, as in the manuscript's definition,
rather than on arbitrary embedding labels. -/
def PhysicalCopySetForestExtension
    (support : Phys → HypergraphPiece W)
    (eligible designated : Phys → Prop)
    (m : ℕ) : Prop :=
  ∀ s : Finset Phys,
    (∀ p : Phys, p ∈ s → eligible p) →
    s.card ≤ m →
      ∃ t : Finset Phys,
        s ⊆ t ∧
        (∀ p : Phys, p ∈ t → p ∈ s ∨ designated p) ∧
        ForestOfCopies
          (fun T : {T : HypergraphPiece W //
            T ∈ t.image support} => T.1)

/-- Physical-copy forest extension implies the full indexed forest
completion invariant on support pieces.

The selected physical copy set is the image of arbitrarily many
indexed support representatives, so its size cannot exceed the
index budget. A physical completion is converted to its SET of
distinct support pieces. In particular, repeated labels of
multi-edge B-copies never need to be attached or deleted. -/
theorem PhysicalCopySetForestExtension.toSupportIndexed
    {support : Phys → HypergraphPiece W}
    {eligible designated : Phys → Prop}
    {tested allowed : HypergraphPiece W → Prop}
    {m : ℕ}
    (hPhysical : PhysicalCopySetForestExtension
      support eligible designated m)
    (hRepresent : ∀ T : HypergraphPiece W, tested T →
      ∃ p : Phys, eligible p ∧ support p = T)
    (hAllowed : ∀ p : Phys, designated p →
      allowed (support p)) :
    ForestCompletionProperty tested allowed m := by
  classical
  intro N finiteN selected hTest hBudget
  letI : Fintype N := finiteN
  have hEvery (n : N) :
      ∃ p : Phys, eligible p ∧ support p = selected n :=
    hRepresent (selected n) (hTest n)
  choose physical hEligible hSupport using hEvery
  let s : Finset Phys := Finset.univ.image physical
  have hSelEligible :
      ∀ p : Phys, p ∈ s → eligible p := by
    intro p hp
    obtain ⟨n, _, hn⟩ := Finset.mem_image.mp hp
    rw [← hn]
    exact hEligible n
  have hCard : s.card ≤ m := by
    calc
      s.card ≤ (Finset.univ : Finset N).card := by
        exact Finset.card_image_le
      _ = Fintype.card N := Finset.card_univ
      _ ≤ m := hBudget
  obtain ⟨t, hIn, hClass, hForest⟩ :=
    hPhysical s hSelEligible hCard
  let K : Type v :=
    {T : HypergraphPiece W // T ∈ t.image support}
  let finiteK : Fintype K := by infer_instance
  refine ⟨K, finiteK, ?_⟩
  letI : Fintype K := finiteK
  refine ⟨(fun k : K => k.1), ?_⟩
  refine ⟨hForest, ?_, ?_⟩
  · intro n
    have hPhys : physical n ∈ t := by
      apply hIn
      exact Finset.mem_image.mpr
        ⟨n, Finset.mem_univ n, rfl⟩
    have hImage : selected n ∈ t.image support := by
      rw [← hSupport n]
      exact Finset.mem_image.mpr ⟨physical n, hPhys, rfl⟩
    exact ⟨⟨selected n, hImage⟩, rfl⟩
  · intro k
    obtain ⟨p, hp, hEq⟩ := Finset.mem_image.mp k.2
    rcases hClass p hp with hSelected | hDesignated
    · obtain ⟨n, _, hn⟩ := Finset.mem_image.mp hSelected
      left
      refine ⟨n, ?_⟩
      calc
        k.1 = support p := hEq.symm
        _ = support (physical n) := congrArg support hn.symm
        _ = selected n := hSupport n
    · right
      have hAllowedP : allowed (support p) :=
        hAllowed p hDesignated
      rw [hEq] at hAllowedP
      exact hAllowedP

end StructuralRamsey.Girth
