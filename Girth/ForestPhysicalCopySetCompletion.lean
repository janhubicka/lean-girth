import Girth.ForestCopySetCompletion

/-!
# From finite sets of PHYSICAL copies to indexed support completion

The manuscript quantifies over finite sets of physical A- and B-copies,
not over arbitrary finite sets of EMBEDDINGS presenting those copies.

A physical copy may admit several embedding labels; different physical
copies may also have the same support piece. Consequently the correct
intermediate object is the finite IMAGE of physical copies under the
complete support-piece map.

The theorem turns the faithful set-of-physical-copies extension
property into the labelled finite-set completion interface,
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
noncomputable def PhysicalCopySetForestExtension
    (support : Phys → HypergraphPiece W)
    (eligible designated : Phys → Prop)
    (m : ℕ) : Prop := by
  classical
  exact ∀ s : Finset Phys,
    (∀ p : Phys, p ∈ s → eligible p) →
    s.card ≤ m →
      ∃ t : Finset Phys,
        s ⊆ t ∧
        (∀ p : Phys, p ∈ t → p ∈ s ∨ designated p) ∧
        ForestOfCopies
          (fun T : {T : HypergraphPiece W //
            T ∈ t.image support} => T.1)

/-- Physical-copy completion induces the labelled-copy-set
completion interface whenever each embedding label has a physical
copy key and its support piece depends only on that key.

There is NO injectivity requirement on the label-to-physical-copy
map or on the physical-copy-to-support map. A completion is formed
on the finite set of physical copies and then indexed by the finite
set of its DISTINCT support pieces. -/
theorem PhysicalCopySetForestExtension.toLabelFinset
    {Label : Type v}
    {support : Phys → HypergraphPiece W}
    {eligible designated : Phys → Prop}
    {allowed : HypergraphPiece W → Prop}
    {m : ℕ}
    (hPhysical : PhysicalCopySetForestExtension
      support eligible designated m)
    (key : Label → Phys)
    (supportLabel : Label → HypergraphPiece W)
    (eligibleLabel : Label → Prop)
    (hSupport : ∀ a : Label,
      supportLabel a = support (key a))
    (hEligible : ∀ a : Label, eligibleLabel a → eligible (key a))
    (hAllowed : ∀ p : Phys, designated p →
      allowed (support p)) :
    FinsetLabelForestCompletionProperty
      supportLabel eligibleLabel allowed m := by
  classical
  intro labels hLabels hBudget
  let s : Finset Phys := labels.image key
  have hSelEligible :
      ∀ p : Phys, p ∈ s → eligible p := by
    intro p hp
    obtain ⟨a, ha, hKey⟩ := Finset.mem_image.mp hp
    rw [← hKey]
    exact hEligible a (hLabels a ha)
  have hBound : s.card ≤ m := by
    calc
      s.card ≤ labels.card := Finset.card_image_le
      _ ≤ m := hBudget
  obtain ⟨t, hSub, hClass, hForest⟩ :=
    hPhysical s hSelEligible hBound
  let K : Type v :=
    {T : HypergraphPiece W // T ∈ t.image support}
  let finiteK : Fintype K := by infer_instance
  refine ⟨K, finiteK, ?_⟩
  letI : Fintype K := finiteK
  refine ⟨(fun k : K => k.1), hForest, ?_, ?_⟩
  · intro a ha
    have hSelectedPhysical : key a ∈ t := by
      apply hSub
      exact Finset.mem_image.mpr ⟨a, ha, rfl⟩
    have hSelectedSupport : supportLabel a ∈ t.image support := by
      rw [hSupport a]
      exact Finset.mem_image.mpr
        ⟨key a, hSelectedPhysical, rfl⟩
    exact ⟨⟨supportLabel a, hSelectedSupport⟩, rfl⟩
  · intro k
    obtain ⟨p, hp, hpSupport⟩ :=
      Finset.mem_image.mp k.2
    rcases hClass p hp with hSelected | hDesignated
    · obtain ⟨a, ha, hKey⟩ :=
        Finset.mem_image.mp hSelected
      left
      refine ⟨a, ha, ?_⟩
      calc
        k.1 = support p := hpSupport.symm
        _ = support (key a) := congrArg support hKey.symm
        _ = supportLabel a := (hSupport a).symm
    · right
      have hPermitted : allowed (support p) :=
        hAllowed p hDesignated
      rw [hpSupport] at hPermitted
      exact hPermitted

end StructuralRamsey.Girth
