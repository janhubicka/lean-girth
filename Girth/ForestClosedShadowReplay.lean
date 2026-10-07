import Girth.ForestShadowClique
import Girth.ForestOneSeparatorReplay

/-!
# A pair-closed old front admits clean one-separator attachments

The triangle-free pair-shadow lemma classifies the intersection of one
new B-piece with the *whole* old base. Strongness of the old designated
copies then translates this boundary classification into the allowed
empty/vertex/whole-A-edge pairwise intersection property.

No forest, Ramsey or universal extension conclusion is hidden here;
genuinely separate attachments may still be incompatible unless their
supports and old pair-owners are coordinated.
-/

namespace StructuralRamsey.Girth

universe v
variable {W ι : Type v}

/-- A closed old support base with no new nonedge B-pairs forces any new
strong piece to meet the old designated copies pairwise cleanly. -/
theorem pairwiseClean_from_pairClosedShadow
    (Y : ι → HypergraphPiece W)
    (F : HypergraphPiece W)
    (D : Set W)
    (hOld : ∀ i : ι, (Y i).carrier ⊆ D)
    (hGirth : GirthGT F.edges 3)
    (hNoNewOwner :
      ∀ ⦃x y : W⦄,
        x ∈ F.carrier ∩ D → y ∈ F.carrier ∩ D → x ≠ y →
        ∃ e : Set W, e ∈ F.edges ∧ x ∈ e ∧ y ∈ e)
    (hEdgeClosed :
      ∀ ⦃e : Set W⦄, e ∈ F.edges →
        ¬ (e ∩ D).Subsingleton → e ⊆ D)
    (hStrong :
      ∀ (i : ι) (e : Set W), e ∈ F.edges →
        ¬ (e ∩ (Y i).carrier).Subsingleton →
          e ∈ (Y i).edges) :
    ∀ i : ι, AllowedIntersection (Y i) F := by
  have hBoundary :
      (F.carrier ∩ D).Subsingleton ∨
        ∃ e : Set W, e ∈ F.edges ∧ F.carrier ∩ D = e := by
    by_cases hs : (F.carrier ∩ D).Subsingleton
    · exact Or.inl hs
    · have hTwo :
          ∃ x y : W,
            x ∈ F.carrier ∩ D ∧
            y ∈ F.carrier ∩ D ∧ x ≠ y := by
        by_contra hn
        apply hs
        intro x hx y hy
        by_contra hxy
        exact hn ⟨x, y, hx, hy, hxy⟩
      obtain ⟨x, y, hx, hy, hxy⟩ := hTwo
      exact Or.inr
        (piece_boundary_is_whole_edge_of_two
          F D hGirth hNoNewOwner hEdgeClosed hx hy hxy)
  exact allowedIntersection_oldFamily_of_oneSeparator
    Y F D hOld hBoundary hStrong

/-- Hence adding one such piece retains the pairwise-clean condition
on the already designated copies.  This is *not* the forest property
of the extended family. -/
theorem pairwiseAllowed_append_pairClosedShadow
    (Y : ι → HypergraphPiece W)
    (F : HypergraphPiece W)
    (D : Set W)
    (hY : PairwiseAllowed Y)
    (hOld : ∀ i : ι, (Y i).carrier ⊆ D)
    (hGirth : GirthGT F.edges 3)
    (hNoNewOwner :
      ∀ ⦃x y : W⦄,
        x ∈ F.carrier ∩ D → y ∈ F.carrier ∩ D → x ≠ y →
        ∃ e : Set W, e ∈ F.edges ∧ x ∈ e ∧ y ∈ e)
    (hEdgeClosed :
      ∀ ⦃e : Set W⦄, e ∈ F.edges →
        ¬ (e ∩ D).Subsingleton → e ⊆ D)
    (hStrong :
      ∀ (i : ι) (e : Set W), e ∈ F.edges →
        ¬ (e ∩ (Y i).carrier).Subsingleton →
          e ∈ (Y i).edges) :
    PairwiseAllowed (sumPieces Y (fun _ : PUnit => F)) := by
  apply pairwiseAllowed_sumPieces hY
    (pairwiseAllowed_singlePiece F)
  intro i _
  exact pairwiseClean_from_pairClosedShadow
    Y F D hOld hGirth hNoNewOwner hEdgeClosed hStrong i

end StructuralRamsey.Girth
