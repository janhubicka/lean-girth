import Girth.ForestCarrierCorner

/-! # Fresh carrier for a minimal bad forest extension

This packages the finite carrier case split used by the successor-tree forest
proof.  We work under the two support hypotheses available in the uniform
hypergraph application:

* support edges of the moving piece are non-subsingleton;
* support edges form an antichain under inclusion.

If a new piece cannot be attached to an old forest, then two old boundary
intersections are incomparable.  If some old boundary is already a whole edge,
the whole moving piece is the fresh carrier.  Otherwise all old boundaries are
subsingletons, and any support edge covering the chosen incomparable pair is
fresh from every old member.
-/

namespace StructuralRamsey.Girth

universe v
variable {W ι : Type v}

/-- Support edges of one uniform piece form an inclusion antichain. -/
def EdgeAntichain (F : HypergraphPiece W) : Prop :=
  ∀ ⦃e f : Set W⦄, e ∈ F.edges → f ∈ F.edges → e ⊆ f → e = f

/-- Carrier alternatives for two incomparable boundary intersections. -/
def FreshCarrierAlternative
    (Y : ι → HypergraphPiece W)
    (F : HypergraphPiece W)
    (i j : ι) : Prop :=
  (∃ e : Set W,
      e ∈ F.edges ∧
      (F.carrier ∩ (Y i).carrier) ∪
          (F.carrier ∩ (Y j).carrier) ⊆ e ∧
      ∀ k : ι, ¬ e ⊆ (Y k).carrier) ∨
  ((∀ ⦃e : Set W⦄, e ∈ F.edges →
      ¬((F.carrier ∩ (Y i).carrier) ∪
          (F.carrier ∩ (Y j).carrier) ⊆ e)) ∧
    ∀ k : ι, ¬ F.carrier ⊆ (Y k).carrier)

/-- Fresh-carrier wrapper used by the successor-profile proof.

The assumption hFreshWhole is automatic for distinct copies of one fixed
finite target B: one copy cannot properly contain another copy of the same
finite carrier. -/
theorem exists_incomparable_fresh_carrier
    [Fintype ι] [Nonempty ι] [Finite W]
    {Y : ι → HypergraphPiece W}
    (hY : ForestOfCopies Y)
    (F : HypergraphPiece W)
    (hCrossAllowed :
      ∀ i : ι, AllowedIntersection F (Y i))
    (hBad :
      ¬ ForestOfCopies (sumPieces Y (fun _ : PUnit.{v+1} => F)))
    (hEdgeBig :
      ∀ ⦃e : Set W⦄, e ∈ F.edges → ¬ e.Subsingleton)
    (hAnti : EdgeAntichain F)
    (hFreshWhole :
      ∀ i : ι, ¬ F.carrier ⊆ (Y i).carrier) :
    ∃ i j : ι,
      ¬(F.carrier ∩ (Y i).carrier ⊆
        F.carrier ∩ (Y j).carrier) ∧
      ¬(F.carrier ∩ (Y j).carrier ⊆
        F.carrier ∩ (Y i).carrier) ∧
      FreshCarrierAlternative Y F i j := by
  classical
  have hCrossAllowed' :
      ∀ i : ι, AllowedIntersection (Y i) F := by
    intro i
    exact AllowedIntersection.symm (hCrossAllowed i)
  by_cases hAllSmall :
      ∀ k : ι, (F.carrier ∩ (Y k).carrier).Subsingleton
  · obtain ⟨i, j, hij, hji⟩ :=
      exists_incomparable_intersections_of_not_forest
        hY F hCrossAllowed' hBad
    refine ⟨i, j, hij, hji, ?_⟩
    by_cases hCover :
        ∃ e : Set W,
          e ∈ F.edges ∧
          (F.carrier ∩ (Y i).carrier) ∪
              (F.carrier ∩ (Y j).carrier) ⊆ e
    · rcases hCover with ⟨e, heF, hCover⟩
      refine Or.inl ⟨e, heF, hCover, ?_⟩
      intro k hekY
      have hSmall := hAllSmall k
      have heSub :
          e ⊆ F.carrier ∩ (Y k).carrier := by
        intro x hx
        exact ⟨F.edge_subset heF hx, hekY hx⟩
      have heSmall : e.Subsingleton := by
        intro x hx y hy
        exact hSmall (heSub hx) (heSub hy)
      exact hEdgeBig heF heSmall
    · refine Or.inr ⟨?_, hFreshWhole⟩
      intro e heF hSub
      exact hCover ⟨e, heF, hSub⟩
  · push_neg at hAllSmall
    obtain ⟨k, hkBig⟩ := hAllSmall
    rcases hCrossAllowed k with hkSmall | ⟨d, hdF, _hdY, hkEq⟩
    · exact (hkBig (by simpa [Set.inter_comm] using hkSmall)).elim
    · have hSk :
          F.carrier ∩ (Y k).carrier = d := by
        simpa [Set.inter_comm] using hkEq
      obtain ⟨j, hjNotSub⟩ :=
        no_dominating_member_of_not_forest
          hY F hCrossAllowed' hBad k
      have hkNotSub :
          ¬(F.carrier ∩ (Y k).carrier ⊆
            F.carrier ∩ (Y j).carrier) := by
        intro hSub
        rcases hCrossAllowed j with hjSmall | ⟨e, heF, _heY, hjEq⟩
        · have hdSub :
              d ⊆ F.carrier ∩ (Y j).carrier := by
            intro x hx
            apply hSub
            rw [hSk]
            exact hx
          have hdSmall : d.Subsingleton := by
            intro x hx y hy
            exact hjSmall
              (by
                simpa [Set.inter_comm] using hdSub hx)
              (by
                simpa [Set.inter_comm] using hdSub hy)
          exact hEdgeBig hdF hdSmall
        · have hSj :
              F.carrier ∩ (Y j).carrier = e := by
            simpa [Set.inter_comm] using hjEq
          have hde : d ⊆ e := by
            intro x hx
            have hxSk :
                x ∈ F.carrier ∩ (Y k).carrier := by
              rw [hSk]
              exact hx
            have hxSj := hSub hxSk
            rw [hSj] at hxSj
            exact hxSj
          have hEqDE : d = e := hAnti hdF heF hde
          apply hjNotSub
          intro x hx
          rw [hSj] at hx
          rw [hSk, hEqDE]
          exact hx
      refine ⟨k, j, hkNotSub, hjNotSub, Or.inr ⟨?_, hFreshWhole⟩⟩
      intro e heF hCover
      have hdSub : d ⊆ e := by
        intro x hx
        apply hCover
        exact Or.inl (by
          rw [hSk]
          exact hx)
      have hde : d = e := hAnti hdF heF hdSub
      apply hjNotSub
      intro x hx
      have hxE : x ∈ e :=
        hCover (Or.inr hx)
      rw [← hde, ← hSk] at hxE
      exact hxE

end StructuralRamsey.Girth
