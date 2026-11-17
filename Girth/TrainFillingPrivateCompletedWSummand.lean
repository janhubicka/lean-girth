import Girth.TrainFillingPrivateCompletedWCopyLocality
import Girth.TrainFillingPrivateRealUnionOrder

set_option Elab.async false

/-!
# Genuine induced first-wagon inclusions into the COMPLETED ordered W

The raw relational coproduct omitted comparisons between
same-colour vertices of different summands. The completed W
adds these comparisons while leaving the k-ary edge
relation componentwise.

This module checks ALL relation symbols, not only the
hyperedge support:
  (1) the k-ary full edge relation is componentwise;
  (2) each unary colour is preserved literally;
  (3) inside one summand, the completed binary
      within-colour order is exactly the old order.

The last condition is the real obstacle to simply using
the raw-coproduct inclusion in the ordered EHN theorem.
This supplies the genuine component inclusion required by
the eventual completed-W EHN adapter.

Candidate source until an exact-head Lean kernel build.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v
variable {I : Type u} {V P : Type v}
variable [LinearOrder I] [LinearOrder V] [LinearOrder P]

/-- For equal-colour vertices of ONE first wagon, the chosen
completed W order is exactly their ORIGINAL ambient order.
Different summands are ordered by their p-tags, but that
does not change any local within-colour relation. -/
theorem completedFirstWagon_intraColour_order_iff
    (carrier : P → Set V) (colour : V → I)
    (p : P) (x y : {z : V // z ∈ carrier p})
    (hColour : colour x.1 = colour y.1) :
    @LT.lt (FirstWagonUnionVertex carrier)
      (firstWagonUnionOrder carrier colour).toLT
      (⟨p, x⟩ : FirstWagonUnionVertex carrier)
      (⟨p, y⟩ : FirstWagonUnionVertex carrier) ↔
    x.1 < y.1 := by
  change
    (toLex (colour x.1, toLex (p, x.1)) : I ×ₗ (P ×ₗ V)) <
      toLex (colour y.1, toLex (p, y.1)) ↔ x.1 < y.1
  constructor
  · intro hxy
    rcases Prod.Lex.toLex_lt_toLex.mp hxy with hDifferent |
      ⟨_, hIntra⟩
    · rw [hColour] at hDifferent
      exact False.elim (lt_irrefl _ hDifferent)
    · rcases Prod.Lex.toLex_lt_toLex.mp hIntra with hTag |
        ⟨_, hOld⟩
      · exact False.elim (lt_irrefl _ hTag)
      · exact hOld
  · intro hxy
    apply Prod.Lex.toLex_lt_toLex.mpr
    refine Or.inr ⟨hColour, ?_⟩
    exact Prod.Lex.toLex_lt_toLex.mpr
      (Or.inr ⟨rfl, hxy⟩)

/-- Each actual first wagon F_p is an INDUCED relational
substructure of the COMPLETED ordered W.
The statement reflects ALL three relation symbols:
k-edge, unary colour, and binary within-colour order.

The k-edge hypothesis k>=2 keeps a genuine spanning
edge type. We do not assume or infer an ordered EHN
Ramsey arrow in this elementary inclusion theorem. -/
noncomputable def completedFirstWagonSummandEmbedding
    (k : ℕ) (_hk : 2 ≤ k)
    (oldEdges : Set (Set V)) (colour : V → I)
    (carrier : P → Set V) (p : P) :
    Embedding
      ((colouredOrderedEdgeTarget k oldEdges colour).induce (carrier p))
      (completedFirstWagonColouredUnion k oldEdges colour carrier) where
  toFun x := ⟨p, x⟩
  injective := by
    intro x y h
    apply Subtype.ext
    exact congrArg
      (fun z : FirstWagonUnionVertex carrier => z.2.1) h
  map_rel_iff := by
    intro symbol xs
    cases symbol with
    | inl kind =>
      cases kind with
      | inl _ =>
        change
          (Function.Injective
            (fun i : Fin k =>
              (⟨p, xs i⟩ : FirstWagonUnionVertex carrier)) ∧
            Set.range (fun i : Fin k =>
              (⟨p, xs i⟩ : FirstWagonUnionVertex carrier)) ∈
              taggedFirstWagonEdges carrier oldEdges) ↔
          (Function.Injective xs ∧
            Set.range (fun i : Fin k => (xs i).1) ∈ oldEdges)
        constructor
        · rintro ⟨hInj, hEdge⟩
          have hLocalInj : Function.Injective xs := by
            intro i j h
            exact hInj (congrArg
              (fun z : {z : V // z ∈ carrier p} =>
                (⟨p, z⟩ : FirstWagonUnionVertex carrier)) h)
          obtain ⟨q, e, he, hImage⟩ := hEdge
          have hImageVal := congrArg
            (fun E : Set (FirstWagonUnionVertex carrier) =>
              (fun z : FirstWagonUnionVertex carrier => z.2.1) '' E)
            hImage
          have hOldEdge :
              Set.range (fun i : Fin k => (xs i).1) =
                Subtype.val '' e := by
            simpa only [Set.image_range, Set.image_image,
              Function.comp_def] using hImageVal
          exact ⟨hLocalInj, by rw [hOldEdge]; exact he⟩
        · rintro ⟨hInj, hEdge⟩
          constructor
          · intro i j h
            apply hInj
            apply Subtype.ext
            exact congrArg
              (fun z : FirstWagonUnionVertex carrier => z.2.1) h
          · refine ⟨p, Set.range xs, ?_, ?_⟩
            · simpa only [Set.image_range, Function.comp_def] using hEdge
            · simp only [Set.image_range, Function.comp_def]
      | inr col =>
        change (colour (xs 0).1 = col ↔
          colour (xs 0).1 = col)
        rfl
    | inr _ =>
      change
        (colour (xs 0).1 = colour (xs 1).1 ∧
          @LT.lt (FirstWagonUnionVertex carrier)
            (firstWagonUnionOrder carrier colour).toLT
            (⟨p, xs 0⟩ : FirstWagonUnionVertex carrier)
            (⟨p, xs 1⟩ : FirstWagonUnionVertex carrier)) ↔
        (colour (xs 0).1 = colour (xs 1).1 ∧
          (xs 0).1 < (xs 1).1)
      constructor
      · rintro ⟨hc, hxy⟩
        exact ⟨hc,
          (completedFirstWagon_intraColour_order_iff
            carrier colour p (xs 0) (xs 1) hc).mp hxy⟩
      · rintro ⟨hc, hxy⟩
        exact ⟨hc,
          (completedFirstWagon_intraColour_order_iff
            carrier colour p (xs 0) (xs 1) hc).mpr hxy⟩

end StructuralRamsey.Girth
