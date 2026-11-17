import Girth.TrainFillingPrivateCompletedWSupport

set_option Elab.async false

/-!
# Direct ordered EHN input from the genuine completed W

The completed ordered first-wagon union has a different binary
relational order from the RAW free coproduct. Its small-A edge
support and A-linearity follow from the induced first-wagon
sources, and its global auxiliary order is exactly the
colour-first order used to COMPLETE the binary order.

Every actual small coloured A-copy in W is increasing:
same-colour comparisons follow from the binary relation
itself, while different-colour comparisons follow from the
fixed source colour profile and the global colour-block order.

This supplies hmono of the ordered EHN theorem for COMPLETED W,
without applying the false raw-coproduct shortcut. It is
still only the first ordered EHN input: its output must be
converted to a covered, marked coloured-edge witness, preserving
the genuinely selected increasing embeddings (Track 1).

Source candidates; no new axiom/admission; kernel build pending.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v w
variable {I : Type u} {V P : Type v}
variable [LinearOrder I] [LinearOrder V] [LinearOrder P]

/-- Different unary colour blocks in completed W occur in the
common prescribed colour order, including pairs whose
vertices belong to different first wagons. -/
theorem completedFirstWagon_order_of_colour_lt
    (carrier : P → Set V) (colour : V → I)
    (x y : FirstWagonUnionVertex carrier)
    (h : colour x.2.1 < colour y.2.1) :
    @LT.lt (FirstWagonUnionVertex carrier)
      (firstWagonUnionOrder carrier colour).toLT x y := by
  change firstWagonUnionOrderKey carrier colour x <
    firstWagonUnionOrderKey carrier colour y
  exact Prod.Lex.toLex_lt_toLex.mpr (Or.inl h)

/-- Each induced F_p inclusion into COMPLETED W is strictly
increasing for the chosen global colour-block order, provided
the old V order already lists its predicate colour blocks in
the same order. This extends the actual within-part order,
and no new independent order certificate is assumed. -/
theorem completedFirstWagonSummand_strictMono
    (k : ℕ) (hk : 2 ≤ k)
    (oldEdges : Set (Set V)) (colour : V → I)
    (carrier : P → Set V)
    (hOldBlocks : ∀ x y : V,
      colour x ≠ colour y → x < y → colour x < colour y)
    (p : P) :
    letI : LinearOrder (FirstWagonUnionVertex carrier) :=
      firstWagonUnionOrder carrier colour
    StrictMono (completedFirstWagonSummandEmbedding
      k hk oldEdges colour carrier p) := by
  letI : LinearOrder (FirstWagonUnionVertex carrier) :=
    firstWagonUnionOrder carrier colour
  intro x y hxy
  by_cases hSame : colour x.1 = colour y.1
  · exact (completedFirstWagon_intraColour_order_iff
      carrier colour p x y hSame).mpr hxy
  · exact completedFirstWagon_order_of_colour_lt carrier colour
      (⟨p, x⟩ : FirstWagonUnionVertex carrier)
      (⟨p, y⟩ : FirstWagonUnionVertex carrier)
      (hOldBlocks x.1 y.1 hSame hxy)

/-- Every induced copy of the genuine coloured one-edge source
in COMPLETED W is increasing for the same auxiliary order
which supplies its full relational within-colour comparisons.

No hypothesis is imposed on arbitrary future closed X-copies:
the ordered EHN selected copy carries its own certificate. -/
theorem completedFirstWagon_allACopies_strictMono
    (k : ℕ) (profile : Fin k → I)
    (hProfileBlocks : ∀ i j : Fin k,
      i < j → profile i ≠ profile j → profile i < profile j)
    (oldEdges : Set (Set V)) (colour : V → I)
    (carrier : P → Set V) :
    letI : LinearOrder (FirstWagonUnionVertex carrier) :=
      firstWagonUnionOrder carrier colour
    ∀ a : Embedding (colouredOrderedEdgeSource.{u,v} k profile)
        (completedFirstWagonColouredUnion k oldEdges colour carrier),
      StrictMono a := by
  letI : LinearOrder (FirstWagonUnionVertex carrier) :=
    firstWagonUnionOrder carrier colour
  intro a x y hxy
  have hColour (z : ULift.{v} (Fin k)) :
      colour (a z).2.1 = profile z.down := by
    have hSrc :
        (colouredOrderedEdgeSource.{u,v} k profile).rel
          (.inl (.inr (profile z.down)))
          (fun _ : Fin 1 => z) := by
      change profile z.down = profile z.down
      rfl
    have hTgt := (a.map_rel_iff
      (.inl (.inr (profile z.down))) (fun _ : Fin 1 => z)).mpr hSrc
    change colour (a z).2.1 = profile z.down at hTgt
    exact hTgt
  by_cases hSame : profile x.down = profile y.down
  · have hSrc :
        (colouredOrderedEdgeSource.{u,v} k profile).rel
          (.inr ()) ![x, y] := by
      change profile x.down = profile y.down ∧
        x.down < y.down
      exact ⟨hSame, hxy⟩
    have hTgt := (a.map_rel_iff (.inr ()) ![x, y]).mpr hSrc
    change colour (a x).2.1 = colour (a y).2.1 ∧
      a x < a y at hTgt
    exact hTgt.2
  · have hLt : colour (a x).2.1 < colour (a y).2.1 := by
      rw [hColour x, hColour y]
      exact hProfileBlocks x.down y.down hxy hSame
    exact completedFirstWagon_order_of_colour_lt
      carrier colour (a x) (a y) hLt

end StructuralRamsey.Girth
