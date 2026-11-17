import Girth.TrainFillingColouredOrderedEdgePresentation

/-!
# Track 1: recover the old vertex colour from its genuine unary relations

The functional EHN witness may have unused vertices carrying arbitrary
unary predicates; there is no global predicate-partition assumption
in the free-amalgamation class. Nevertheless, on the image of every
genuine selected coloured B-copy, reflection of ALL unary relations
forces exactly one colour.

Choose a default colour away from the selected family. On every
selected full B image, the induced old colour is independent of this
choice and agrees with the source colour. This supplies the
hPredicate assumption of the owner-splitting assembly without
postulating an extra unary colouring function.

STAGED DRAFT, not exact-head kernel compiled.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v
variable {I : Type u} {VB V : Type v}

/-- Read a colour from the actual old unary relations, with an arbitrary
default on vertices outside the union of genuinely coloured images. -/
noncomputable def oldColourOfRel
    {k : ℕ}
    (D : RelStructure (colouredOrderedEdgeLanguage I k) V)
    (default : I) (x : V) : I := by
  classical
  exact if h : ∃ i : I, D.rel (.inl (.inr i)) (fun _ : Fin 1 => x) then
    Classical.choose h
  else
    default

/-- Every full induced old selected B embedding preserves the
oldColourOfRel colour obtained by reading its unary predicates.
This does NOT require the ambient EHN witness to partition all vertices
by unary predicates: selected ranges have that property automatically. -/
theorem oldColourOfRel_on_selected
    (k : ℕ) (E : Set (Set VB))
    (sourceColour : VB → I)
    [LinearOrder VB]
    (D : RelStructure (colouredOrderedEdgeLanguage I k) V)
    (default : I)
    (b : Embedding (colouredOrderedEdgeTarget k E sourceColour) D)
    (w : VB) :
    oldColourOfRel D default (b w) = sourceColour w := by
  classical
  unfold oldColourOfRel
  split_ifs with h
  · have hChosen :
        D.rel (.inl (.inr (Classical.choose h)))
          (fun _ : Fin 1 => b w) :=
      Classical.choose_spec h
    have hPull := (b.map_rel_iff
        (.inl (.inr (Classical.choose h)))
        (fun _ : Fin 1 => w)).mp hChosen
    change sourceColour w = Classical.choose h at hPull
    exact hPull.symm
  · have hOld :
        (colouredOrderedEdgeTarget k E sourceColour).rel
          (.inl (.inr (sourceColour w)))
          (fun _ : Fin 1 => w) := by
      change sourceColour w = sourceColour w
      rfl
    have hTarget := (b.map_rel_iff
        (.inl (.inr (sourceColour w)))
        (fun _ : Fin 1 => w)).mpr hOld
    exact (h ⟨sourceColour w, hTarget⟩).elim

#print axioms StructuralRamsey.Girth.oldColourOfRel_on_selected

end StructuralRamsey.Girth
