import Girth.ForestSuccessorBridge

/-!
# Abstract two-copy elimination of a bad finite successor-tree profile

This lemma packages the Ramsey half of the proposed forest-partite proof.
A *two-copy test* here means a pair of finite shape presentations whose
images under no shape reduction can both have a specified forbidden
profile.  Applying the verified finite-dimensional successor-tree Ramsey
theorem makes the full profile constant; a forbidden homogeneous profile
would contradict its two-copy test.

The missing girth-specific theorem is precisely the geometric construction
of such tests for every minimally bad forest profile.  No such existence
is assumed unconditionally in this file.
-/

namespace StructuralRamsey.Girth

universe u w
variable {Label : Type u} [Fintype Label] [Nonempty Label]

/-- If every forbidden finite profile admits an obstruction by two
presentations *before* the homogeneous shape map is selected, then finite
successor-tree Ramsey eliminates all forbidden profiles. -/
theorem forestProfileElimination_of_twoCopyTests
    (arity n k : Nat)
    {κ : Type w} [Fintype κ]
    (colour :
      SuccessorTree.SMTree.AM
        (forestHistorySMTree (Label := Label) arity) n k → κ)
    (bad : κ → Prop)
    (hTwoCopy :
      ∀ δ : κ, bad δ →
        ∃ a b :
          SuccessorTree.SMTree.AM
            (forestHistorySMTree (Label := Label) arity) n k,
          ∀ W :
            SuccessorTree.SMTree.ShapeSubspace
              (forestHistorySMTree (Label := Label) arity) n,
            ¬
              (colour
                ((forestHistorySMTree (Label := Label) arity).shapeActK
                  n k W a) = δ ∧
               colour
                ((forestHistorySMTree (Label := Label) arity).shapeActK
                  n k W b) = δ)) :
    ∃ W :
        SuccessorTree.SMTree.ShapeSubspace
          (forestHistorySMTree (Label := Label) arity) n,
      ∀ a :
        SuccessorTree.SMTree.AM
          (forestHistorySMTree (Label := Label) arity) n k,
        ¬ bad
          (colour
            ((forestHistorySMTree (Label := Label) arity).shapeActK
              n k W a)) := by
  obtain ⟨W, hMono⟩ :=
    forestHistoryFiniteRamsey (Label := Label)
      arity n k colour
  refine ⟨W, ?_⟩
  intro a hBad
  obtain ⟨x, y, hNoPair⟩ := hTwoCopy _ hBad
  exact hNoPair W ⟨hMono x a, hMono y a⟩

end StructuralRamsey.Girth
