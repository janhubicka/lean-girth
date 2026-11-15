import Girth.TrainRecursiveRefinementForget

set_option autoImplicit false
set_option Elab.async false

/-!
# Track 6: same selected edge maps after forgetting inserted cuts

The ordinary-train coarsening changes only level indices. It does not
change physical edges, their image map, selected-copy indices, or
the original edge-colouring arrow. A map reflecting and preserving
EVERY fine relation consequently reflects and preserves EVERY
coarsened relation through the literal firstForgetIndex.

These are exact relational transport lemmas, not existence theorems
for strong hypergraph embeddings or the selected lower Ramsey family.
They do not prove colour-arrow selection or strong inducedness on
their own; those properties are independent of train level indexing.
The selected maps here are GIVEN injective maps of physical edge
labels and are retained unchanged.

Uncompiled candidate; strict kernel axiom audit required.
-/

namespace StructuralRamsey.Girth

universe v
variable {E F I : Type v}

/-- Forgetting inserted cuts preserves and reflects EVERY coarse
train relation under the same given physical-edge map. -/
theorem EdgeTrainLevels.forgetFirstCuts_map_rel_iff
    {m d : ℕ}
    (S : EdgeTrainLevels E (m + d))
    (T : EdgeTrainLevels F (m + d))
    (hm : 0 < m) (f : E → F)
    (hFine : ∀ ν : Fin (m + d + 1), ∀ a b : E,
      S.rel ν a b ↔ T.rel ν (f a) (f b))
    (μ : Fin (m + 1)) (a b : E) :
    (S.forgetFirstCuts hm).rel μ a b ↔
      (T.forgetFirstCuts hm).rel μ (f a) (f b) := by
  change S.rel (EdgeTrainLevels.firstForgetIndex m d μ) a b ↔
    T.rel (EdgeTrainLevels.firstForgetIndex m d μ) (f a) (f b)
  exact hFine _ a b

/-- For a specified family of injective edge maps, **the same
indices and maps** remain relation-preserving and -reflecting
after coarsening. This is the train-relation component of the
selected embedding clause in the forgetting lemma. -/
theorem EdgeTrainLevels.forgetFirstCuts_selected_rel_iff
    {m d : ℕ}
    (S : EdgeTrainLevels E (m + d))
    (T : EdgeTrainLevels F (m + d))
    (hm : 0 < m) (selected : I → E ↪ F)
    (hFine : ∀ i : I, ∀ ν : Fin (m + d + 1), ∀ a b : E,
      S.rel ν a b ↔
        T.rel ν (selected i a) (selected i b)) :
    ∀ i : I, ∀ μ : Fin (m + 1), ∀ a b : E,
      (S.forgetFirstCuts hm).rel μ a b ↔
        (T.forgetFirstCuts hm).rel μ (selected i a) (selected i b) := by
  intro i μ a b
  exact S.forgetFirstCuts_map_rel_iff T hm (selected i)
    (hFine i) μ a b

end StructuralRamsey.Girth

#print axioms StructuralRamsey.Girth.EdgeTrainLevels.forgetFirstCuts_map_rel_iff
#print axioms StructuralRamsey.Girth.EdgeTrainLevels.forgetFirstCuts_selected_rel_iff
