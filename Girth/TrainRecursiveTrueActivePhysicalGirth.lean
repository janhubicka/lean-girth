import Girth.TrainRecursiveTrueActiveCoverage
import Girth.ForestActualRecursiveSupport

set_option autoImplicit false
set_option Elab.async false

/-!
# Physical support girth of the genuine active lower target

In the q > 2 forest recursion the lower target is exactly the
induced structure on the TRUE active A-copy carrier, not the entire
part fibre and not the high-dimensional Hales--Jewett Ramsey base.

The OLD ForestTailStage has a complete mixed forest at its bottom
cutoff, including every ambient physical A-edge even if it belongs
to no designated B-copy. It therefore has ordinary A-support girth
at that cutoff. The A-support of the genuine induced active target
embeds in this unchanged ambient support family, so girth persists
at EVERY smaller requested cutoff.

The source has nonempty A-support whenever its active carrier is
nonempty. Both statements are actual geometric invariants, not
standalone lower recursive witness or SupremeCycleBound inputs.
-/

namespace StructuralRamsey.Girth.TrainRecursiveWitness

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}} {UA VB P : Type v}

/-- The genuine active lower target inherits ALL requested physical
A-support girth bounds below the old mixed-forest bottom cutoff.
No Hales--Jewett power or selected-edge pruning is involved. -/
theorem ForestTailStage.trueActive_supportGirthGT
    (A : RelStructure L UA) (B : RelStructure L VB)
    (D : RelStructure L P)
    {family : Set (Embedding B D)}
    {t : List ℕ}
    {targetTrain : EdgeTrainLevels (OldACarrierEdge A B) t.length}
    {allowed : Fin (t.length + 1) → Set P}
    (S : ForestTailStage A B D family t targetTrain allowed)
    (e : Embedding A D)
    (q : ℕ) (hq : q ≤ t.headD 0) :
    GirthGT
      (supportCopies A
        (actualActiveSubsystemPartite
          A S.system e.toFunctionEmbedding).toRelStructure) q := by
  have hAmbient :
      GirthGT (supportCopies A S.system.toRelStructure) (t.headD 0) := by
    apply girthGT_of_finiteMixedForestThrough _ _ (t.headD 0) S.bottomForest
    rintro edge ⟨a, rfl⟩
    exact Or.inl ⟨a, rfl⟩
  change GirthGT
    (supportCopies A
      (S.system.toRelStructure.induce
        (activeCarrier A S.system e.toFunctionEmbedding))) q
  exact supportGirthGT_induce A S.system.toRelStructure
    (activeCarrier A S.system e.toFunctionEmbedding) q
    (girthGT_mono hAmbient hq)

/-- A nonempty true active carrier has a genuine ambient A-edge
inside the exact induced target. In particular this also handles
the empty irreducible-substructure case without postulating a
fictitious selected B-copy. -/
theorem ForestTailStage.trueActive_supportNonempty
    (A : RelStructure L UA) (B : RelStructure L VB)
    (D : RelStructure L P)
    {family : Set (Embedding B D)}
    {t : List ℕ}
    {targetTrain : EdgeTrainLevels (OldACarrierEdge A B) t.length}
    {allowed : Fin (t.length + 1) → Set P}
    (S : ForestTailStage A B D family t targetTrain allowed)
    (e : Embedding A D)
    (hActive : (activeCarrier A S.system e.toFunctionEmbedding).Nonempty) :
    Nonempty (OldACarrierEdge A
      (actualActiveSubsystemPartite
        A S.system e.toFunctionEmbedding).toRelStructure) := by
  obtain ⟨edge, he⟩ :=
    actualRecursiveActiveSupport_nonempty
      A S.system e.toFunctionEmbedding hActive
  exact ⟨⟨edge, he⟩⟩

end StructuralRamsey.Girth.TrainRecursiveWitness
