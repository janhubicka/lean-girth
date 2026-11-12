import Girth.TrainRecursiveCoarsenedSelectedRestriction
import Girth.TrainRecursiveExactHeightTransport

set_option autoImplicit false
set_option Elab.async false

/-!
# Actual selected fine train reflection at the recursive height

The selected lower ForestTailStage records target train preservation AND
reflection on every source A-edge and every selected designated copy.
The lower recursive cutoff vector is arithmetically equal in length to
the actual first-wagon refined train, but its dependent Fin index type
is not necessarily definitionally equal.

Transport the SAME complete physical train across that height equality,
without requiring a second independent restriction hypothesis, altering
wagon quotient indices, identifying carrier-coincident selected copies,
or forgetting the bottom and top levels.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}} {UA X V : Type v}

/-- Equality-transported trains have exactly the old relation on the
corresponding Fin coordinate; physical edge labels are unchanged. -/
theorem EdgeTrainLevels.castHeight_rel_iff
    {Edge : Type v} {m n : ℕ}
    (T : EdgeTrainLevels Edge m) (h : m = n)
    (ν : Fin (n + 1)) (a b : Edge) :
    (T.castHeight h).rel ν a b ↔
      T.rel (Fin.cast (congrArg (fun k : ℕ => k + 1) h).symm ν) a b := by
  cases h
  rfl

end StructuralRamsey.Girth

namespace StructuralRamsey.Girth.TrainRecursiveWitness

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}} {UA X V : Type v}

/-- The REAL selected lower stage's targetRestriction, at its exact
cutoff-vector length, provides the full refined fine-witness restriction
at the original refinement height. The gluing family is the literal
selected designated-copy subtype, and source/target labels are not
quotiented by their underlying carriers. -/
theorem ForestTailStage.coarsenedSelected_fineRestriction_castHeight
    (A : RelStructure L UA)
    (Target : StructuralRamsey.Partite.System L UA X)
    (Large : StructuralRamsey.Partite.System L UA V)
    {h : ℕ} (refinedTrain : EdgeTrainLevels
      (OldACarrierEdge A Target.toRelStructure) h)
    {cuts : List ℕ} (hLen : cuts.length = h)
    {family : Set (Embedding Target.toRelStructure Large.toRelStructure)}
    {allowed : Fin (cuts.length + 1) → Set V}
    (S : ForestTailStage A Target.toRelStructure Large.toRelStructure
      family cuts (refinedTrain.castHeight hLen.symm) allowed)
    (hFamilyParts : ∀ b, b ∈ family → ∀ x : X,
      Large.part (b x) = Target.part x) :
    let E := S.system.coarsenVia Large S.isPartite
    let I := {b : DesignatedCopy Target.toRelStructure
      Large.toRelStructure S.system family // b ∈ S.selected}
    let f : I → StructuralRamsey.Partite.Embedding Target E :=
      fun i => selectedPartiteGluingFamily_of_largeBase
        Target Large S.system S.isPartite family hFamilyParts
        S.selected i
    let T := S.train.castHeight hLen
    ∀ ν : Fin (h + 1), ∀ i : I,
      ∀ a b : Embedding A Target.toRelStructure,
        T.rel ν (actualEdge ((f i).toEmbedding.comp a))
          (actualEdge ((f i).toEmbedding.comp b)) ↔
        refinedTrain.rel ν (actualEdge a) (actualEdge b) := by
  let E := S.system.coarsenVia Large S.isPartite
  let I := {b : DesignatedCopy Target.toRelStructure
    Large.toRelStructure S.system family // b ∈ S.selected}
  let f : I → StructuralRamsey.Partite.Embedding Target E :=
    fun i => selectedPartiteGluingFamily_of_largeBase
      Target Large S.system S.isPartite family hFamilyParts S.selected i
  let T := S.train.castHeight hLen
  dsimp only
  intro ν i a b
  let ρ : Fin (cuts.length + 1) :=
    Fin.cast (congrArg (fun k : ℕ => k + 1) hLen).symm ν
  have hRestriction : S.train.rel ρ
      (actualEdge ((f i).toEmbedding.comp a))
      (actualEdge ((f i).toEmbedding.comp b)) ↔
      (refinedTrain.castHeight hLen.symm).rel ρ
        (actualEdge a) (actualEdge b) := by
    change S.train.rel ρ
      (actualEdge (i.1.embedding.comp a))
      (actualEdge (i.1.embedding.comp b)) ↔
      (refinedTrain.castHeight hLen.symm).rel ρ
        (actualEdge a) (actualEdge b)
    exact S.targetRestriction i.1 i.2 ρ a b
  have hBack : (refinedTrain.castHeight hLen.symm).rel ρ
      (actualEdge a) (actualEdge b) ↔
      refinedTrain.rel ν (actualEdge a) (actualEdge b) := by
    have hIndex :
        Fin.cast (congrArg (fun k : ℕ => k + 1) hLen.symm).symm ρ = ν :=
      Fin.ext rfl
    simpa only [hIndex] using
      (EdgeTrainLevels.castHeight_rel_iff refinedTrain hLen.symm ρ
        (actualEdge a) (actualEdge b))
  exact (EdgeTrainLevels.castHeight_rel_iff S.train hLen ν
    (actualEdge ((f i).toEmbedding.comp a))
    (actualEdge ((f i).toEmbedding.comp b))).trans
    (hRestriction.trans hBack)

end StructuralRamsey.Girth.TrainRecursiveWitness
