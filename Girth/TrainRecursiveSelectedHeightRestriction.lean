import Girth.TrainRecursiveCoarsenedSelectedRestriction
import Girth.TrainRecursiveExactHeightTransport

set_option autoImplicit false
set_option Elab.async false

/-!
# Selected target-train restriction survives an exact height cast

A genuine lower ForestTailStage uses the exact selected designated-copy
subtype. If its prescribed target train is a height cast of a physical
train on the same full edge set, casting the lower stage back gives
restriction to that physical train at EVERY coordinate. Neither the
selected index nor any physical carrier is changed or quotient-ed.

This is the reusable arithmetic interface for the true active first
refinement; it is not lower-stage existence or a system-girth claim.
-/

namespace StructuralRamsey.Girth.TrainRecursiveWitness

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}} {UA VB P X : Type v}

private theorem castHeight_rel_iff_selected
    {W : Type v} {m n : ℕ}
    (S : EdgeTrainLevels W m) (h : m = n)
    (ν : Fin (n + 1)) (a b : W) :
    (S.castHeight h).rel ν a b ↔
      S.rel (Fin.cast (congrArg (fun k : ℕ => k + 1) h).symm ν) a b := by
  cases h
  rfl

/-- Every selected original target-train relation survives the cast
in BOTH directions, including bottom equality and the universal top.
This derives the full hRestriction required for the fine attachment. -/
theorem ForestTailStage.coarsenedSelected_trainRestriction_castBack
    (A : RelStructure L UA)
    (Target : StructuralRamsey.Partite.System L UA VB)
    (Large : StructuralRamsey.Partite.System L UA P)
    {t : List ℕ} {m : ℕ}
    (sourceTrain : EdgeTrainLevels (OldACarrierEdge A Target.toRelStructure) m)
    (hLen : t.length = m)
    {family : Set (Embedding Target.toRelStructure Large.toRelStructure)}
    {allowed : Fin (t.length + 1) → Set P}
    (S : ForestTailStage A Target.toRelStructure Large.toRelStructure
      family t (sourceTrain.castHeight hLen.symm) allowed)
    (hFamilyParts : ∀ b, b ∈ family → ∀ x : VB,
      Large.part (b x) = Target.part x) :
    let E := S.system.coarsenVia Large S.isPartite
    let I := {b : DesignatedCopy Target.toRelStructure
      Large.toRelStructure S.system family // b ∈ S.selected}
    let f : I → Embedding Target.toRelStructure E.toRelStructure :=
      fun i => (selectedPartiteGluingFamily_of_largeBase
        Target Large S.system S.isPartite family hFamilyParts
        S.selected i).toEmbedding
    ∀ (ν : Fin (m + 1)) (i : I)
      (a b : Embedding A Target.toRelStructure),
      (S.train.castHeight hLen).rel ν
        (actualEdge ((f i).comp a)) (actualEdge ((f i).comp b)) ↔
      sourceTrain.rel ν (actualEdge a) (actualEdge b) := by
  classical
  let E := S.system.coarsenVia Large S.isPartite
  let I := {b : DesignatedCopy Target.toRelStructure
    Large.toRelStructure S.system family // b ∈ S.selected}
  let f : I → Embedding Target.toRelStructure E.toRelStructure :=
    fun i => (selectedPartiteGluingFamily_of_largeBase
      Target Large S.system S.isPartite family hFamilyParts
      S.selected i).toEmbedding
  dsimp only
  intro ν i a b
  let νLower : Fin (t.length + 1) :=
    Fin.cast (congrArg (fun k : ℕ => k + 1) hLen).symm ν
  have hBack :
      Fin.cast (congrArg (fun k : ℕ => k + 1) hLen.symm).symm νLower =
        ν := Fin.ext rfl
  have hRaw := S.coarsenedSelected_trainRestriction
    A Target Large hFamilyParts νLower i a b
  have hRHS :
      S.train.rel νLower
        (actualEdge ((f i).comp a)) (actualEdge ((f i).comp b)) ↔
      sourceTrain.rel ν (actualEdge a) (actualEdge b) := by
    simpa only [castHeight_rel_iff_selected, hBack] using hRaw
  exact (castHeight_rel_iff_selected S.train hLen ν
    (actualEdge ((f i).comp a)) (actualEdge ((f i).comp b))).trans hRHS

end StructuralRamsey.Girth.TrainRecursiveWitness
