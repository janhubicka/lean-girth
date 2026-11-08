import Girth.TrainRecursiveTrueActiveCoverage
import Girth.TrainRecursiveNontrivialFibre

set_option autoImplicit false
set_option Elab.async false

/-!
# Nonempty active fibres without a separate coverage assumption

In the nontrivial physical-fibre branch of the finite Ramsey pass, an actual
projected A-copy is already supplied. Since A is nonempty, its image gives
a point of the TRUE active carrier. The existing high-girth
irreducible-coverage theorem can therefore be applied without an additional
nonempty-active-carrier hypothesis.

For ordered A the same-copy rigidity premise is automatic. The final
specialization consumes the physical two-copy dispatch condition, so it
fits the real fresh nontrivial-fibre step rather than an abstract target.

Neither theorem constructs the lower recursive stage, a local PictureStep,
a full-system gluing girth certificate, nor output SupremeCycleBound.
Circulation-only: no appendix or manuscript marker is changed.
-/

namespace StructuralRamsey.Girth.TrainRecursiveWitness

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}} {UA VB P : Type v}

section General

variable {A : RelStructure L UA} {B : RelStructure L VB}
variable {D : RelStructure L P} {family : Set (Embedding B D)}
variable {t : List ℕ}
variable {targetTrain : EdgeTrainLevels (OldACarrierEdge A B) t.length}
variable {allowed : Fin (t.length + 1) → Set P}

/-- The image of one genuine projected A-embedding witnesses nonemptiness
of the complete physical active carrier. Nonemptiness of A is necessary. -/
theorem ForestTailStage.activeCarrier_nonempty_of_projected
    [Nonempty UA]
    (stage : ForestTailStage A B D family t targetTrain allowed)
    (e : Embedding A D)
    (projected : StructuralRamsey.Partite.ProjectedEmbedding
      A stage.system e.toFunctionEmbedding) :
    (activeCarrier A stage.system e.toFunctionEmbedding).Nonempty := by
  obtain ⟨x⟩ := (inferInstance : Nonempty UA)
  exact ⟨projected.val x,
    projected_mem_activeCarrier A stage.system
      e.toFunctionEmbedding projected x⟩

/-- At head cutoff at least three, a nonempty projected copy discharges
the only extra active-carrier premise in the checked true-active A-coverage
argument. The source is the literal induced active structure. -/
theorem ForestTailStage.trueActive_irreduciblesExtendTo_of_projected
    [Nonempty UA]
    (stage : ForestTailStage A B D family t targetTrain allowed)
    (hA : A.Irreducible)
    (hBaseLinear : ALinear A D)
    (hBaseStrong : ∀ b : DesignatedCopy B D stage.system family,
      b ∈ stage.selected → AStrong A D (copyCarrier b.base))
    (e : Embedding A D)
    (hRigid : ∀ a : Embedding A D, SameCopy a e → a = e)
    (projected : StructuralRamsey.Partite.ProjectedEmbedding
      A stage.system e.toFunctionEmbedding)
    (hHigh : 3 ≤ t.headD 0) :
    IrreduciblesExtendTo A
      (actualActiveSubsystemPartite A stage.system
        e.toFunctionEmbedding).toRelStructure := by
  have hActive := stage.activeCarrier_nonempty_of_projected e projected
  exact stage.trueActive_irreduciblesExtendTo
    hA hBaseLinear hBaseStrong e hRigid hActive projected hHigh

end General

section Ordered

variable (A₀ : RelStructure L UA) [LinearOrder UA] [Finite UA] [Nonempty UA]
variable {B : RelStructure L.withOrder VB}
variable {D : RelStructure L.withOrder P}
variable {family : Set (Embedding B D)} {t : List ℕ}
variable {targetTrain : EdgeTrainLevels
  (OldACarrierEdge A₀.ordered B) t.length}
variable {allowed : Fin (t.length + 1) → Set P}

/-- In the actual nontrivial ordered-source profile, the two distinct
physical projected copies give the source-copy and nonempty carrier,
while ordered same-copy rigidity needs no separate hypothesis. -/
theorem ForestTailStage.orderedTrueActive_irreduciblesExtendTo_of_nontrivial
    (stage : ForestTailStage A₀.ordered B D family t targetTrain allowed)
    (hBaseLinear : ALinear A₀.ordered D)
    (hBaseStrong : ∀ b : DesignatedCopy B D stage.system family,
      b ∈ stage.selected →
        AStrong A₀.ordered D (copyCarrier b.base))
    (e : Embedding A₀.ordered D)
    (hPhysical : ∃ a b : StructuralRamsey.Partite.ProjectedEmbedding
      A₀.ordered stage.system e.toFunctionEmbedding,
      copyCarrier a.val ≠ copyCarrier b.val)
    (hHigh : 3 ≤ t.headD 0) :
    IrreduciblesExtendTo A₀.ordered
      (actualActiveSubsystemPartite A₀.ordered stage.system
        e.toFunctionEmbedding).toRelStructure := by
  obtain ⟨projected, _, _⟩ := hPhysical
  have hA : A₀.ordered.Irreducible :=
    (RelStructure.ordered_hereditarilyIrreducible A₀).irreducible
  exact stage.trueActive_irreduciblesExtendTo_of_projected
    hA hBaseLinear hBaseStrong e
    (fun a ha => ordered_embedding_eq_of_sameCopy a e ha)
    projected hHigh

end Ordered

end StructuralRamsey.Girth.TrainRecursiveWitness
