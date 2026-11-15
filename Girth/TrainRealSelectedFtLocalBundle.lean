import Girth.TrainRecursiveCoarsenedSelectedIndexedBundle
import Girth.TrainIndexedPartitePhysicalArrow
import Girth.TrainRecursiveActualCoarsenedFullSystem

set_option autoImplicit false
set_option Elab.async false

/-!
# The actual SAME-VECTOR selected lower F_t stage supplies the local data

The genuine selected ForestTailStage used as the lower F_t witness
already carries:
  (a) partiteness of the coarsened local core over the source A;
  (b) irreducible-A coverage of the complete local core;
  (c) injectivity of selected COMPLETE physical support pieces;
  (d) the finite mixed-SET support forest through q;
  (e) exact restriction of the selected physical train at every cut;
  (f) actual adjacent core-part intersection parameters;
  (g) an INDEXED partite Ramsey arrow retaining the selected label.

The checked indexed bundle proves all seven fields. For a finite
ordered A, the checked rigid-partite conversion, composed with the
literal physical-edge labelling, gives the PHYSICAL A-edge-colouring
arrow required by the actual old-stage picture step. Thus no
separate local edge-Ramsey oracle is needed.

The positive local FullSystemGirthGT certificates follow separately
from the checked coarsened-selected positive theorem, without
downgrading or pruning any physical edge labels. This file only
packages the seven fields plus the physical arrow; it does not
construct the lower selected F_t stage or the remaining same-vector
old/core train identification.
-/

namespace StructuralRamsey.Girth.TrainRecursiveWitness

open StructuralRamsey.RelStructure

universe u v w
variable {L : RelLanguage.{u}} {UA X V I : Type v}

/-- Genuine selected lower F_t stage data plus the precise PHYSICAL
A-edge Ramsey arrow on the actual coarsened local core. The
family index is the LITERAL selected designated-copy subtype. -/
theorem ForestTailStage.coarsenedSelected_Ft_localData_and_physicalArrow
    (A₀ : RelStructure L UA) [LinearOrder UA] [Finite UA]
    (Target : StructuralRamsey.Partite.System L.withOrder UA X)
    (Large : StructuralRamsey.Partite.System L.withOrder UA V)
    (family : Set (Embedding Target.toRelStructure Large.toRelStructure))
    {t : List ℕ}
    {targetTrain : EdgeTrainLevels
      (OldACarrierEdge A₀.ordered Target.toRelStructure) t.length}
    (fineAllowed : Fin (t.length + 1) → Set UA)
    (S : ForestTailStage A₀.ordered Target.toRelStructure
      Large.toRelStructure family t targetTrain
      (fun ν => Large.part ⁻¹' fineAllowed ν))
    (hTarget : Target.IsPartiteOver A₀.ordered)
    (hLarge : Large.IsPartiteOver A₀.ordered)
    (hTargetCoverage :
      IrreduciblesExtendTo A₀.ordered Target.toRelStructure)
    (hFamilyParts : ∀ b, b ∈ family → ∀ x : X,
      Large.part (b x) = Target.part x)
    (q : ℕ) (hq : q ≤ t.headD 0)
    (κ : Type w) [Nonempty κ]
    (hArrow : DesignatedArrow S κ) :
    let E := S.system.coarsenVia Large S.isPartite
    let J := {b : DesignatedCopy Target.toRelStructure
      Large.toRelStructure S.system family // b ∈ S.selected}
    let f : J → StructuralRamsey.Partite.Embedding Target E :=
      fun i => selectedPartiteGluingFamily_of_largeBase
        Target Large S.system S.isPartite family hFamilyParts
        S.selected i
    E.IsPartiteOver A₀.ordered ∧
      IrreduciblesExtendTo A₀.ordered E.toRelStructure ∧
      Function.Injective (fun i : J =>
        bSupportPiece A₀.ordered ((f i).toEmbedding)) ∧
      FiniteMixedForestThrough
        (RelationalMixedSupportTest A₀.ordered
          (fun i : J => (f i).toEmbedding)) q ∧
      (∀ (ν : Fin (t.length + 1)) (i : J)
        (a b : Embedding A₀.ordered Target.toRelStructure),
        S.train.rel ν
          (actualEdge ((f i).toEmbedding.comp a))
          (actualEdge ((f i).toEmbedding.comp b)) ↔
        targetTrain.rel ν (actualEdge a) (actualEdge b)) ∧
      S.train.AdjacentParameters (fun edge => edge.1)
        (fun ν => E.part ⁻¹' fineAllowed ν) ∧
      (∀ χ : OldACarrierEdge A₀.ordered E.toRelStructure → κ,
        ∃ i : J, ∀ a b : Embedding A₀.ordered Target.toRelStructure,
          χ (actualEdge ((f i).toEmbedding.comp a)) =
            χ (actualEdge ((f i).toEmbedding.comp b))) := by
  let E := S.system.coarsenVia Large S.isPartite
  let J := {b : DesignatedCopy Target.toRelStructure
    Large.toRelStructure S.system family // b ∈ S.selected}
  let f : J → StructuralRamsey.Partite.Embedding Target E :=
    fun i => selectedPartiteGluingFamily_of_largeBase
      Target Large S.system S.isPartite family hFamilyParts
      S.selected i
  have hBundle :=
    S.coarsenedSelected_actualIndexedLocalInputBundle
      A₀.ordered Target Large family fineAllowed
      hLarge hTargetCoverage hFamilyParts q hq κ hArrow
  obtain ⟨hPartite, hCoverage, hInjective, hForest, hTrain,
      hParams, hIndexed⟩ := hBundle
  have hPhysical :=
    indexedPhysicalArrow_of_partiteFamilyArrow_for_orderedA
      A₀ Target E f hTarget κ hIndexed
  exact ⟨hPartite, hCoverage, hInjective, hForest,
    hTrain, hParams, hPhysical⟩

end StructuralRamsey.Girth.TrainRecursiveWitness
