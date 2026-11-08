import Girth.TrainFillingIndexedContractedTrain
import Girth.TrainFillingIndexedColouredInsertionOrder
import Girth.TrainRecursiveParameterRestrictionKernel
import Girth.TrainLabelledCutGirth
import Girth.TrainRecursiveWitnessPass

set_option Elab.async false

/-!
# The contracted train on ACTUAL relational support edges of M

The shortened-train induction has to use genuine physical A-support
edges of its relational source M, not the abstract occurrence names
(choice, first wagon). When M has exactly the complete contracted
first-wagon carriers as A-support, the verified first-wagon
injectivity and support equality give an exact EQUIVALENCE of the
two physical edge types, including every occurrence and no phantom
or unused source edge.

Pull the checked contracted component train back along this exact
equivalence. All quotient cuts, labelled girth and AdjacentParameters
then transport without changing the ambient vertex set, shrinking
edge carriers, or identifying repeated labelled occurrences.

Finally instantiate the construction on the ACTUAL indexed
colour-block-ordered M already checked in main. That definition
introduces no source-train existence assumption and is the geometric
link needed to apply the shorter-train induction to G0.
It does not construct the selected M-copy, its Ramsey arrow, or
full A2/A3 system-girth at the target.
-/

namespace StructuralRamsey.Girth.IndexedPrivateChoice

open StructuralRamsey.RelStructure

universe u v
variable {C V P X UA : Type v} {L : RelLanguage.{u}}
variable (U : C → PrivateWagonInput V P X)

/-- The labelled contracted first wagons are exactly ALL genuine
physical A-support edges of the relational M, with inverse uniquely
recovering their choice and first-wagon owner. -/
noncomputable def contractedPhysicalEdgeEquiv [Nontrivial X]
    (A : RelStructure L UA)
    (M : RelStructure L (Vertex U))
    (hSupport : supportCopies A M = Set.range (contractedCarrier U))
    (hLinear : ∀ c : C, ∀ p q : P, p ≠ q →
      ((U c).oldCarrier p ∩ (U c).oldCarrier q).Subsingleton) :
    (C × P) ≃ OldACarrierEdge A M := by
  let f : (C × P) → OldACarrierEdge A M := fun cp =>
    ⟨contractedCarrier U cp, by
      rw [hSupport]
      exact ⟨cp, rfl⟩⟩
  apply Equiv.ofBijective f
  constructor
  · intro a b hab
    exact contractedCarrier_injective U hLinear
      (congrArg Subtype.val hab)
  · rintro ⟨e, he⟩
    have h : e ∈ Set.range (contractedCarrier U) := by
      rw [← hSupport]
      exact he
    obtain ⟨cp, hcp⟩ := h
    refine ⟨cp, ?_⟩
    exact Subtype.ext hcp

@[simp] theorem contractedPhysicalEdgeEquiv_carrier [Nontrivial X]
    (A : RelStructure L UA) (M : RelStructure L (Vertex U))
    (hSupport : supportCopies A M = Set.range (contractedCarrier U))
    (hLinear : ∀ c : C, ∀ p q : P, p ≠ q →
      ((U c).oldCarrier p ∩ (U c).oldCarrier q).Subsingleton)
    (cp : C × P) :
    (contractedPhysicalEdgeEquiv U A M hSupport hLinear cp).1 =
      contractedCarrier U cp := rfl

/-- Exact reverse physical carrier identity for the recovered owner. -/
theorem contractedPhysicalEdgeEquiv_symm_carrier [Nontrivial X]
    (A : RelStructure L UA) (M : RelStructure L (Vertex U))
    (hSupport : supportCopies A M = Set.range (contractedCarrier U))
    (hLinear : ∀ c : C, ∀ p q : P, p ≠ q →
      ((U c).oldCarrier p ∩ (U c).oldCarrier q).Subsingleton)
    (e : OldACarrierEdge A M) :
    contractedCarrier U
        ((contractedPhysicalEdgeEquiv U A M hSupport hLinear).symm e) =
      e.1 := by
  have h := congrArg Subtype.val
    ((contractedPhysicalEdgeEquiv U A M hSupport hLinear).apply_symm_apply e)
  simpa only [contractedPhysicalEdgeEquiv_carrier] using h

/-- The ACTUAL shortened edge train on the relational A-support
edge type. It is the exact reindexing of the checked heterogeneous
choice train, not a second ad hoc equivalence hierarchy. -/
noncomputable def contractedPhysicalTrain [Nontrivial X]
    (A : RelStructure L UA) (M : RelStructure L (Vertex U))
    {m : ℕ} (T : EdgeTrainLevels P m) (hm : 0 < m)
    (hSupport : supportCopies A M = Set.range (contractedCarrier U))
    (hLinear : ∀ c : C, ∀ p q : P, p ≠ q →
      ((U c).oldCarrier p ∩ (U c).oldCarrier q).Subsingleton) :
    EdgeTrainLevels (OldACarrierEdge A M) m :=
  (contractedChoiceTrain U T hm).restrict
    (contractedPhysicalEdgeEquiv U A M hSupport hLinear).symm.toEmbedding

/-- Reflection and preservation of ALL train cuts on their genuine
relational source physical edge labels. -/
theorem contractedPhysicalTrain_rel_iff [Nontrivial X]
    (A : RelStructure L UA) (M : RelStructure L (Vertex U))
    {m : ℕ} (T : EdgeTrainLevels P m) (hm : 0 < m)
    (hSupport : supportCopies A M = Set.range (contractedCarrier U))
    (hLinear : ∀ c : C, ∀ p q : P, p ≠ q →
      ((U c).oldCarrier p ∩ (U c).oldCarrier q).Subsingleton)
    (μ : Fin (m + 1)) (e f : C × P) :
    (contractedPhysicalTrain U A M T hm hSupport hLinear).rel μ
      (contractedPhysicalEdgeEquiv U A M hSupport hLinear e)
      (contractedPhysicalEdgeEquiv U A M hSupport hLinear f) ↔
    (contractedChoiceTrain U T hm).rel μ e f := by
  change (contractedChoiceTrain U T hm).rel μ
      ((contractedPhysicalEdgeEquiv U A M hSupport hLinear).symm
        (contractedPhysicalEdgeEquiv U A M hSupport hLinear e))
      ((contractedPhysicalEdgeEquiv U A M hSupport hLinear).symm
        (contractedPhysicalEdgeEquiv U A M hSupport hLinear f)) ↔ _
  simp only [Equiv.symm_apply_apply]

/-- Quantitative labelled cut girth survives the physical reindexing
exactly. No inequality between abstract and actual edge sets is
postulated: equality of each complete carrier was proved above. -/
theorem contractedPhysicalTrain_labelledCutGirth [Nontrivial X]
    (A : RelStructure L UA) (M : RelStructure L (Vertex U))
    {m : ℕ} (T : EdgeTrainLevels P m) (hm : 0 < m)
    (hSupport : supportCopies A M = Set.range (contractedCarrier U))
    (hLinear : ∀ c : C, ∀ p q : P, p ≠ q →
      ((U c).oldCarrier p ∩ (U c).oldCarrier q).Subsingleton)
    (μ : Fin (m + 1)) (g : ℕ)
    (hOld : LabelledGirthGT
      ((contractedChoiceTrain U T hm).wagonClassCarrier
        (contractedCarrier U) μ) g) :
    LabelledGirthGT
      ((contractedPhysicalTrain U A M T hm hSupport hLinear).wagonClassCarrier
        (fun e : OldACarrierEdge A M => e.1) μ) g := by
  let φ := contractedPhysicalEdgeEquiv U A M hSupport hLinear
  have hShrink : ∀ e : OldACarrierEdge A M,
      e.1 ⊆ contractedCarrier U (φ.symm e) := by
    intro e
    change e.1 ⊆ contractedCarrier U
      ((contractedPhysicalEdgeEquiv U A M hSupport hLinear).symm e)
    rw [contractedPhysicalEdgeEquiv_symm_carrier
      U A M hSupport hLinear e]
  exact (contractedChoiceTrain U T hm).labelledCutGirth_restrict
    (contractedCarrier U) φ.symm.toEmbedding
    (fun e : OldACarrierEdge A M => e.1) hShrink μ g hOld

/-- The complete AdjacentParameters condition transfers to the real
relational M physical support train at EVERY adjacent cut, including
the common universal top. The permitted vertex sets do not change. -/
theorem contractedPhysicalTrain_adjacentParameters [Nontrivial X]
    (A : RelStructure L UA) (M : RelStructure L (Vertex U))
    {m : ℕ} (T : EdgeTrainLevels P m) (hm : 0 < m)
    (hSupport : supportCopies A M = Set.range (contractedCarrier U))
    (hLinear : ∀ c : C, ∀ p q : P, p ≠ q →
      ((U c).oldCarrier p ∩ (U c).oldCarrier q).Subsingleton)
    (allowed : Fin (m + 1) → Set (Vertex U))
    (hOld : (contractedChoiceTrain U T hm).AdjacentParameters
      (contractedCarrier U) allowed) :
    (contractedPhysicalTrain U A M T hm hSupport hLinear).AdjacentParameters
      (fun e : OldACarrierEdge A M => e.1) allowed := by
  let φ := contractedPhysicalEdgeEquiv U A M hSupport hLinear
  have hShrink : ∀ e : OldACarrierEdge A M,
      e.1 ⊆ contractedCarrier U (φ.symm e) := by
    intro e
    change e.1 ⊆ contractedCarrier U
      ((contractedPhysicalEdgeEquiv U A M hSupport hLinear).symm e)
    rw [contractedPhysicalEdgeEquiv_symm_carrier
      U A M hSupport hLinear e]
  exact (contractedChoiceTrain U T hm).adjacentParameters_restrict
    (contractedCarrier U) φ.symm.toEmbedding
    (fun e : OldACarrierEdge A M => e.1) hShrink allowed hOld


/-- The shortened train on the ALREADY CONSTRUCTED full heterogeneous
colour-block relational M. This uses exactly the checked actual
M-support equality and physical first-wagon injectivity, not an
independent choice of relational source edges or a postulated train
on their carrier sets. -/
noncomputable def actualIndexedContractedPhysicalTrain
    {I : Type v}
    [LinearOrder C] [LinearOrder V] [Fintype V]
    [LinearOrder P] [LinearOrder X] [Finite X]
    [LinearOrder I] [Nontrivial X]
    {k m : ℕ}
    (enumerateX : Fin k ≃ X) (hEnumerate : StrictMono enumerateX)
    (oldColour : V → I) (templateColour : X → I)
    (hColour : ∀ c : C, ∀ p : P,
      ∀ z : {v : V // v ∈ (U c).oldCarrier p},
        oldColour z.1 = templateColour ((U c).coordinate p z))
    (hCoordinate : ∀ c : C, ∀ p : P,
      StrictMono ((U c).coordinate p))
    (hXBlocks : ∀ x y : X,
      templateColour x ≠ templateColour y →
      x < y → templateColour x < templateColour y)
    (hLinear : ∀ c : C, ∀ p q : P, p ≠ q →
      ((U c).oldCarrier p ∩ (U c).oldCarrier q).Subsingleton)
    (T : EdgeTrainLevels P m) (hm : 0 < m) :
    EdgeTrainLevels
      (OldACarrierEdge
        (colouredOrderedEdgeSource k
          (fun i => templateColour (enumerateX i)))
        (actualIndexedContractedM U oldColour templateColour)) m :=
  contractedPhysicalTrain U
    (colouredOrderedEdgeSource k
      (fun i => templateColour (enumerateX i)))
    (actualIndexedContractedM U oldColour templateColour)
    T hm
    (actualIndexedContractedM_support_eq U enumerateX hEnumerate
      oldColour templateColour hColour hCoordinate hXBlocks)
    hLinear


end StructuralRamsey.Girth.IndexedPrivateChoice
