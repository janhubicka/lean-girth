import Girth.TrainActiveGluingWitness
import Girth.TrainRecursiveRefinementForget
import Girth.TrainSystemCutGirthFullConverse

set_option autoImplicit false
set_option Elab.async false

/-!
# Full system girth at the retained cuts of the actual local witness

Forgetting initial refinement cuts changes only the choice of train
coordinate.  At each retained coordinate, the local incidence record is
literally the same record: every physical edge, prescribed gluing index,
whole gluing-image carrier and quotient wagon label is retained.

Consequently positive, nonterminal fine full-system bounds at cutoffs at
least two supply the coarse `interiorFull` field used by the actual
attachment.  The fine certificates remain inputs; no completed coarse
bound, vertex coverage, nonempty source or injective family of carriers
is assumed.

The same actual incidence record also has exactly the train's complete
quotient-labelled wagon carriers.  Its full-system bounds therefore give
the physical labelled cut bounds used by first-wagon refinement, without
changing any designated gluing-copy index.
-/

namespace StructuralRamsey.Girth

universe u v
variable {L : RelLanguage.{u}} {UA P X Y I : Type v}

/-- The actual gluing system's entire labelled wagon family is the
physical train's entire quotient-labelled carrier family. -/
theorem activeGluingWitness_wagonCarrier_eq
    (A : RelStructure L UA) (C : StructuralRamsey.Partite.System L P X)
    (α : UA → P) (R : RelStructure L Y)
    (f : I → RelStructure.Embedding
      (C.toRelStructure.induce (activeCarrier A C α)) R)
    {m : ℕ} (T : EdgeTrainLevels (OldACarrierEdge A R) m)
    (μ : Fin (m + 1)) :
    (fun p : Quotient (T.wagonSetoid μ) =>
      {x : Y | (activeGluingWitnessOrderOneData A C α R f T μ).WagonVertex p x}) =
      T.wagonClassCarrier (fun edge => edge.1) μ := by
  funext p
  ext x
  induction p using Quotient.inductionOn with
  | h edge =>
      constructor
      · rintro ⟨e, he, hx⟩
        exact ⟨e, (T.equivalent μ).symm (Quotient.exact he), hx⟩
      · rintro ⟨e, he, hx⟩
        exact ⟨e, Quotient.sound ((T.equivalent μ).symm he), hx⟩

/-- Full-system girth of the actual whole-image gluing system supplies
girth of the complete physical wagon cut at the same cutoff. -/
theorem activeGluingWitness_labelledCutGirth_of_fullSystemGirth
    (A : RelStructure L UA) (C : StructuralRamsey.Partite.System L P X)
    (α : UA → P) (R : RelStructure L Y)
    (f : I → RelStructure.Embedding
      (C.toRelStructure.induce (activeCarrier A C α)) R)
    {m : ℕ} (T : EdgeTrainLevels (OldACarrierEdge A R) m)
    (μ : Fin (m + 1)) (q : ℕ)
    (hFull :
      (activeGluingWitnessOrderOneData A C α R f T μ).FullSystemGirthGT q) :
    LabelledGirthGT (T.wagonClassCarrier (fun edge => edge.1) μ) q := by
  rw [← activeGluingWitness_wagonCarrier_eq A C α R f T μ]
  exact (activeGluingWitnessOrderOneData A C α R f T μ).fullSystemGirth_implies_labelledWagonCutGirth
    q hFull

/-- Retaining a fine cut preserves the complete actual local incidence
record, including all labels and whole gluing-copy images. -/
theorem activeGluingWitness_forgetFirstCuts_eq
    (A : RelStructure L UA) (C : StructuralRamsey.Partite.System L P X)
    (α : UA → P) (R : RelStructure L Y)
    (f : I → RelStructure.Embedding
      (C.toRelStructure.induce (activeCarrier A C α)) R)
    {m d : ℕ} (T : EdgeTrainLevels (OldACarrierEdge A R) (m + d))
    (hm : 0 < m) (μ : Fin (m + 1)) :
    activeGluingWitnessOrderOneData A C α R f (T.forgetFirstCuts hm) μ =
      activeGluingWitnessOrderOneData A C α R f T
        (EdgeTrainLevels.firstForgetIndex m d μ) := rfl

/-- The actual fine witness's positive full-system certificates imply all
coarse interior order-two bounds.  Retained positive interior coordinates
remain positive and nonterminal in the fine train, and their supplied
cutoffs are lowered to two only after the exact incidence identification. -/
theorem activeGluingWitness_interiorFull_of_fine
    (A : RelStructure L UA) (C : StructuralRamsey.Partite.System L P X)
    (α : UA → P) (R : RelStructure L Y)
    (f : I → RelStructure.Embedding
      (C.toRelStructure.induce (activeCarrier A C α)) R)
    {m d : ℕ} (T : EdgeTrainLevels (OldACarrierEdge A R) (m + d))
    (hm : 0 < m)
    (hFine : ∀ ν : Fin (m + d + 1), 0 < ν.val → ν.val < m + d →
      ∃ q : ℕ, 2 ≤ q ∧
        (activeGluingWitnessOrderOneData A C α R f T ν).FullSystemGirthGT q) :
    ∀ μ : Fin (m + 1), 0 < μ.val → μ.val < m →
      (activeGluingWitnessOrderOneData A C α R f
        (T.forgetFirstCuts hm) μ).FullSystemGirthGT 2 := by
  intro μ hPos hLt
  let ν := EdgeTrainLevels.firstForgetIndex m d μ
  have hν : ν.val = μ.val + d := by
    simp only [ν, EdgeTrainLevels.firstForgetIndex, Nat.ne_of_gt hPos, ↓reduceIte]
  obtain ⟨q, hq, hFull⟩ := hFine ν (by omega) (by omega)
  change (activeGluingWitnessOrderOneData A C α R f T ν).FullSystemGirthGT 2
  refine ⟨hFull.1, ?_⟩
  intro n cycle hAccept hSmall
  exact hFull.2 n cycle hAccept (by omega)

end StructuralRamsey.Girth
