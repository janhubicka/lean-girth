import Girth.TrainRecursiveInitialTailLocalization
import Girth.LabelledWagonCutRestriction

/-!
# Target horizontal-cut bounds in the actual initial picture

Disjoint tagged copies preserve labelled Berge girth.  The proper initial
wagon coordinates identify the full initial cut with an injectively indexed
subfamily of those tagged target cuts.  This preserves wagon labels, including
distinct labels whose physical carriers might coincide.

The final bridge identifies the incidence model's full wagon carrier with
the train quotient carrier.  Target cut girth greater than two therefore
supplies the wagon part of physical pretrain linearity.
-/

namespace StructuralRamsey.Girth

universe u v

section Labelled

variable {V Q I : Type v}

/-- Lowering a labelled girth cutoff retains all original labels. -/
theorem labelledGirthGT_mono {H : Q → Set V} {g q : ℕ}
    (h : LabelledGirthGT H g) (hq : q ≤ g) : LabelledGirthGT H q := by
  rintro ⟨c, hc⟩
  exact h ⟨c, hc.trans hq⟩

/-- Distinct labelled carriers intersect in at most one vertex when
labelled girth is greater than two. -/
theorem labelledGirthGT_two_pairwise_subsingleton
    {H : Q → Set V} (h : LabelledGirthGT H 2) :
    ∀ p q : Q, p ≠ q → (H p ∩ H q).Subsingleton := by
  intro p q hpq x hx y hy
  by_contra hxy
  let c : LabelledBergeCycle H := {
    length := 2
    hlength := by omega
    label := ![p, q]
    vertex := ![x, y]
    label_injective := by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all
    vertex_injective := by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all
    left_mem := by
      intro i
      fin_cases i
      · exact hx.1
      · exact hy.2
    right_mem := by
      intro i
      fin_cases i
      · simpa [cyclicSucc] using hx.2
      · simpa [cyclicSucc] using hy.1
  }
  exact h ⟨c, by simp [c]⟩

/-- A disjoint union of labelled hypergraph copies has the same girth
lower bound.  The component coordinate is retained on both labels and
vertices, so no equal physical carriers are silently identified. -/
theorem labelledGirthGT_tagged
    (H : Q → Set V) (I : Type v) (q : ℕ)
    (h : LabelledGirthGT H q) :
    LabelledGirthGT
      (fun p : I × Q => (fun x : V => (p.1, x)) '' H p.2) q := by
  rintro ⟨c, hc⟩
  have hLeftTag (i : Fin c.length) : (c.vertex i).1 = (c.label i).1 := by
    obtain ⟨x, _, hx⟩ := c.left_mem i
    exact (congrArg Prod.fst hx).symm
  have hRightTag (i : Fin c.length) :
      (c.vertex i).1 = (c.label (cyclicSucc i)).1 := by
    obtain ⟨x, _, hx⟩ := c.right_mem i
    exact (congrArg Prod.fst hx).symm
  let owner : Fin c.length → I := fun i => (c.label i).1
  have hStep (i : Fin c.length) : owner i = owner (cyclicSucc i) :=
    (hLeftTag i).symm.trans (hRightTag i)
  let zero : Fin c.length := ⟨0, by have := c.hlength; omega⟩
  have hAll (i : Fin c.length) : owner i = owner (cyclicSucc zero) := by
    by_cases hi : i = zero
    · subst i
      exact hStep zero
    · exact cyclicOwner_eq_off_singleton c.hlength owner zero
        (fun j _ _ => hStep j) i hi
  have hLabelTag (i j : Fin c.length) : (c.label i).1 = (c.label j).1 :=
    (hAll i).trans (hAll j).symm
  let projected : LabelledBergeCycle H := {
    length := c.length
    hlength := c.hlength
    label := fun i => (c.label i).2
    vertex := fun i => (c.vertex i).2
    label_injective := by
      intro i j hij
      exact c.label_injective (Prod.ext (hLabelTag i j) hij)
    vertex_injective := by
      intro i j hij
      exact c.vertex_injective (Prod.ext
        ((hLeftTag i).trans ((hLabelTag i j).trans (hLeftTag j).symm)) hij)
    left_mem := by
      intro i
      obtain ⟨x, hx, heq⟩ := c.left_mem i
      exact (congrArg Prod.snd heq) ▸ hx
    right_mem := by
      intro i
      obtain ⟨x, hx, heq⟩ := c.right_mem i
      exact (congrArg Prod.snd heq) ▸ hx
  }
  exact h ⟨projected, hc⟩

end Labelled

namespace TrainRecursiveWitness

variable {L : RelLanguage.{u}} {UA VB P I : Type v}

/-- The natural target bound at a proper cut supplies that exact labelled
cut bound in the actual initial picture. -/
theorem initialTrain_labelledCutGirth
    (A : RelStructure L UA) (hA : A.Irreducible) [Nonempty UA]
    (B : RelStructure L VB) (β : I → VB ↪ P) [Nonempty I]
    {m : ℕ} (T : EdgeTrainLevels (OldACarrierEdge A B) m) (hm : 0 < m)
    (μ : Fin (m + 1)) (hμ : μ.val < m) (q : ℕ)
    (hTarget : LabelledGirthGT (T.wagonClassCarrier (fun edge => edge.1) μ) q) :
    LabelledGirthGT
      ((initialTrain A hA B β T hm).wagonClassCarrier (fun edge => edge.1) μ) q := by
  let H := T.wagonClassCarrier (fun edge => edge.1) μ
  let tagged := fun p : I × Quotient (T.wagonSetoid μ) =>
    (fun x : VB => (p.1, x)) '' H p.2
  have hTagged : LabelledGirthGT tagged q := labelledGirthGT_tagged H I q hTarget
  have hCarriers :
      (initialTrain A hA B β T hm).wagonClassCarrier (fun edge => edge.1) μ =
        fun p => tagged (initialWagonCoordinates A hA B β T hm μ hμ p) := by
    funext p
    exact initialWagonCoordinates_carrier A hA B β T hm μ hμ p
  rw [hCarriers]
  exact labelledGirthGT_of_injective_reindex tagged
    (initialWagonCoordinates A hA B β T hm μ hμ)
    (initialWagonCoordinates_injective A hA B β T hm μ hμ) q hTagged

end TrainRecursiveWitness

section Actual

variable {L : RelLanguage.{u}} {UA VB P X : Type v}
variable (A : RelStructure L UA) (B : RelStructure L VB)
variable (D : RelStructure L P) (C : StructuralRamsey.Partite.System L P X)
variable (family : Set (RelStructure.Embedding B D))
variable (selected : Set (DesignatedCopy B D C family))
variable {m : ℕ} (T : EdgeTrainLevels (OldACarrierEdge A C.toRelStructure) m)
variable (μ : Fin (m + 1))

local notation "O" => selectedPictureOrderOneData A B D C family selected T μ

/-- The incidence model uses the complete quotient wagon carrier. -/
theorem selectedPicture_wagonVertex_iff
    (p : Quotient (T.wagonSetoid μ)) (x : X) :
    (O).WagonVertex p x ↔ x ∈ T.wagonClassCarrier (fun edge => edge.1) μ p := by
  induction p using Quotient.inductionOn with
  | h edge =>
      constructor
      · rintro ⟨f, hf, hx⟩
        exact ⟨f, (T.equivalent μ).symm (Quotient.exact hf), hx⟩
      · rintro ⟨f, hf, hx⟩
        exact ⟨f, Quotient.sound ((T.equivalent μ).symm hf), hx⟩

/-- Actual physical edge linearity and the natural labelled cut bound
supply both parts of the circulation pretrain-linearity predicate. -/
theorem selectedPicture_linearPretrain_of_labelledCutGirth
    (hLinear : ALinear A C.toRelStructure)
    {q : ℕ} (hq : 2 ≤ q)
    (hCut : LabelledGirthGT (T.wagonClassCarrier (fun edge => edge.1) μ) q) :
    (O).LinearPretrain := by
  constructor
  · intro edge edge' hne
    obtain ⟨a, ha⟩ := edge.2
    obtain ⟨b, hb⟩ := edge'.2
    have hCopies : ¬ SameCopy a b := by
      intro h
      apply hne
      exact Subtype.ext (ha.trans (h.trans hb.symm))
    change (edge.1 ∩ edge'.1).Subsingleton
    rw [ha, hb]
    exact hLinear a b hCopies
  · intro p q hpq x hx y hy
    have hPair := labelledGirthGT_two_pairwise_subsingleton
      (labelledGirthGT_mono hCut hq) p q hpq
    exact hPair
      ⟨(selectedPicture_wagonVertex_iff A B D C family selected T μ p x).mp hx.1,
        (selectedPicture_wagonVertex_iff A B D C family selected T μ q x).mp hx.2⟩
      ⟨(selectedPicture_wagonVertex_iff A B D C family selected T μ p y).mp hy.1,
        (selectedPicture_wagonVertex_iff A B D C family selected T μ q y).mp hy.2⟩

end Actual
end StructuralRamsey.Girth
