import Girth.TrainRecursiveUniformAllInputs
import Girth.TrainRecursiveOneEdgeDichotomy

set_option autoImplicit false
set_option Elab.async false

/-!
# The genuinely unrestricted order input needed at cutoff two

The shorter train in the manuscript is of a NEW coloured edge type X
(possibly with repeated coarse vertex predicates). It is not generally
X-partite: different X coordinates on two first-wagon edges can be
identified at an original common vertex.

Hence UniformSelectedPartiteOrderAllInputs, despite its correct type
and palette quantifiers, is insufficient as the RR_tail input.

The order assertion below quantifies over an ARBITRARY finite ordered
target train B without any B.IsPartiteOver A premise. Its output
may be partite over a NEW large base D, which supports a prescribed
family of embeddings B to D. This is the ordinary Ramsey picture setup;
the invalid identity-only base is restricted to the verified one-copy case.

This corrects the type of the order field in the abstract rank
operators. Nothing here proves the general forest-to-order transfer
or the cutoff-two filling step. The still-needed theorems remain
explicit inputs to the conditional operators.
-/

namespace StructuralRamsey.Girth.TrainRecursiveWitness

open StructuralRamsey.RelStructure

universe u v w
variable {UA VB : Type v}

/-- An unrestricted selected order-Ramsey assertion at a given vector,
for every finite ordered edge type, arbitrary finite ordered target
and finite nonempty palette. No global A-part map on the target B is
present in the input.

The output is a finite, potentially larger base D with genuine prescribed
B-embeddings and an actual selected OrderStage. Fixing the base to B
with only its identity embedding is impossible for a multi-copy target:
a two-colouring by projected B-coordinate prevents homogeneity. -/
/-- Genuine unrestricted selected order output: the Ramsey base D and its
prescribed B-embedding family are CHOSEN, not fixed to the identity copy.
Each output allowed-part set restricts inside every prescribed B-image to
the corresponding original allowed set. -/
def UnrestrictedSelectedOrderWitness
    {L : RelLanguage.{u}}
    (A : RelStructure L UA) (B : RelStructure L VB)
    (t : List ℕ)
    (targetTrain : EdgeTrainLevels (OldACarrierEdge A B) t.length)
    (allowed : Fin (t.length + 1) → Set VB)
    (κ : Type w) : Prop :=
  ∃ (W : Type v) (_ : Finite W)
      (D : RelStructure L W)
      (family : Set (Embedding B D))
      (allowedD : Fin (t.length + 1) → Set W),
    (∀ b : Embedding B D, b ∈ family →
      ∀ ν : Fin (t.length + 1),
        b ⁻¹' allowedD ν ⊆ allowed ν) ∧
    ∃ S : OrderStage A B D family t targetTrain allowedD,
      DesignatedArrow S.toForestTailStage κ

/-- No fixed identity-base picture can force monochromaticity of two
A-subcopies whose values disagree at even one vertex. This proves why
a larger Ramsey base is essential for unrestricted targets. -/
theorem no_identityBase_designatedArrow_of_distinct_A_values
    {L : RelLanguage.{u}}
    (A : RelStructure L UA) (B : RelStructure L VB)
    {t : List ℕ}
    {targetTrain : EdgeTrainLevels (OldACarrierEdge A B) t.length}
    {allowed : Fin (t.length + 1) → Set VB}
    (S : ForestTailStage A B B {Embedding.id B} t targetTrain allowed)
    (a₁ a₂ : Embedding A B) (u : UA)
    (hDifferent : a₁ u ≠ a₂ u) :
    ¬ DesignatedArrow S Bool := by
  classical
  intro hArrow
  let χ : Embedding A S.system.toRelStructure → Bool :=
    fun f => decide (S.system.part (f u) = a₁ u)
  obtain ⟨b, _hb, hMono⟩ := hArrow χ
  have hBase : b.base = Embedding.id B := by
    simpa only [Set.mem_singleton_iff] using b.base_mem
  have hPart (a : Embedding A B) :
      S.system.part ((b.embedding.comp a) u) = a u := by
    change S.system.part (b.embedding (a u)) = a u
    rw [b.projects (a u), hBase]
    rfl
  have hColour₁ : χ (b.embedding.comp a₁) = true := by
    change decide (S.system.part ((b.embedding.comp a₁) u) = a₁ u) = true
    rw [hPart a₁]
    simp
  have hColour₂ : χ (b.embedding.comp a₂) = false := by
    change decide (S.system.part ((b.embedding.comp a₂) u) = a₁ u) = false
    rw [hPart a₂]
    simp [hDifferent.symm]
  have hEq := hMono a₁ a₂
  rw [hColour₁, hColour₂] at hEq
  cases hEq

/-- The obstruction is automatic for every genuinely nontrivial
target: two physical A-copies cannot be given an identity-only selected
Ramsey witness, even with just two colours. -/
theorem no_identityBase_designatedArrow_of_two_copies
    {L : RelLanguage.{u}}
    (A : RelStructure L UA) (B : RelStructure L VB)
    {t : List ℕ}
    {targetTrain : EdgeTrainLevels (OldACarrierEdge A B) t.length}
    {allowed : Fin (t.length + 1) → Set VB}
    (S : ForestTailStage A B B {Embedding.id B} t targetTrain allowed)
    (hTwo : ∃ a b : Embedding A B, ¬ SameCopy a b) :
    ¬ DesignatedArrow S Bool := by
  obtain ⟨a, b, hNotSame⟩ := hTwo
  have hDifferent : ∃ u : UA, a u ≠ b u := by
    by_contra hNo
    apply hNotSame
    have hEq : a = b := by
      apply Embedding.ext
      intro u
      by_contra hu
      exact hNo ⟨u, hu⟩
    subst b
    rfl
  obtain ⟨u, hu⟩ := hDifferent
  exact no_identityBase_designatedArrow_of_distinct_A_values
    S a b u hu

/-- Arbitrary finite target B: unlike the invalid identity-base proposal,
the conclusion allows a sufficiently large finite base D and a real
prescribed family of B-embeddings. No global A-part map on B is required. -/
def UniformSelectedUnrestrictedOrderAllInputs
    (L : RelLanguage.{u}) (t : List ℕ) : Prop :=
  ∀ {UA : Type v} [LinearOrder UA] [Finite UA] [Nonempty UA]
    (A₀ : RelStructure L UA)
    (κ : Type) [Fintype κ] [Nonempty κ]
    {VB : Type v} [Finite VB]
    (B : RelStructure L.withOrder VB)
    (ht : Admissible t)
    (targetTrain : EdgeTrainLevels
      (OldACarrierEdge A₀.ordered B) t.length)
    (allowed : Fin (t.length + 1) → Set VB)
    (hSupportNonempty : Nonempty
      (OldACarrierEdge A₀.ordered B))
    (hSupportCovers : ∀ x : VB,
      ∃ a : OldACarrierEdge A₀.ordered B, x ∈ a.1)
    (hGirth : GirthGT
      (supportCopies A₀.ordered B) (t.headD 0))
    (hParameters : targetTrain.AdjacentParameters
      (fun e => e.1) allowed)
    (hTargetCuts : ∀ j : Fin t.length, 0 < j.val →
      LabelledGirthGT
        (targetTrain.wagonClassCarrier (fun e => e.1) j.castSucc)
        (t.get j)),
    UnrestrictedSelectedOrderWitness A₀.ordered B t
      targetTrain allowed κ

/-- The already checked one-physical-edge result really is a member
of this NONPARTITE order domain: no B-to-A part map is assumed and
the conclusion uses the actual original train and base B. -/
theorem unrestrictedOrder_oneEdge_case
    {L : RelLanguage.{u}}
    (A₀ : RelStructure L UA) [LinearOrder UA] [Finite UA]
    [Nonempty UA]
    (B : RelStructure L.withOrder VB) [Finite VB]
    (t : List ℕ) (ht : Admissible t)
    (targetTrain : EdgeTrainLevels
      (OldACarrierEdge A₀.ordered B) t.length)
    (allowed : Fin (t.length + 1) → Set VB)
    (hSupportNonempty : Nonempty (OldACarrierEdge A₀.ordered B))
    (hSupportCovers : ∀ x : VB,
      ∃ a : OldACarrierEdge A₀.ordered B, x ∈ a.1)
    (κ : Type w)
    (hNoTwo : ¬ ∃ a b : Embedding A₀.ordered B,
      ¬ SameCopy a b) :
    ∃ S : OrderStage A₀.ordered B B
        {Embedding.id B} t targetTrain allowed,
      DesignatedArrow S.toForestTailStage κ :=
  exists_orderStage_of_no_two_copies
    A₀ B t ht targetTrain allowed
    hSupportNonempty hSupportCovers κ hNoTwo

/-- Specialize the genuinely UNRESTRICTED shorter-train order assertion
to the new finite edge type and the r^n-colour palette required by
canonical cutoff-two filling. The target B is arbitrary: no fine
part map B → A is introduced or assumed. -/
/-- A genuine one-copy order witness inhabits the existential-base
unrestricted interface by choosing D=B, the singleton identity family,
and unchanged allowed-part sets. -/
theorem unrestrictedOrder_oneEdge_case_general
    {L : RelLanguage.{u}}
    (A₀ : RelStructure L UA) [LinearOrder UA] [Finite UA]
    [Nonempty UA]
    (B : RelStructure L.withOrder VB) [Finite VB]
    (t : List ℕ) (ht : Admissible t)
    (targetTrain : EdgeTrainLevels
      (OldACarrierEdge A₀.ordered B) t.length)
    (allowed : Fin (t.length + 1) → Set VB)
    (hSupportNonempty : Nonempty (OldACarrierEdge A₀.ordered B))
    (hSupportCovers : ∀ x : VB,
      ∃ a : OldACarrierEdge A₀.ordered B, x ∈ a.1)
    (κ : Type w)
    (hNoTwo : ¬ ∃ a b : Embedding A₀.ordered B,
      ¬ SameCopy a b) :
    UnrestrictedSelectedOrderWitness A₀.ordered B t
      targetTrain allowed κ := by
  obtain ⟨S, hArrow⟩ := unrestrictedOrder_oneEdge_case
    A₀ B t ht targetTrain allowed hSupportNonempty
    hSupportCovers κ hNoTwo
  refine ⟨VB, inferInstance, B, {Embedding.id B}, allowed, ?_,
    S, hArrow⟩
  intro b hb ν x hx
  have hId : b = Embedding.id B := by
    simpa only [Set.mem_singleton_iff] using hb
  subst b
  simpa using hx

/-- The smaller-rank unrestricted order assertion applies to a NEW
finite edge structure and a finite power palette, without imposing
an A-partite structure on the arbitrary shorter target B. -/
theorem UniformSelectedUnrestrictedOrderAllInputs.finPower
    (L : RelLanguage.{u}) (t : List ℕ)
    (h : UniformSelectedUnrestrictedOrderAllInputs.{u, v} L t)
    (A₀ : RelStructure L UA)
    [LinearOrder UA] [Finite UA] [Nonempty UA]
    (B : RelStructure L.withOrder VB) [Finite VB]
    (ht : Admissible t)
    (targetTrain : EdgeTrainLevels
      (OldACarrierEdge A₀.ordered B) t.length)
    (allowed : Fin (t.length + 1) → Set VB)
    (hSupportNonempty : Nonempty
      (OldACarrierEdge A₀.ordered B))
    (hSupportCovers : ∀ x : VB,
      ∃ a : OldACarrierEdge A₀.ordered B, x ∈ a.1)
    (hGirth : GirthGT
      (supportCopies A₀.ordered B) (t.headD 0))
    (hParameters : targetTrain.AdjacentParameters
      (fun e => e.1) allowed)
    (hTargetCuts : ∀ j : Fin t.length, 0 < j.val →
      LabelledGirthGT
        (targetTrain.wagonClassCarrier (fun e => e.1) j.castSucc)
        (t.get j))
    (r n : ℕ) (hr : 0 < r) :
    UnrestrictedSelectedOrderWitness A₀.ordered B t targetTrain
      allowed (Fin (r ^ n)) := by
  letI : Nonempty (Fin (r ^ n)) := ⟨⟨0, pow_pos hr n⟩⟩
  exact h A₀ (Fin (r ^ n)) B ht targetTrain allowed
    hSupportNonempty hSupportCovers hGirth hParameters hTargetCuts

/-- Correct mixed operator contract: the q>2 partite forest step is
already proved, but SAME-VECTOR forest-to-order must produce an
UNRESTRICTED order witness before cutoff two can consume it.
The two fields are mathematical obligations, not instance fields
filled by a partite-only order theorem. -/
def uniformSelectedUnrestrictedOperators
    (L : RelLanguage.{u})
    (baseTwo : UniformSelectedPartiteForestAllInputs.{u, v} L [2])
    (forestToUnrestrictedOrder : ∀ t, Admissible t →
      UniformSelectedPartiteForestAllInputs.{u, v} L t →
      UniformSelectedUnrestrictedOrderAllInputs.{u, v} L t)
    (cutoffTwo : ∀ tail, Admissible tail →
      UniformSelectedUnrestrictedOrderAllInputs.{u, v} L tail →
      UniformSelectedPartiteForestAllInputs.{u, v} L (2 :: tail)) :
    Operators
      (UniformSelectedPartiteForestAllInputs.{u, v} L)
      (UniformSelectedUnrestrictedOrderAllInputs.{u, v} L) where
  baseTwo := baseTwo
  forestToOrder := forestToUnrestrictedOrder
  cutoffTwo := cutoffTwo
  largerCutoff := by
    intro q tail _ hq hAllLower
    exact uniformSelectedPartiteForestAllInputs_largerCutoff
      L q tail hq hAllLower

/-- Full rank assembly, CONDITIONAL on the three genuine unproved
operators. In particular no partite-order statement is substituted
for the arbitrary shorter-train RR_tail premise. -/
theorem uniformSelectedPartiteForest_of_correctOrderOperators
    (L : RelLanguage.{u})
    (baseTwo : UniformSelectedPartiteForestAllInputs.{u, v} L [2])
    (forestToUnrestrictedOrder : ∀ t, Admissible t →
      UniformSelectedPartiteForestAllInputs.{u, v} L t →
      UniformSelectedUnrestrictedOrderAllInputs.{u, v} L t)
    (cutoffTwo : ∀ tail, Admissible tail →
      UniformSelectedUnrestrictedOrderAllInputs.{u, v} L tail →
      UniformSelectedPartiteForestAllInputs.{u, v} L (2 :: tail))
    (t : List ℕ) (ht : Admissible t) :
    UniformSelectedPartiteForestAllInputs.{u, v} L t :=
  (uniformSelectedUnrestrictedOperators L baseTwo
    forestToUnrestrictedOrder cutoffTwo).assemble t ht

end StructuralRamsey.Girth.TrainRecursiveWitness
