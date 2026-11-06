import Girth.TrainRecursiveTrueActiveTailCutGirth

set_option autoImplicit false
set_option Elab.async false

/-!
# The first retained cut of the genuine active recursive target

For a nonempty nondecreasing cutoff vector, the old level-one cut
already has the numerical girth required by the first-wagon refinement.

* If the old vector has a tail, its index-one tailGirth certificate
  gives the FULL old level-one labelled cut.  Honest restriction to
  the active induced A-support transports this exact statement.
* If the vector has length one, old level one is the universal top.
  Its quotient has only one label, hence arbitrary labelled girth.

This is a genuinely global retained-cut statement.  It uses neither
bottomForest as a fictitious labelled-cut certificate nor an assumption
that Hales--Jewett powers have high girth.  It does not build the
lower recursive witness or its output SupremeCycleBound.
-/

namespace StructuralRamsey.Girth

universe v
variable {E W : Type v}

/-- At the universal top train level there is only one quotient wagon
label, so no labelled Berge cycle of length at least two is possible. -/
theorem EdgeTrainLevels.top_labelledCutGirth
    {m : ℕ} (T : EdgeTrainLevels E m) (edge : E → Set W) (q : ℕ) :
    LabelledGirthGT
      (T.wagonClassCarrier edge
        (⟨m, Nat.lt_succ_self m⟩ : Fin (m + 1))) q := by
  have hSingle :
      ∀ a b : Quotient
          (T.wagonSetoid (⟨m, Nat.lt_succ_self m⟩ : Fin (m + 1))),
        a = b := by
    intro a b
    induction a using Quotient.inductionOn with
    | h a =>
      induction b using Quotient.inductionOn with
      | h b =>
        exact Quotient.sound (T.top a b)
  rintro ⟨C, _⟩
  let i : Fin C.length := ⟨0, by have := C.hlength; omega⟩
  let j : Fin C.length := ⟨1, by have := C.hlength; omega⟩
  have hij : i = j := C.label_injective (hSingle (C.label i) (C.label j))
  have hval := congrArg Fin.val hij
  change (0 : ℕ) = 1 at hval
  omega

end StructuralRamsey.Girth

namespace StructuralRamsey.Girth.TrainRecursiveWitness

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}} {UA VB P : Type v}

/-- The head cutoff of an admissible vector is bounded by every entry.
This is the only numerical input in the retained first-cut proof. -/
theorem Admissible.headD_le_get
    {t : List ℕ} (ht : Admissible t) (j : Fin t.length) :
    t.headD 0 ≤ t.get j := by
  cases t with
  | nil =>
    exact (ht.nonempty rfl).elim
  | cons q tail =>
    change q ≤ (q :: tail).get j
    have hmem : (q :: tail).get j ∈ q :: tail :=
      List.get_mem (q :: tail) j
    rcases List.mem_cons.mp hmem with heq | htail
    · omega
    · exact (List.pairwise_cons.mp ht.nondecreasing).1 _ htail

variable {A : RelStructure L UA} {B : RelStructure L VB}
variable {D : RelStructure L P}
variable {family : Set (Embedding B D)} {t : List ℕ}
variable {targetTrain : EdgeTrainLevels (OldACarrierEdge A B) t.length}
variable {allowed : Fin (t.length + 1) → Set P}

/-- The complete old first positive wagon cut of the TRUE active induced
source has labelled girth at least the old head cutoff.  In the
one-level case this is the universal top; otherwise it follows from
the literal index-one tail invariant (not from bottomForest). -/
theorem ForestTailStage.trueActive_inducedFirstCutGirth
    (stage : ForestTailStage A B D family t targetTrain allowed)
    (e : Embedding A D) (ht : Admissible t) :
    LabelledGirthGT
      (((stage.train.restrict
          (sharedOldACarrierInclusion A stage.system.toRelStructure
            (activeCarrier A stage.system e.toFunctionEmbedding))).restrict
          (inducedACarrierToShared A stage.system.toRelStructure
            (activeCarrier A stage.system e.toFunctionEmbedding))).wagonClassCarrier
          (fun edge : OldACarrierEdge A
            (stage.system.toRelStructure.induce
              (activeCarrier A stage.system e.toFunctionEmbedding)) => edge.1)
          (⟨1, by
            have hpos : 0 < t.length := List.length_pos_iff.mpr ht.nonempty
            omega⟩ : Fin (t.length + 1))) (t.headD 0) := by
  let S := activeCarrier A stage.system e.toFunctionEmbedding
  let Tactive :=
    (stage.train.restrict
      (sharedOldACarrierInclusion A stage.system.toRelStructure S)).restrict
      (inducedACarrierToShared A stage.system.toRelStructure S)
  have hpos : 0 < t.length := List.length_pos_iff.mpr ht.nonempty
  change LabelledGirthGT
    (Tactive.wagonClassCarrier
      (fun edge : OldACarrierEdge A (stage.system.toRelStructure.induce S) => edge.1)
      (⟨1, by omega⟩ : Fin (t.length + 1))) (t.headD 0)
  by_cases hone : t.length = 1
  · have hTop :
        (⟨1, by omega⟩ : Fin (t.length + 1)) =
          ⟨t.length, Nat.lt_succ_self t.length⟩ := by
      apply Fin.ext
      omega
    rw [hTop]
    exact Tactive.top_labelledCutGirth
      (fun edge : OldACarrierEdge A (stage.system.toRelStructure.induce S) =>
        edge.1) (t.headD 0)
  · have htwo : 1 < t.length := by omega
    let j : Fin t.length := ⟨1, htwo⟩
    have hOld :
        LabelledGirthGT
          (Tactive.wagonClassCarrier
            (fun edge : OldACarrierEdge A
              (stage.system.toRelStructure.induce S) => edge.1)
            (⟨1, by omega⟩ : Fin (t.length + 1))) (t.get j) := by
      simpa [Tactive, S, j] using
        (stage.trueActive_inducedTailCutGirth e j (by change 0 < 1; omega))
    exact labelledGirthGT_mono hOld (ht.headD_le_get j)

end StructuralRamsey.Girth.TrainRecursiveWitness
