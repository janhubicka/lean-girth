import Girth.TrainRecursiveWitnessInitial

/-!
# Adjacent parameters of the actual initial train

Proper-cut wagon carriers in the initial train are exactly tagged target
wagon carriers.  In particular, wagons from different initial components
are disjoint, including when their parent is the universal top.

The resulting parameter theorem assumes the target train's adjacent bounds
with the allowed parts pulled back along each literal base embedding.  It
derives the bounds for the complete actual initial support train.  No
initial-picture parameter conclusion or tail system-girth is an input.
-/

namespace StructuralRamsey.Girth.TrainRecursiveWitness

universe u v
variable {L : RelLanguage.{u}} {UA VB P I : Type v}

/-- Exact relations on possibly different physical initial components. -/
theorem initialTrain_rel_iff
    (A : RelStructure L UA) (hA : A.Irreducible) [Nonempty UA]
    (B : RelStructure L VB) (β : I → VB ↪ P) [Nonempty I]
    {m : ℕ} (T : EdgeTrainLevels (OldACarrierEdge A B) m) (hm : 0 < m)
    (i j : I) (μ : Fin (m + 1)) (e f : OldACarrierEdge A B) :
    (initialTrain A hA B β T hm).rel μ
      (initialPhysicalEdge A B β (i, e))
      (initialPhysicalEdge A B β (j, f)) ↔
      μ.val = m ∨ (i = j ∧ T.rel μ e f) := by
  change (componentTrain T hm).rel μ
    ((initialPhysicalEdgeEquiv A hA B β).symm
      ((initialPhysicalEdgeEquiv A hA B β) (i, e)))
    ((initialPhysicalEdgeEquiv A hA B β).symm
      ((initialPhysicalEdgeEquiv A hA B β) (j, f))) ↔ _
  simp only [Equiv.symm_apply_apply]
  rfl

/-- Every proper-cut initial wagon is the exact image of its target wagon. -/
theorem initialTrain_wagonCarrier
    (A : RelStructure L UA) (hA : A.Irreducible) [Nonempty UA]
    (B : RelStructure L VB) (β : I → VB ↪ P) [Nonempty I]
    {m : ℕ} (T : EdgeTrainLevels (OldACarrierEdge A B) m) (hm : 0 < m)
    (i : I) (μ : Fin (m + 1)) (hμ : μ.val < m)
    (e : OldACarrierEdge A B) :
    (initialTrain A hA B β T hm).wagonCarrier (fun edge => edge.1) μ
      (initialPhysicalEdge A B β (i, e)) =
      (fun b : VB => (i, b)) '' T.wagonCarrier (fun edge => edge.1) μ e := by
  ext x
  constructor
  · rintro ⟨edge, hrel, hx⟩
    obtain ⟨⟨j, f⟩, rfl⟩ := initialPhysicalEdge_surjective A hA B β edge
    rcases (initialTrain_rel_iff A hA B β T hm i j μ e f).mp hrel with
      htop | ⟨hij, htarget⟩
    · exact (Nat.ne_of_lt hμ htop).elim
    · subst j
      obtain ⟨b, hb, hbx⟩ := hx
      exact ⟨b, ⟨f, htarget, hb⟩, hbx⟩
  · rintro ⟨b, ⟨f, hrel, hb⟩, hbx⟩
    exact ⟨initialPhysicalEdge A B β (i, f),
      (initialTrain_rel_iff A hA B β T hm i i μ e f).mpr (Or.inr ⟨rfl, hrel⟩),
      ⟨b, hb, hbx⟩⟩

/-- All adjacent parameter bounds lift from the target to the actual initial
train.  The universal top causes no extra intersection between disjoint
components; inside a component the target bound applies with the same parts.
-/
theorem initialTrain_adjacentParameters
    (A : RelStructure L UA) (hA : A.Irreducible) [Nonempty UA]
    (B : RelStructure L VB) (β : I → VB ↪ P) [Nonempty I]
    {m : ℕ} (T : EdgeTrainLevels (OldACarrierEdge A B) m) (hm : 0 < m)
    (allowed : Fin (m + 1) → Set P)
    (hTarget : ∀ i : I, T.AdjacentParameters (fun edge => edge.1)
      (fun ν => (β i) ⁻¹' allowed ν)) :
    (initialTrain A hA B β T hm).AdjacentParameters (fun edge => edge.1)
      (fun ν => (StructuralRamsey.Partite.Initial.picture B β).part ⁻¹' allowed ν) := by
  intro μ ν hμν hsucc p q
  have hμ : μ.val < m := by
    have hν := ν.isLt
    omega
  induction p using Quotient.inductionOn with
  | h a =>
      induction q using Quotient.inductionOn with
      | h b =>
          intro hne hparent x hx
          obtain ⟨⟨i, e⟩, rfl⟩ := initialPhysicalEdge_surjective A hA B β a
          obtain ⟨⟨j, f⟩, rfl⟩ := initialPhysicalEdge_surjective A hA B β b
          have hx₁ : x ∈ (fun b : VB => (i, b)) ''
              T.wagonCarrier (fun edge => edge.1) μ e := by
            rw [← initialTrain_wagonCarrier A hA B β T hm i μ hμ e]
            exact hx.1
          have hx₂ : x ∈ (fun b : VB => (j, b)) ''
              T.wagonCarrier (fun edge => edge.1) μ f := by
            rw [← initialTrain_wagonCarrier A hA B β T hm j μ hμ f]
            exact hx.2
          obtain ⟨y, hy, rfl⟩ := hx₁
          obtain ⟨z, hz, hzy⟩ := hx₂
          have hij : i = j := (congrArg Prod.fst hzy).symm
          have hzy' : z = y := congrArg Prod.snd hzy
          subst j
          subst z
          have htargetRel : T.rel ν e f := by
            apply (initialTrain_component_iff A hA B β T hm i ν e f).mp
            exact Quotient.exact hparent
          have htargetNe :
              Quotient.mk (T.wagonSetoid μ) e ≠ Quotient.mk (T.wagonSetoid μ) f := by
            intro heq
            apply hne
            apply Quotient.sound
            apply (initialTrain_component_iff A hA B β T hm i μ e f).mpr
            exact Quotient.exact heq
          have htargetParent :
              T.wagonParent μ ν hμν (Quotient.mk (T.wagonSetoid μ) e) =
                T.wagonParent μ ν hμν (Quotient.mk (T.wagonSetoid μ) f) :=
            Quotient.sound htargetRel
          exact hTarget i μ ν hμν hsucc htargetNe htargetParent ⟨hy, hz⟩

end StructuralRamsey.Girth.TrainRecursiveWitness
