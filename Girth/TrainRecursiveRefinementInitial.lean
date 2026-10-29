import Girth.TrainRecursiveRefinement
import Girth.TrainRecursiveWitnessInitial
import Girth.ActivePicture

/-!
# Initial refinements on the complete active physical support

For finite nonempty irreducible A, every actual A-edge contained in an
initial active carrier is the physical carrier of a projected fibre copy.
Irreducibility places it in one initial component.  The injective component
projection gives one active copy in that component, and finite containment
between A-copies gives equality of carriers.  Thus the complete physical
support of the active subsystem is a matching, not merely the selected
projected edge subfamily.

The actual restricted train therefore has a first-wagon refinement of any
prescribed finite positive depth, with empty permitted-part sets and any
finite labelled child-girth bound.  All higher train levels and all active
physical edges are retained.  No preservation under attachment is claimed.
-/

namespace StructuralRamsey.Girth.TrainRecursiveWitness

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}} {UA VB P I X : Type v}

/-- Any actual A-copy carried by an initial active subsystem has the same
physical carrier as a projected fibre copy.  No rigidity or orderedness
hypothesis is needed: only physical carriers, rather than embeddings, are
identified here. -/
theorem initialActiveACopy_has_projectedCarrier
    (A : RelStructure L UA) (hA : A.Irreducible) [Finite UA] [Nonempty UA]
    (B : RelStructure L VB) (β : I → VB ↪ P) [Nonempty I]
    (α : UA ↪ P)
    (a : Embedding A (StructuralRamsey.Partite.Initial.picture B β).toRelStructure)
    (hActive : ∀ u : UA, a u ∈ activeCarrier A
      (StructuralRamsey.Partite.Initial.picture B β) α) :
    ∃ e : StructuralRamsey.Partite.ProjectedEmbedding A
      (StructuralRamsey.Partite.Initial.picture B β) α, SameCopy a e.val := by
  obtain ⟨i, a₀, rfl⟩ := initialACopy_factors_component A hA B β a
  obtain ⟨u₀⟩ := (inferInstance : Nonempty UA)
  obtain ⟨e, v₀, hev⟩ := hActive u₀
  obtain ⟨j, b, he⟩ := initialACopy_factors_component A hA B β e.val
  have hji : j = i := by
    rw [he] at hev
    exact congrArg Prod.fst hev
  subst j
  refine ⟨e, sameCopy_of_range_subset _ _ ?_⟩
  intro u
  obtain ⟨f, v, hfv⟩ := hActive u
  obtain ⟨k, c, hf⟩ := initialACopy_factors_component A hA B β f.val
  have hki : k = i := by
    rw [hf] at hfv
    exact congrArg Prod.fst hfv
  subst k
  have hef : e = f := by
    apply Subtype.ext
    apply RelStructure.Embedding.ext
    intro w
    have hp := (e.property w).trans (f.property w).symm
    rw [he, hf] at hp
    rw [he, hf]
    exact Prod.ext rfl ((β i).injective hp)
  rw [← hef] at hfv
  exact ⟨v, hfv.symm⟩

/-- Every contained physical edge is represented, with no edge pruning. -/
theorem initialActiveEdge_has_projectedCarrier
    (A : RelStructure L UA) (hA : A.Irreducible) [Finite UA] [Nonempty UA]
    (B : RelStructure L VB) (β : I → VB ↪ P) [Nonempty I]
    (α : UA ↪ P)
    (e : SharedOldACarrierEdge A
      (StructuralRamsey.Partite.Initial.picture B β).toRelStructure
      (activeCarrier A (StructuralRamsey.Partite.Initial.picture B β) α)) :
    ∃ a : StructuralRamsey.Partite.ProjectedEmbedding A
      (StructuralRamsey.Partite.Initial.picture B β) α,
      e.val.val = copyCarrier a.val := by
  obtain ⟨a, ha⟩ := e.val.property
  obtain ⟨b, hb⟩ := initialActiveACopy_has_projectedCarrier A hA B β α a (by
    intro u
    apply e.property
    rw [ha]
    exact ⟨u, rfl⟩)
  exact ⟨b, ha.trans hb⟩

/-- The full physical A-support in each initial active carrier is a
matching.  This includes every actual A-edge contained in that carrier. -/
theorem initialActiveEdges_pairwiseDisjoint
    (A : RelStructure L UA) (hA : A.Irreducible) [Finite UA] [Nonempty UA]
    (B : RelStructure L VB) (β : I → VB ↪ P) [Nonempty I]
    (α : UA ↪ P)
    ⦃e f : SharedOldACarrierEdge A
      (StructuralRamsey.Partite.Initial.picture B β).toRelStructure
      (activeCarrier A (StructuralRamsey.Partite.Initial.picture B β) α)⦄
    (hne : e ≠ f) : Disjoint e.val.val f.val.val := by
  obtain ⟨a, ha⟩ := initialActiveEdge_has_projectedCarrier A hA B β α e
  obtain ⟨b, hb⟩ := initialActiveEdge_has_projectedCarrier A hA B β α f
  rw [ha, hb]
  apply initialFibre_pairwiseDisjoint A hA B β α a b
  intro hab
  apply hne
  apply Subtype.ext
  apply Subtype.ext
  exact ha.trans ((congrArg (fun c => copyCarrier c.val) hab).trans hb.symm)

/-- The full train on the active physical support inherits a concrete
refinement.  `d` counts extra equality cuts, so the positive refinement
depth is `d + 1`.  The conclusion is actual data, not a refinability premise.
-/
noncomputable def initialActiveFirstWagonRefinement
    (A : RelStructure L UA) (hA : A.Irreducible) [Finite UA] [Nonempty UA]
    (B : RelStructure L VB) (β : I → VB ↪ P) [Nonempty I]
    {m : ℕ}
    (T : EdgeTrainLevels (OldACarrierEdge A
      (StructuralRamsey.Partite.Initial.picture B β).toRelStructure) m)
    (hm : 0 < m) (α : UA ↪ P) (firstAllowed : Set P) (q d : ℕ) :
    FirstWagonRefinement
      (T.restrict (sharedOldACarrierInclusion A
        (StructuralRamsey.Partite.Initial.picture B β).toRelStructure
        (activeCarrier A (StructuralRamsey.Partite.Initial.picture B β) α)))
      hm (fun e => e.val.val)
      (StructuralRamsey.Partite.Initial.picture B β).part firstAllowed q :=
  firstWagonRefinement_of_matching
    (T.restrict (sharedOldACarrierInclusion A
      (StructuralRamsey.Partite.Initial.picture B β).toRelStructure
      (activeCarrier A (StructuralRamsey.Partite.Initial.picture B β) α)))
    hm (fun e => e.val.val)
    (initialActiveEdges_pairwiseDisjoint A hA B β α)
    (StructuralRamsey.Partite.Initial.picture B β).part firstAllowed q d

/-- Refinability of the actual active physical train for one profile. -/
def ActiveFirstRefinable
    (A : RelStructure L UA) (C : StructuralRamsey.Partite.System L P X)
    {m : ℕ} (T : EdgeTrainLevels (OldACarrierEdge A C.toRelStructure) m)
    (hm : 0 < m) (firstAllowed : Set P) (q : ℕ) (α : UA ↪ P) : Prop :=
  Nonempty (FirstWagonRefinement
    (T.restrict (sharedOldACarrierInclusion A C.toRelStructure
      (activeCarrier A C α))) hm (fun e => e.val.val) C.part firstAllowed q)

/-- Remaining-profile readiness records the manuscript's actual finite
first-wagon refinements on all remaining active physical supports. -/
def RemainingFirstRefinable
    (A : RelStructure L UA) (C : StructuralRamsey.Partite.System L P X)
    {m : ℕ} (T : EdgeTrainLevels (OldACarrierEdge A C.toRelStructure) m)
    (hm : 0 < m) (firstAllowed : Set P) (q : ℕ) (profiles : List (UA ↪ P)) : Prop :=
  ∀ α ∈ profiles, ActiveFirstRefinable A C T hm firstAllowed q α

/-- Initial readiness is constructed for every finite list of profiles.
There is no dependence on a supplied readiness proof or local operator. -/
theorem initial_remainingFirstRefinable
    (A : RelStructure L UA) (hA : A.Irreducible) [Finite UA] [Nonempty UA]
    (B : RelStructure L VB) (β : I → VB ↪ P) [Nonempty I]
    {m : ℕ}
    (T : EdgeTrainLevels (OldACarrierEdge A
      (StructuralRamsey.Partite.Initial.picture B β).toRelStructure) m)
    (hm : 0 < m) (firstAllowed : Set P) (q : ℕ) (profiles : List (UA ↪ P)) :
    RemainingFirstRefinable A (StructuralRamsey.Partite.Initial.picture B β)
      T hm firstAllowed q profiles := by
  intro α hα
  exact ⟨initialActiveFirstWagonRefinement A hA B β T hm α firstAllowed q 0⟩

/-- Dropping a processed or absent profile preserves this concrete
remaining-profile invariant without changing any edge or train relation. -/
theorem RemainingFirstRefinable.tail
    {A : RelStructure L UA} {C : StructuralRamsey.Partite.System L P X}
    {m : ℕ} {T : EdgeTrainLevels (OldACarrierEdge A C.toRelStructure) m}
    {hm : 0 < m} {firstAllowed : Set P} {q : ℕ}
    {α : UA ↪ P} {profiles : List (UA ↪ P)}
    (h : RemainingFirstRefinable A C T hm firstAllowed q (α :: profiles)) :
    RemainingFirstRefinable A C T hm firstAllowed q profiles := by
  intro β hβ
  exact h β (List.mem_cons_of_mem α hβ)

end StructuralRamsey.Girth.TrainRecursiveWitness
