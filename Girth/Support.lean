import PartiteConstruction

/-! # Support copies and strong inducedness

The manuscript measures girth in the hypergraph of image copies of a fixed
structure `A`.  We keep image carriers explicit rather than quotienting
embeddings by automorphisms; for the ordered structures in the paper the two
views coincide because the structures are rigid.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {U V W : Type v}

/-- Carrier of the image copy represented by an embedding. -/
def copyCarrier {A : RelStructure L U} {D : RelStructure L W}
    (e : Embedding A D) : Set W :=
  Set.range e

/-- Two embeddings represent the same image copy. -/
def SameCopy {A : RelStructure L U} {D : RelStructure L W}
    (e f : Embedding A D) : Prop :=
  copyCarrier e = copyCarrier f

/-- The support hypergraph of `A)-copies, represented as their image carriers. -/
def supportCopies (A : RelStructure L U) (D : RelStructure L W) : Set (Set W) :=
  {S | ∃ e : Embedding A D, S = copyCarrier e}

/-- Distinct `A)-copies meet in at most one vertex. -/
def ALinear (A : RelStructure L U) (D : RelStructure L W) : Prop :=
  ∀ e f : Embedding A D,
    ¬ SameCopy e f →
      (copyCarrier e ∩ copyCarrier f).Subsingleton

/-- A vertex set is `A)-strongly induced when every ambient `A)-copy
meeting it in at least two vertices is entirely contained in it. -/
def AStrong (A : RelStructure L U) (D : RelStructure L W) (S : Set W) : Prop :=
  ∀ e : Embedding A D,
    ¬ (copyCarrier e ∩ S).Subsingleton →
      copyCarrier e ⊆ S

theorem aStrong_univ (A : RelStructure L U) (D : RelStructure L W) :
    AStrong A D Set.univ := by
  intro e _ x _
  exact Set.mem_univ x

theorem sameCopy_refl {A : RelStructure L U} {D : RelStructure L W}
    (e : Embedding A D) : SameCopy e e :=
  rfl

/-- For a finite source, containment between two embedded copies forces equality
of their image carriers. -/
theorem sameCopy_of_range_subset
    {A : RelStructure L U} {D : RelStructure L W}
    [Finite U]
    (e f : Embedding A D)
    (h : ∀ a : U, ∃ b : U, e a = f b) :
    SameCopy e f := by
  classical
  let q : Embedding A A := e.factorThroughRange f h
  have hqSpec (a : U) : e a = f (q a) :=
    Classical.choose_spec (h a)
  have hqSurj : Function.Surjective q :=
    Finite.injective_iff_surjective.mp q.injective
  change Set.range e = Set.range f
  apply Set.Subset.antisymm
  · intro x hx
    rcases hx with ⟨a, rfl⟩
    exact ⟨q a, (hqSpec a).symm⟩
  · intro x hx
    rcases hx with ⟨b, rfl⟩
    obtain ⟨a, ha⟩ := hqSurj b
    refine ⟨a, ?_⟩
    simpa [ha] using hqSpec a

end StructuralRamsey.Girth
