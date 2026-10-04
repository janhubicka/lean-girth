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



/-- Equality of copy carriers reflects back through an ambient embedding. -/
theorem sameCopy_of_comp
    {X : Type v}
    {A : RelStructure L U} {D : RelStructure L W}
    {E : RelStructure L X}
    (i : Embedding D E)
    {e f : Embedding A D}
    (h : SameCopy (i.comp e) (i.comp f)) :
    SameCopy e f := by
  change Set.range e = Set.range f
  apply Set.Subset.antisymm
  · rintro x ⟨a, rfl⟩
    have hx : i (e a) ∈ copyCarrier (i.comp f) := by
      change copyCarrier (i.comp e) = copyCarrier (i.comp f) at h
      rw [← h]
      exact ⟨a, rfl⟩
    rcases hx with ⟨b, hb⟩
    refine ⟨b, ?_⟩
    apply i.injective
    exact hb
  · rintro x ⟨a, rfl⟩
    have hx : i (f a) ∈ copyCarrier (i.comp e) := by
      change copyCarrier (i.comp e) = copyCarrier (i.comp f) at h
      rw [h]
      exact ⟨a, rfl⟩
    rcases hx with ⟨b, hb⟩
    refine ⟨b, ?_⟩
    apply i.injective
    exact hb

/-- A-linearity is hereditary under induced substructures. -/
theorem aLinear_induce
    {A : RelStructure L U} {D : RelStructure L W}
    (hD : ALinear A D) (S : Set W) :
    ALinear A (D.induce S) := by
  let incl : Embedding (D.induce S) D :=
    RelStructure.inclusion D S
  intro e f hne
  have hne' :
      ¬ SameCopy (incl.comp e) (incl.comp f) := by
    intro h
    exact hne (sameCopy_of_comp incl h)
  have hsmall := hD (incl.comp e) (incl.comp f) hne'
  intro x hx y hy
  apply Subtype.ext
  apply hsmall
  · rcases hx.1 with ⟨a, ha⟩
    rcases hx.2 with ⟨b, hb⟩
    constructor
    · refine ⟨a, ?_⟩
      exact congrArg Subtype.val ha
    · refine ⟨b, ?_⟩
      exact congrArg Subtype.val hb
  · rcases hy.1 with ⟨a, ha⟩
    rcases hy.2 with ⟨b, hb⟩
    constructor
    · refine ⟨a, ?_⟩
      exact congrArg Subtype.val ha
    · refine ⟨b, ?_⟩
      exact congrArg Subtype.val hb
end StructuralRamsey.Girth
