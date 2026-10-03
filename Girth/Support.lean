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

end StructuralRamsey.Girth
