import Girth.ACopyRelationalUnion

set_option autoImplicit false

/-!
# The relational free union of a decorated A-copy star

The generated point quotient of ACopyDecoratedStar has exact pairwise source
intersections through the core. This module equips it with the union of the
relational chart tuples.

Only core/source agreement on their genuinely shared tuples is required.
Agreement between two different standards is *derived* from exact point
intersection and core agreement, including nullary relation symbols.

Thus all source point maps are proved to be induced relational embeddings.
The separate problem of establishing core/source agreement from the actual
full induced gluing-link structures remains explicit.
-/

namespace StructuralRamsey.Girth.ACopyDecoratedRelationalStar

open StructuralRamsey.RelStructure
open ACopyLayeredStar ACopyDecoratedStar ACopyRelationalUnion

universe u v

variable {L : RelLanguage.{u}}
variable {CN I K PC : Type v} {SN SH PS PQ : I → Type v}
variable {N : Diagram CN I SN SH}
variable (D : Data N K PC PS PQ)

/-- Quotienting the original source point records adds no extra points to
their image. Unsupported points are included. -/
theorem core_range : Set.range D.coreMap = D.coreImage := by
  ext p
  constructor
  · rintro ⟨q, rfl⟩
    refine Quotient.inductionOn q ?_
    intro x
    exact ⟨x, rfl⟩
  · rintro ⟨x, hx⟩
    exact ⟨Quotient.mk D.coreEq x, hx⟩

theorem source_range (i : I) :
    Set.range (D.sourceMap i) = D.sourceImage i := by
  ext p
  constructor
  · rintro ⟨q, rfl⟩
    refine Quotient.inductionOn q ?_
    intro x
    exact ⟨x, rfl⟩
  · rintro ⟨x, hx⟩
    exact ⟨Quotient.mk (D.sourceEq i) x, hx⟩

/-- Point equality between different standards is always witnessed in
the original core, even if the point was not supported by a physical node. -/
theorem source_pair_meets_core
    (i j : I) (hij : i ≠ j) (p : D.Point)
    (hp : p ∈ Set.range (D.sourceMap i) ∩ Set.range (D.sourceMap j)) :
    p ∈ Set.range D.coreMap := by
  have hi : p ∈ D.sourceImage i := by
    rw [← D.source_range i]
    exact hp.1
  have hj : p ∈ D.sourceImage j := by
    rw [← D.source_range j]
    exact hp.2
  have hshared : p ∈ D.sharedImage i ∩ D.sharedImage j := by
    rw [← D.distinct_sourceImage_inter i j hij]
    exact ⟨hi, hj⟩
  obtain ⟨q, hq⟩ := hshared.1
  exact ⟨Quotient.mk D.coreEq (D.alpha i q), hq⟩

/-- The amalgamation union of all source relational tuples, on the
*already checked* generated point quotient. -/
def relationalUnion
    (C : RelStructure L (Quotient D.coreEq))
    (S : (i : I) → RelStructure L (Quotient (D.sourceEq i))) :
    RelStructure L D.Point :=
  ACopyRelationalUnion.union C S D.coreMap D.sourceMap

/-- Core inducedness uses only equality/reflection of relations on each
actual core/standard overlap; output linearity is irrelevant. -/
def coreRelEmbedding
    (C : RelStructure L (Quotient D.coreEq))
    (S : (i : I) → RelStructure L (Quotient (D.sourceEq i)))
    (hAgree : CoreSourceAgreement C S D.coreMap D.sourceMap) :
    Embedding C (relationalUnion D C S) :=
  ACopyRelationalUnion.coreEmbedding C S D.coreMap D.sourceMap
    D.coreMap_injective hAgree

/-- Source-to-source relation agreement is not assumed. It follows from
exact point intersections and the core/standard induced link agreement. -/
def sourceRelEmbedding
    (C : RelStructure L (Quotient D.coreEq))
    (S : (i : I) → RelStructure L (Quotient (D.sourceEq i)))
    (hAgree : CoreSourceAgreement C S D.coreMap D.sourceMap)
    (i : I) :
    Embedding (S i) (relationalUnion D C S) := by
  have hStandards : SourceSourceAgreement S D.sourceMap :=
    sourceAgreement_of_core C S D.coreMap D.sourceMap
      (fun j => D.sourceMap_injective j)
      (fun j k hjk p hp => D.source_pair_meets_core j k hjk p hp)
      hAgree
  exact ACopyRelationalUnion.sourceEmbedding C S D.coreMap D.sourceMap
    i (D.sourceMap_injective i) hAgree hStandards

end StructuralRamsey.Girth.ACopyDecoratedRelationalStar
