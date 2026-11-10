import Girth.ACopyDecoratedRelationalStar

set_option autoImplicit false

/-!
# Deriving core/source relation reflection from full induced link charts

The decorated point star has an exact normal form for equality of a core
point and a source point. Every such equality is witnessed by one point
of the complete gluing link. Choosing a link witness for every tuple
coordinate and using the two genuine link embeddings therefore proves
the required CoreSourceAgreement; it is not a separate axiom.

The result handles nullary symbols as well: an empty tuple has a unique
link-coordinate function, and both embeddings reflect its truth value.

The relational union then gives actual induced core and standard charts,
including unsupported retained chart points. This theorem deliberately
does not derive the A-copy support coverage or train cycle invariants.
-/

namespace StructuralRamsey.Girth.ACopyInducedLinkRelations

open StructuralRamsey.RelStructure
open ACopyLayeredStar ACopyDecoratedStar ACopyRelationalUnion
open ACopyDecoratedRelationalStar

universe u v
variable {L : RelLanguage.{u}}
variable {CN I K PC : Type v} {SN SH PS PQ : I → Type v}
variable {N : Diagram CN I SN SH}
variable (D : Data N K PC PS PQ)

/-- A core/source equality in the generated point quotient has a literal
link witness, modulo the original source point equalities. This uses the
*complete* point presentations, including records not on an A-node. -/
theorem source_core_eq_link_witness
    (i : I) (x : Quotient D.coreEq)
    (y : Quotient (D.sourceEq i))
    (hxy : D.coreMap x = D.sourceMap i y) :
    ∃ p : PQ i,
      Quotient.mk D.coreEq (D.alpha i p) = x ∧
      Quotient.mk (D.sourceEq i) (D.beta i p) = y := by
  revert hxy
  refine Quotient.inductionOn x ?_
  intro a
  refine Quotient.inductionOn y ?_
  intro b h
  have hRecord : D.sourceRecord i b = D.coreRecord a := h.symm
  obtain ⟨p, hpSource, hpCore⟩ :=
    (D.sourceRecord_eq_coreRecord_iff i b a).mp hRecord
  exact ⟨p, Quotient.sound hpCore, Quotient.sound hpSource⟩

/-- Relations agree on all tuples with equal core/source images whenever
the *full induced* link has genuine relational embeddings to both sides
with the declared point coordinates. No separate agreement property
is assumed, and no pairwise standard/standard relation check is needed. -/
theorem core_source_agreement_of_full_induced_links
    (C : RelStructure L (Quotient D.coreEq))
    (S : (i : I) → RelStructure L (Quotient (D.sourceEq i)))
    (Q : (i : I) → RelStructure L (PQ i))
    (embedCore : (i : I) → Embedding (Q i) C)
    (embedSource : (i : I) → Embedding (Q i) (S i))
    (hCoreCoord : ∀ i (p : PQ i),
      embedCore i p = Quotient.mk D.coreEq (D.alpha i p))
    (hSourceCoord : ∀ i (p : PQ i),
      embedSource i p = Quotient.mk (D.sourceEq i) (D.beta i p)) :
    CoreSourceAgreement C S D.coreMap D.sourceMap := by
  intro i sym x y hxy
  classical
  have hWitness : ∀ k : Fin (L.arity sym),
      ∃ p : PQ i, embedCore i p = x k ∧ embedSource i p = y k := by
    intro k
    obtain ⟨p, hcp, hsp⟩ :=
      source_core_eq_link_witness D i (x k) (y k) (hxy k)
    exact ⟨p, (hCoreCoord i p).trans hcp, (hSourceCoord i p).trans hsp⟩
  let z : Fin (L.arity sym) → PQ i := fun k => Classical.choose (hWitness k)
  have hC : (fun k => embedCore i (z k)) = x := by
    funext k
    exact (Classical.choose_spec (hWitness k)).1
  have hS : (fun k => embedSource i (z k)) = y := by
    funext k
    exact (Classical.choose_spec (hWitness k)).2
  have hc : C.rel sym x ↔ (Q i).rel sym z := by
    simpa only [Function.comp_def, hC] using (embedCore i).map_rel_iff sym z
  have hs : (S i).rel sym y ↔ (Q i).rel sym z := by
    simpa only [Function.comp_def, hS] using (embedSource i).map_rel_iff sym z
  exact hc.trans hs.symm

/-- The core is an induced relational chart in the decorated free point
quotient, with the core/source relation agreement now derived from the
actual full induced link embeddings. -/
def core_embedding_of_full_induced_links
    (C : RelStructure L (Quotient D.coreEq))
    (S : (i : I) → RelStructure L (Quotient (D.sourceEq i)))
    (Q : (i : I) → RelStructure L (PQ i))
    (embedCore : (i : I) → Embedding (Q i) C)
    (embedSource : (i : I) → Embedding (Q i) (S i))
    (hCoreCoord : ∀ i (p : PQ i),
      embedCore i p = Quotient.mk D.coreEq (D.alpha i p))
    (hSourceCoord : ∀ i (p : PQ i),
      embedSource i p = Quotient.mk (D.sourceEq i) (D.beta i p)) :
    Embedding C (ACopyDecoratedRelationalStar.relationalUnion D C S) :=
  ACopyDecoratedRelationalStar.coreRelEmbedding D C S
    (core_source_agreement_of_full_induced_links D C S Q
      embedCore embedSource hCoreCoord hSourceCoord)

/-- Every standard is likewise an induced full relational chart. A separate
standard-to-standard agreement premise is not needed: intersection
through the core derives it, even for unsupported source points. -/
def source_embedding_of_full_induced_links
    (C : RelStructure L (Quotient D.coreEq))
    (S : (i : I) → RelStructure L (Quotient (D.sourceEq i)))
    (Q : (i : I) → RelStructure L (PQ i))
    (embedCore : (i : I) → Embedding (Q i) C)
    (embedSource : (i : I) → Embedding (Q i) (S i))
    (hCoreCoord : ∀ i (p : PQ i),
      embedCore i p = Quotient.mk D.coreEq (D.alpha i p))
    (hSourceCoord : ∀ i (p : PQ i),
      embedSource i p = Quotient.mk (D.sourceEq i) (D.beta i p))
    (i : I) :
    Embedding (S i) (ACopyDecoratedRelationalStar.relationalUnion D C S) :=
  ACopyDecoratedRelationalStar.sourceRelEmbedding D C S
    (core_source_agreement_of_full_induced_links D C S Q
      embedCore embedSource hCoreCoord hSourceCoord) i

end StructuralRamsey.Girth.ACopyInducedLinkRelations
