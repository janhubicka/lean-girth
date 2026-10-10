import Girth.Decoration
import PartiteConstruction.Partite.Induced

/-!
# Exact partite projection of a decorated high-girth support witness

The structural local-forest lemma decorates a transversal support
hypergraph by the source irreducible structure A and uses the source
vertex positions as parts. Its projection to A is an honest
homomorphism-embedding, not merely a weak relation-preserving map.

The only nontrivial reflection obligation is local to an irreducible
vertex set. High support girth puts that set in one support edge;
inside one decorated edge the part map reflects every relation.

Relabelling along a base embedding alpha then gives exactly the
partite-over-base hypothesis and fine-part factorization used by the
circulation picture construction. This needs no Ramsey existence
statement: it is the deterministic decoration geometry.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {U W Q : Type v}

/-- Exact transversal decoration is partite over the source A.
The girth >3 hypothesis is used only to cover irreducibles by one
support edge, where relation reflection is automatic. -/
theorem decorateSupportSystem_isPartiteOver
    (A : RelStructure L U)
    [Finite U]
    {H : Set (Set W)} {part : W → U}
    (hA : A.Irreducible)
    (hTrans : EdgeTransversal H part)
    (hgt : GirthGT H 3)
    (hH : H.Nonempty)
    (hCover : ∀ w : W, ∃ e : Set W, e ∈ H ∧ w ∈ e) :
    (decorateSupportSystem A H part hTrans).IsPartiteOver A := by
  change (decorateSupport A H part).IsHomomorphismEmbedding A part
  have hIrreducibleCovered :=
    (decorateSupport_exact A hA hTrans hgt hH hCover).2
  apply RelStructure.IsHomomorphismEmbedding.of_map_reflect
  · intro R x hx
    rcases hx with ⟨e, he, hIn, hRel⟩
    exact hRel
  · intro S hS
    exact (decorateSupportSystem A H part hTrans).part_injOn_irreducible
      S hS
  · intro S hS R x hIn hRel
    obtain ⟨e, he, hSep⟩ := hIrreducibleCovered S hS
    exact ⟨e, he, (fun i => hSep ⟨x i, hIn i⟩), hRel⟩

/-- Relabelling the decorated parts by one induced base A-embedding
makes the entire local witness partite over the actual Ramsey base. -/
theorem decorateSupportRelabel_isPartiteOver
    (A : RelStructure L U)
    [Finite U]
    {H : Set (Set W)} {part : W → U}
    (hA : A.Irreducible)
    (hTrans : EdgeTransversal H part)
    (hgt : GirthGT H 3)
    (hH : H.Nonempty)
    (hCover : ∀ w : W, ∃ e : Set W, e ∈ H ∧ w ∈ e)
    (D : RelStructure L Q)
    (α : RelStructure.Embedding A D) :
    ((decorateSupportSystem A H part hTrans).relabel
      α.toFunctionEmbedding).IsPartiteOver D := by
  exact StructuralRamsey.Partite.Induced.relabel_isPartiteOver
    A (decorateSupportSystem A H part hTrans)
    (decorateSupportSystem_isPartiteOver
      A hA hTrans hgt hH hCover) α

/-- The fine-part map of the relabelled local witness really is
the processed base embedding composed with the source part map. -/
@[simp] theorem decorateSupportRelabel_part
    (A : RelStructure L U)
    {H : Set (Set W)} {part : W → U}
    (hTrans : EdgeTransversal H part)
    (α : U ↪ Q) (w : W) :
    ((decorateSupportSystem A H part hTrans).relabel α).part w =
      α (part w) := rfl

end StructuralRamsey.Girth
