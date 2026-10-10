import Girth.AGeneratedDecorationIdentity

/-!
# Ordered A-generated partite systems are exactly their A-support decoration

An induced A-copy in a genuine A-partite system need not project pointwise
to the identity for arbitrary A: it can project through a nontrivial
self-embedding of A. For FINITE ORDERED A, however, every order-preserving
self-embedding is the identity. Thus the exact-copy-projection hypothesis
of AGeneratedDecorationIdentity is automatic, not an additional
invariant to maintain.

Consequently an A-generated ordered A-partite system is literally the
decorated full A-support, via the identity-on-vertices partite embedding.
This is the source translation needed to apply the structural local-forest
lemma to processed active subsystems.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {U W : Type v}

/-- Every A-copy of a genuine partite system over finite ordered A
projects identically to A, without an extra rigidity hypothesis. -/
theorem orderedPartite_ACopies_project_identity
    (A₀ : RelStructure L U)
    [LinearOrder U] [Finite U]
    (C : StructuralRamsey.Partite.System L.withOrder U W)
    (hPartite : C.IsPartiteOver A₀.ordered)
    (a : RelStructure.Embedding A₀.ordered C.toRelStructure)
    (u : U) :
    C.part (a u) = u := by
  obtain ⟨b, hb⟩ :=
    hPartite.after_irreducible_embedding
      (RelStructure.ordered_hereditarilyIrreducible A₀).irreducible a
  have hMono : StrictMono (b : U → U) :=
    RelStructure.Embedding.strictMono b
  have hId : (b : U → U) = id :=
    StrictMono.eq_id hMono
  calc
    C.part (a u) = b u := (hb u).symm
    _ = u := congrFun hId u

/-- Ordered A-generation and the genuine partite-over-A projection
suffice for the complete identity with decorated A-support.
The source has no separate girth or Ramsey hypothesis. -/
def orderedAGenerated_partite_toDecorated
    (A₀ : RelStructure L U)
    [LinearOrder U] [Finite U]
    (C : StructuralRamsey.Partite.System L.withOrder U W)
    (hGen : AGenerated A₀.ordered C.toRelStructure)
    (hPartite : C.IsPartiteOver A₀.ordered) :
    StructuralRamsey.Partite.Embedding C
      (decorateSupportSystem A₀.ordered
        (supportCopies A₀.ordered C.toRelStructure) C.part
        (aSupport_edgeTransversal_of_exact_projection A₀.ordered C
          (orderedPartite_ACopies_project_identity A₀ C hPartite))) :=
  aGenerated_partite_toDecorated A₀.ordered C hGen hPartite
    (orderedPartite_ACopies_project_identity A₀ C hPartite)

end StructuralRamsey.Girth
