import Girth.DesignatedPicture
import Girth.Decoration
import PartiteConstruction.Partite.Induced

/-!
# Exact decoration of an A-generated partite system

The structural local-forest lemma applies to the support hypergraph
of an A-generated active subsystem. Its canonical decoration is
literally the same relational structure, provided the part projection
preserves relation tuples and every A-copy projects pointwise to A.

No girth or Ramsey theorem is needed for this *source* equivalence.
High girth is needed separately for the new local witness's exact
support and irreducible coverage.

This is the precise bridge between the manuscript's old active
relational subsystem and the support-hypergraph presentation used
to construct its local Ramsey witness.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {U W : Type v}

/-- In an A-generated structure, the original relation is exactly the
relation obtained by decorating its full A-support, provided every
A-copy is part-preserving and the part map preserves relations. -/
theorem aGenerated_relation_iff_decorated
    (A : RelStructure L U)
    (D : RelStructure L W)
    (part : W → U)
    (hGen : AGenerated A D)
    (hProjection : D.IsHomomorphism A part)
    (hCopyPart :
      ∀ (a : RelStructure.Embedding A D) (u : U),
        part (a u) = u)
    (R : L.Symbol) (z : Fin (L.arity R) → W) :
    D.rel R z ↔
      (decorateSupport A (supportCopies A D) part).rel R z := by
  constructor
  · intro hR
    obtain ⟨a, hIn⟩ := hGen.2 R z hR
    exact ⟨copyCarrier a, ⟨a, rfl⟩, hIn,
      hProjection R z hR⟩
  · rintro ⟨e, ⟨a, rfl⟩, hIn, hA⟩
    have hPoint (i : Fin (L.arity R)) :
        z i = a (part (z i)) := by
      obtain ⟨u, hu⟩ := hIn i
      have hPart : part (z i) = u := by
        calc
          part (z i) = part (a u) := congrArg part hu.symm
          _ = u := hCopyPart a u
      calc
        z i = a u := hu.symm
        _ = a (part (z i)) := congrArg a hPart.symm
    have hTuple : z = a ∘ (part ∘ z) := by
      funext i
      exact hPoint i
    rw [hTuple]
    exact (a.map_rel_iff R (part ∘ z)).mpr hA

/-- A support edge of a partite A-system has exactly one vertex
in each A-part whenever every A-copy projects to the identity. -/
theorem aSupport_edgeTransversal_of_exact_projection
    (A : RelStructure L U)
    (C : StructuralRamsey.Partite.System L U W)
    (hCopyPart :
      ∀ (a : RelStructure.Embedding A C.toRelStructure) (u : U),
        C.part (a u) = u) :
    EdgeTransversal (supportCopies A C.toRelStructure) C.part := by
  intro e he p
  obtain ⟨a, rfl⟩ := he
  refine ⟨a p, ⟨⟨p, rfl⟩, hCopyPart a p⟩, ?_⟩
  intro w hw
  obtain ⟨u, hu⟩ := hw.1
  have hup : u = p := by
    calc
      u = C.part (a u) := (hCopyPart a u).symm
      _ = C.part w := congrArg C.part hu
      _ = p := hw.2
  calc
    w = a u := hu.symm
    _ = a p := congrArg a hup

/-- An A-generated partite system embeds by the identity map into
the canonical decoration of its A-support, preserving its parts.
No new relational tuples are introduced or lost. -/
def aGenerated_partite_toDecorated
    (A : RelStructure L U)
    (C : StructuralRamsey.Partite.System L U W)
    (hGen : AGenerated A C.toRelStructure)
    (hPartite : C.IsPartiteOver A)
    (hCopyPart :
      ∀ (a : RelStructure.Embedding A C.toRelStructure) (u : U),
        C.part (a u) = u) :
    StructuralRamsey.Partite.Embedding C
      (decorateSupportSystem A
        (supportCopies A C.toRelStructure) C.part
        (aSupport_edgeTransversal_of_exact_projection
          A C hCopyPart)) where
  toEmbedding := {
    toFun := id
    injective := fun _ _ h => h
    map_rel_iff := by
      intro R z
      simpa only [Function.id_comp] using
        (aGenerated_relation_iff_decorated
          A C.toRelStructure C.part hGen hPartite.1 hCopyPart R z).symm
  }
  map_part _ := rfl

end StructuralRamsey.Girth
