import Girth.AGeneratedDecorationIdentity
import Girth.ActiveCarrierProjectedSupport
import PartiteConstruction.Partite.Induced

/-!
# Exact decoration of the actual ordered active subsystem

The circulation proof applies the structural local forest lemma to the
induced subsystem on the TRUE active A-carrier of a base A-copy beta.
This subsystem is initially partite over the large Ramsey base D,
rather than literally over A.

All its vertices have parts in the base copy beta[A]. The inverse
part coordinate supplies a genuine A-valued part map. The partite
projection to D and the embedding beta show that this map preserves
relations. For finite ordered A, each contained A-copy projects
exactly to beta, so it has the identity A-part map. With the existing
A-generation invariant, the source relations therefore equal the
decoration of its own full A-support.

This is a deterministic SOURCE translation: no successor-tree,
Hales-Jewett, hypergraph Ramsey witness or support-girth hypothesis
is used in the equality.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {UA P X : Type v}

/-- The A-coordinate of a vertex of the true active beta-carrier,
obtained by inverting beta on its part label. -/
noncomputable def activeSourcePart
    (A : RelStructure L UA)
    (C : StructuralRamsey.Partite.System L P X)
    (beta : UA ↪ P)
    (x : activeCarrier A C beta) : UA :=
  C.restrictedPart beta
    ⟨x.val, activeCarrier_subset_support A C beta x.property⟩

/-- The chosen local A-coordinate reconstructs the actual base part. -/
theorem activeSourcePart_spec
    (A : RelStructure L UA)
    (C : StructuralRamsey.Partite.System L P X)
    (beta : UA ↪ P)
    (x : activeCarrier A C beta) :
    beta (activeSourcePart A C beta x) = C.part x.val :=
  C.restrictedPart_spec beta
    ⟨x.val, activeCarrier_subset_support A C beta x.property⟩

/-- For an ordered D-partite picture, inverse part coordinates of its
true active beta-subsystem define a genuine relational homomorphism
to ordered A. The structural partiteness of the original picture is
the only relational projection hypothesis. -/
theorem activeSourcePart_isHomomorphism
    (A₀ : RelStructure L UA)
    [LinearOrder UA] [Finite UA]
    (D : RelStructure L.withOrder P)
    (C : StructuralRamsey.Partite.System L.withOrder P X)
    (hPartite : C.IsPartiteOver D)
    (beta : RelStructure.Embedding A₀.ordered D) :
    (C.induce (activeCarrier A₀.ordered C beta.toFunctionEmbedding)).toRelStructure.IsHomomorphism
      A₀.ordered (activeSourcePart A₀.ordered C beta.toFunctionEmbedding) := by
  let S := activeCarrier A₀.ordered C beta.toFunctionEmbedding
  let part := activeSourcePart A₀.ordered C beta.toFunctionEmbedding
  intro R z hz
  change C.rel R (Subtype.val ∘ z) at hz
  have hD : D.rel R (C.part ∘ (Subtype.val ∘ z)) :=
    hPartite.1 R (Subtype.val ∘ z) hz
  have hD' : D.rel R (beta ∘ (part ∘ z)) := by
    convert hD using 1
    funext i
    exact (activeSourcePart_spec A₀.ordered C
      beta.toFunctionEmbedding (z i)).symm
  exact (beta.map_rel_iff R (part ∘ z)).mp hD'

/-- Every A-copy actually contained in the ordered beta-active source
has the identity A-coordinate map. This uses finite ordered rigidity
of contained copies, rather than assuming a separate A-partite
presentation of the source. -/
theorem activeSourceACopy_part_identity
    (A₀ : RelStructure L UA)
    [LinearOrder UA] [Finite UA]
    (D : RelStructure L.withOrder P)
    (C : StructuralRamsey.Partite.System L.withOrder P X)
    (hPartite : C.IsPartiteOver D)
    (beta : RelStructure.Embedding A₀.ordered D)
    (a : RelStructure.Embedding A₀.ordered
      (C.induce
        (activeCarrier A₀.ordered C beta.toFunctionEmbedding)).toRelStructure)
    (u : UA) :
    activeSourcePart A₀.ordered C beta.toFunctionEmbedding (a u) = u := by
  obtain ⟨proj, hProj⟩ :=
    activeInduced_ACopy_projects_ordered A₀ D C hPartite beta a
  have hBase :
      C.part (a u).val = beta u := by
    calc
      C.part (a u).val = C.part (proj.val u) :=
        congrArg C.part (hProj u).symm
      _ = beta u := proj.property u
  exact beta.injective
    ((activeSourcePart_spec A₀.ordered C
      beta.toFunctionEmbedding (a u)).trans hBase)

/-- The actual induced beta-active source has precisely the relations
of the canonical decoration of its FULL support hypergraph. Its
A-generation, established separately from designated B-coverage,
is the only combinatorial assumption. No local forest Ramsey theorem
is required to make this change of representation. -/
theorem actualActiveSubsystem_relation_iff_decorated
    (A₀ : RelStructure L UA)
    [LinearOrder UA] [Finite UA]
    (D : RelStructure L.withOrder P)
    (C : StructuralRamsey.Partite.System L.withOrder P X)
    (hPartite : C.IsPartiteOver D)
    (beta : RelStructure.Embedding A₀.ordered D)
    (hGen : AGenerated A₀.ordered
      (C.induce
        (activeCarrier A₀.ordered C beta.toFunctionEmbedding)).toRelStructure)
    (R : L.withOrder.Symbol)
    (z : Fin (L.withOrder.arity R) →
      activeCarrier A₀.ordered C beta.toFunctionEmbedding) :
    (C.induce (activeCarrier A₀.ordered C beta.toFunctionEmbedding)).toRelStructure.rel R z ↔
      (decorateSupport A₀.ordered
        (supportCopies A₀.ordered
          (C.induce
            (activeCarrier A₀.ordered C beta.toFunctionEmbedding)).toRelStructure)
        (activeSourcePart A₀.ordered C beta.toFunctionEmbedding)).rel R z := by
  exact aGenerated_relation_iff_decorated
    A₀.ordered
    (C.induce (activeCarrier A₀.ordered C beta.toFunctionEmbedding)).toRelStructure
    (activeSourcePart A₀.ordered C beta.toFunctionEmbedding)
    hGen
    (activeSourcePart_isHomomorphism A₀ D C hPartite beta)
    (activeSourceACopy_part_identity A₀ D C hPartite beta)
    R z

end StructuralRamsey.Girth
