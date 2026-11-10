import Girth.ACopyActualRelationalStar

set_option autoImplicit false

/-!
# Physical A-copy sites should be actual image copies

Taking the physical node type of each source to be its actual A-copy
carriers makes the native completeness and carrier-uniqueness fields
in ACopyActualRelationalStar automatic. One can choose a representing
embedding for every carrier. It need not be unique for an arbitrary
A with automorphisms; coordinate compatibility is a genuinely separate
property. For the ordered A in the manuscript, source rigidity makes
the representing embedding unique.

This is a simplification of SOURCE DATA, not a new Ramsey theorem.
-/

namespace StructuralRamsey.Girth.ACopyCanonicalSites

open StructuralRamsey.RelStructure

universe u v

variable {L : RelLanguage.{u}}
variable {U W : Type v}
variable {A : RelStructure L U} {H : RelStructure L W}

/-- Every physical image copy has a genuine relational embedding
realizing its actual carrier. This is classical choice only, not
an assertion of a canonical coordinate order for nonrigid A. -/
noncomputable def representative (p : supportCopies A H) : Embedding A H :=
  Classical.choose p.property

theorem representative_carrier (p : supportCopies A H) :
    copyCarrier (representative p) = p.val :=
  (Classical.choose_spec p.property).symm

/-- Distinct image-copy sites have distinct native carriers. -/
theorem representative_carrier_injective :
    Function.Injective (fun p : supportCopies A H =>
      copyCarrier (representative p)) := by
  intro p q h
  apply Subtype.ext
  exact (representative_carrier p).symm.trans
    (h.trans (representative_carrier q))

/-- Native physical sites list ALL actual A-copies in the chart. -/
theorem representative_complete (b : Embedding A H) :
    ∃ p : supportCopies A H, SameCopy b (representative p) := by
  let p : supportCopies A H :=
    ⟨copyCarrier b, ⟨b, rfl⟩⟩
  refine ⟨p, ?_⟩
  exact (representative_carrier p).symm

/-- With genuinely rigid A, the carrier-based choice is forced:
any two source embeddings of the same A-copy have equal coordinates. -/
theorem representative_eq_of_rigid
    (hRigid : ∀ b c : Embedding A H, SameCopy b c → b = c)
    (p : supportCopies A H) (b : Embedding A H)
    (h : SameCopy b (representative p)) :
    b = representative p :=
  hRigid b (representative p) h

/-- Under rigidity, physical image copies and full A-embeddings are
equivalent. This theorem must NOT be used without hRigid; in general,
two different A-embeddings can have the same carrier. -/
noncomputable def embeddingsEquivSupport
    (hRigid : ∀ b c : Embedding A H, SameCopy b c → b = c) :
    Embedding A H ≃ supportCopies A H := by
  let f : Embedding A H → supportCopies A H :=
    fun b => ⟨copyCarrier b, ⟨b, rfl⟩⟩
  apply Equiv.ofBijective f
  constructor
  · intro b c h
    apply hRigid b c
    exact congrArg Subtype.val h
  · intro p
    refine ⟨representative p, ?_⟩
    apply Subtype.ext
    exact representative_carrier p

/-- In the ordered setting used by the girth manuscript, hRigid is
already supplied by equality of ordered embeddings with equal carrier.
No arbitrary choice of an A-automorphism remains. -/
noncomputable def orderedEmbeddingsEquivSupport
    {A₀ : RelStructure L U}
    {D : RelStructure L.withOrder W}
    [LinearOrder U] [Finite U] :
    Embedding A₀.ordered D ≃ supportCopies A₀.ordered D :=
  embeddingsEquivSupport
    (fun b c h => ordered_embedding_eq_of_sameCopy b c h)

end StructuralRamsey.Girth.ACopyCanonicalSites
