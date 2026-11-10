import Girth.ACopyCanonicalSites

set_option autoImplicit false

/-!
# Full induced links on canonical actual A-copy sites

A genuinely induced embedding of source charts sends each actual A-copy
carrier to an actual A-copy carrier. This defines an injective map of
physical node sites without inventing a new edge-label equivalence or
pruning the ambient support.

When A is rigid, the unique source parametrization commutes with that
physical node map. The coordinate equation is the remaining crucial
ingredient for instantiating the ACopyDecoratedStar shared coordinates
with actual selected picture links.
-/

namespace StructuralRamsey.Girth.ACopyCanonicalLinks

open StructuralRamsey.RelStructure
open ACopyCanonicalSites

universe u v

variable {L : RelLanguage.{u}}
variable {U W X : Type v}
variable {A : RelStructure L U} {Q : RelStructure L W} {H : RelStructure L X}

/-- Apply an induced relational source inclusion to an ACTUAL physical
A-copy site, retaining its entire image carrier. -/
noncomputable def nodeMap
    (j : Embedding Q H) (p : supportCopies A Q) :
    supportCopies A H :=
  ⟨copyCarrier (j.comp (representative p)),
    ⟨j.comp (representative p), rfl⟩⟩

theorem nodeMap_carrier
    (j : Embedding Q H) (p : supportCopies A Q) :
    (nodeMap j p).val = copyCarrier (j.comp (representative p)) := rfl

/-- The map on physical source nodes is injective. No rigidity is
needed here because physical nodes are already carrier sets. -/
theorem nodeMap_injective
    (j : Embedding Q H) :
    Function.Injective (nodeMap (A := A) j) := by
  intro p q h
  apply (representative_carrier_injective (A := A) (H := Q))
  have hComp : SameCopy (j.comp (representative p))
      (j.comp (representative q)) :=
    congrArg Subtype.val h
  exact sameCopy_of_comp j hComp

/-- Full support carrier transport by a link embedding. -/
theorem nodeMap_mem_image
    (j : Embedding Q H) (p : supportCopies A Q) :
    (nodeMap j p).val = j '' p.val := by
  change copyCarrier (j.comp (representative p)) = j '' p.val
  rw [← representative_carrier p]
  ext x
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨representative p a, ⟨a, rfl⟩, rfl⟩
  · rintro ⟨y, ⟨a, rfl⟩, rfl⟩
    exact ⟨a, rfl⟩

/-- With coordinate-rigid A, the chosen embedding of the image copy
is literally the composite of the link embedding and the chosen
source embedding. This fails without a rigidity assumption for A. -/
theorem representative_nodeMap_commutes_of_rigid
    (j : Embedding Q H)
    (hRigid : ∀ b c : Embedding A H, SameCopy b c → b = c)
    (p : supportCopies A Q) :
    representative (nodeMap j p) = j.comp (representative p) := by
  apply hRigid
  exact representative_carrier (nodeMap j p)

/-- In an ordered finite source, rigidity is already proved by the
existing ordered-copy uniqueness lemma, so the link-coordinate
compatibility has no extra A-automorphism choice. -/
theorem ordered_representative_nodeMap_commutes
    {A₀ : RelStructure L U}
    {Q₀ : RelStructure L.withOrder W}
    {H₀ : RelStructure L.withOrder X}
    [LinearOrder U] [Finite U]
    (j : Embedding Q₀ H₀)
    (p : supportCopies A₀.ordered Q₀) :
    representative (nodeMap j p) = j.comp (representative p) :=
  representative_nodeMap_commutes_of_rigid j
    (fun b c h => ordered_embedding_eq_of_sameCopy b c h) p

end StructuralRamsey.Girth.ACopyCanonicalLinks
