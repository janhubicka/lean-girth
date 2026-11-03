import Girth.TrainRecursiveLargeBaseCoarsening
import Girth.TrainAllAdjacentParameterPreservation

set_option autoImplicit false

/-!
# Physical edge carriers and train parameters survive larger-base coarsening

The large-base repair changes the PART map only.  Its relational
structure and full physical A-support edge family stay literally fixed.

To transfer wagon sibling-intersection parameters, an allowable fine
part set F_mu in the larger P-base is mapped into the inverse image
of an allowable Q-part set G_mu under D.part:P -> Q.  The previously
verified fine AdjacentParameters bound then applies directly,
including original quotient wagon labels, parent maps and the top cut.

No GirthGT / FullSystemGirthGT is inferred from part coarsening: they
are predicates on the unchanged physical incidence data, for which
the corresponding certificate must still be supplied separately.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}} {UA P Q X : Type v}

variable (A : RelStructure L UA)
variable (D : StructuralRamsey.Partite.System L Q P)
variable (E : StructuralRamsey.Partite.System L P X)
variable (hE : E.IsPartiteOver D.toRelStructure)

/-- Coarsening changes no ambient relational edge or physical support:
the two hypergraph families are definitionally identical. -/
theorem supportCopies_coarsenVia_eq :
    supportCopies A (E.coarsenVia D hE).toRelStructure =
      supportCopies A E.toRelStructure := rfl

/-- A sibling intersection permitted at fine P-parts stays permitted in
coarsened Q-parts.  No edge/wagon label is reindexed, and no wagon is
pruned or identified by its carrier. -/
theorem EdgeTrainLevels.adjacentParameters_after_baseCoarsening
    {m : ℕ} (T : EdgeTrainLevels (OldACarrierEdge A E.toRelStructure) m)
    (permitted : Fin (m + 1) → Set P)
    (allowed : Fin (m + 1) → Set Q)
    (hFine : T.AdjacentParameters (fun edge => edge.1)
      (fun ν => E.part ⁻¹' permitted ν))
    (hAllow : ∀ ν, permitted ν ⊆ D.part ⁻¹' allowed ν) :
    T.AdjacentParameters (fun edge => edge.1)
      (fun ν => (E.coarsenVia D hE).part ⁻¹' allowed ν) := by
  intro μ ν hμν hNext a b hne hParent x hx
  change D.part (E.part x) ∈ allowed ν
  exact hAllow ν ((hFine μ ν hμν hNext) hne hParent hx)

/-- When the fine permitted part sets are the exact preimages of the
coarse allowed sets, the adjacent-train parameter predicates agree
without additional choices or geometric inputs. -/
theorem EdgeTrainLevels.adjacentParameters_coarsen_iff
    {m : ℕ} (T : EdgeTrainLevels (OldACarrierEdge A E.toRelStructure) m)
    (allowed : Fin (m + 1) → Set Q) :
    T.AdjacentParameters (fun edge => edge.1)
      (fun ν => (E.coarsenVia D hE).part ⁻¹' allowed ν) ↔
    T.AdjacentParameters (fun edge => edge.1)
      (fun ν => E.part ⁻¹' (D.part ⁻¹' allowed ν)) := Iff.rfl

end StructuralRamsey.Girth
