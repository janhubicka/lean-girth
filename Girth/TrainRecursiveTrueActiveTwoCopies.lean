import Girth.TrainRecursiveNontrivialFibre
import Girth.TrainRecursiveActivePartite

set_option autoImplicit false
set_option Elab.async false

/-!
# Nontrivial physical projected fibres give two genuine active target copies

A recursive nontrivial local step is entered only when its actual
projected A-fibre has two different physical copy carriers.
The lower recursive target is the honest induced active A-subsystem
on that projected profile, not the entire ambient part fibre.

The existing physical-support theorem constructs two DISTINCT labelled
OldACarrierEdges in this genuine lower target. Unpacking the literal
support embeddings yields two A-embeddings with distinct image carriers,
precisely the target-two-copies premise of the fine-witness constructor.
No new target pair, quotient of image labels or independent two-copy
assumption is needed. Circulation only; no appendix.
-/

namespace StructuralRamsey.Girth.TrainRecursiveWitness

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}} {UA P X : Type v}

/-- A nontrivial actual projected fibre *forces* the two physical A-copies
in the exact true active target of the recursive lower call. -/
theorem activeTarget_twoGenuineCopies_of_nontrivialFibre
    (A : RelStructure L UA)
    (C : StructuralRamsey.Partite.System L P X)
    (α : UA ↪ P)
    (hPair : ∃ a b : StructuralRamsey.Partite.ProjectedEmbedding A C α,
      copyCarrier a.val ≠ copyCarrier b.val) :
    ∃ a b : Embedding A
      (actualActiveSubsystemPartite A C α).toRelStructure,
      ¬ SameCopy a b := by
  obtain ⟨a, b, hab⟩ := hPair
  obtain ⟨s, t, hst⟩ :=
    activeSupport_two_distinct_of_projected_carriers A C α a b hab
  obtain ⟨a', ha'⟩ := s.2
  obtain ⟨b', hb'⟩ := t.2
  refine ⟨a', b', ?_⟩
  intro hSame
  apply hst
  apply Subtype.ext
  change copyCarrier a' = copyCarrier b' at hSame
  exact ha'.trans (hSame.trans hb'.symm)

end StructuralRamsey.Girth.TrainRecursiveWitness
