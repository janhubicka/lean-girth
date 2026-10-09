import Girth.UntouchedGirthTransversalBridge

/-!
# Girth of every projected untouched A-edge family

The circulation untouched-subsystem argument is naturally a girth
assertion, not a separately chosen short cycle contradiction.  Define
the support family of genuine A-copies with exactly the prescribed
base projection, and discharge all cycle-selection quantifiers in
one theorem.

This is a conditional geometric theorem: the structural local
Ramsey witness still needs to supply bounded forests, transversality
and the gluing-copy carrier equation.  The step from the projected
family to all A-copies in the induced active carrier belongs to the
global picture invariant.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {UA P X Y I Z : Type v}

/-- The support edges of A-copies with precisely one prescribed base
projection; this distinguishes a projected fibre from all ambient
A-copies lying inside its vertex carrier. -/
def projectedSupportCopies
    (A : RelStructure L UA)
    (C : StructuralRamsey.Partite.System L P X)
    (β : UA ↪ P) : Set (Set X) :=
  {e | ∃ a : StructuralRamsey.Partite.ProjectedEmbedding A C β,
    e = copyCarrier a.val}

/-- A projected support edge is an actual support edge of the whole
relational picture. -/
theorem projectedSupportCopies_subset_support
    (A : RelStructure L UA)
    (C : StructuralRamsey.Partite.System L P X)
    (β : UA ↪ P) :
    projectedSupportCopies A C β ⊆
      supportCopies A C.toRelStructure := by
  rintro e ⟨a, rfl⟩
  exact ⟨a.val, rfl⟩

/-- All genuine beta-projected A-edges in the new picture have girth
strictly greater than g. In particular the projected-edge hypothesis
previously supplied for each individual short Berge cycle is now
eliminated by the definition of the tested edge family. -/
theorem untouched_projectedSupport_girthGT_of_transversal_local
    (A : RelStructure L UA)
    (C : StructuralRamsey.Partite.System L P X)
    (S : Set X)
    (E : StructuralRamsey.Partite.System L P Y)
    (f : I → StructuralRamsey.Partite.Embedding (C.induce S) E)
    (α β : UA ↪ P)
    (hA : A.Irreducible)
    (hInter : (Set.range α ∩ Set.range β).Subsingleton)
    (u v : UA) (huv : u ≠ v)
    [Nonempty I]
    (part : Y → UA)
    (hFine : ∀ y, E.part y = α (part y))
    {H : Set (Set Z)} {K : Set (Set Y)}
    (family : I → StrongSupportEmbedding H K)
    (hTransK : EdgeTransversal K part)
    (g : ℕ)
    (hLocalForest :
      LocalForestThrough (fun i : I => (family i).supportPiece) g)
    (hCarrier :
      ∀ i : I,
        Set.range (family i) = copyCarrier ((f i).toEmbedding))
    (hOldBeta :
      GirthGT
        (supportCopies A
          (C.induce (activeCarrier A C β)).toRelStructure) g) :
    GirthGT
      (projectedSupportCopies A
        (StructuralRamsey.Partite.Attachment.attach C S E f) β) g := by
  rintro ⟨cyc, hLen⟩
  let Whole := StructuralRamsey.Partite.Attachment.attach C S E f
  let cycWhole : BergeCycle (supportCopies A Whole.toRelStructure) :=
    cyc.ofEdgeMem (fun j =>
      projectedSupportCopies_subset_support A Whole β (cyc.edge_mem j))
  exact no_short_untouched_cycle_of_transversal_local_support
    A C S E f α β hA hInter u v huv
    part hFine family hTransK g hLocalForest hCarrier
    hOldBeta cycWhole hLen (fun j => cyc.edge_mem j)

end StructuralRamsey.Girth
