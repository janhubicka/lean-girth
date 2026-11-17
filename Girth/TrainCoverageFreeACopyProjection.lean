import Girth.ActiveCarrierStrong
import Girth.ActualActivePartitePresentation
import Girth.TrainRecursiveLargeBaseCoarsening
import PartiteConstruction.Partite.Attachment
import Mathlib.Tactic

set_option autoImplicit false
set_option Elab.async false

/-!
# Weak partite projection on genuine A-copies

The abstract forest assertion permits local hypergraphs whose auxiliary
order relation joins vertices that do not lie in a common A-edge.
Full IsPartiteOver on the order-expanded language may therefore fail
already at q=2. Only the projections of genuine A-copies are needed
for the active strongness argument.

ProjectsACopies records precisely that weaker physical condition.
It is inherited from full partiteness, survives genuine free
attachment, and implies active-carrier A-strongness under the same
base linearity and rigidity assumptions.

No mixedCoverage, extra Ramsey axiom or order-irreducible coverage
is assumed. Source only: not yet Lean elaborated.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}} {UA P X Y I : Type v}

/-- Projection of every physical A-copy, not of every ambient
order-irreducible substructure. -/
def ProjectsACopies
    (A : RelStructure L UA) (D : RelStructure L P)
    (C : StructuralRamsey.Partite.System L P X) : Prop :=
  ∀ a : Embedding A C.toRelStructure,
    ∃ b : Embedding A D, ∀ x : UA, b x = C.part (a x)

/-- The original stronger partiteness condition entails the
physical-copy projection condition; the converse is not claimed. -/
theorem projectsACopies_of_isPartiteOver
    (A : RelStructure L UA) (D : RelStructure L P)
    (C : StructuralRamsey.Partite.System L P X)
    (hA : A.Irreducible) (hC : C.IsPartiteOver D) :
    ProjectsACopies A D C := by
  intro a
  exact hC.after_irreducible_embedding hA a

/-- A fixed genuine base A-embedding transports a fine-partite
edge-type witness into a picture over D. The only local assumption
concerns its physical A-copies. -/
theorem projectsACopies_relabel_of_fineEdges
    (A : RelStructure L UA) (D : RelStructure L P)
    (H : StructuralRamsey.Partite.System L UA Y)
    (e : Embedding A D)
    (hFine : ∀ a : Embedding A H.toRelStructure,
      ∀ x : UA, H.part (a x) = x) :
    ProjectsACopies A D (H.relabel e.toFunctionEmbedding) := by
  intro a
  refine ⟨e, ?_⟩
  intro x
  change e x = e (H.part (a x))
  exact congrArg e (hFine a x).symm

/-- Rebasing the true active subsystem makes each actual source edge use
its own fine coordinates. The weak physical projection condition suffices. -/
theorem actualActiveSubsystemPartite_fineEdges_of_projectedACopies
    (A : RelStructure L UA) [Finite UA] (D : RelStructure L P)
    (C : StructuralRamsey.Partite.System L P X)
    (hProjected : ProjectsACopies A D C) (e : Embedding A D)
    (hRigid : ∀ b : Embedding A D, SameCopy b e → b = e)
    (a : Embedding A (actualActiveSubsystemPartite A C e.toFunctionEmbedding).toRelStructure)
    (x : UA) :
    (actualActiveSubsystemPartite A C e.toFunctionEmbedding).part (a x) = x := by
  let includeActive : Embedding
      (actualActiveSubsystemPartite A C e.toFunctionEmbedding).toRelStructure
      C.toRelStructure :=
    { toFun := Subtype.val
      injective := Subtype.val_injective
      map_rel_iff := fun _ _ => Iff.rfl }
  obtain ⟨b, hb⟩ := hProjected (includeActive.comp a)
  have hFine (y : UA) :
      e ((actualActiveSubsystemPartite A C e.toFunctionEmbedding).part (a y)) = b y :=
    (activeSourcePart_spec A C e.toFunctionEmbedding (a y)).trans (hb y).symm
  have hSame : SameCopy b e :=
    sameCopy_of_range_subset b e (fun y => ⟨_, (hFine y).symm⟩)
  apply e.injective
  exact (hFine x).trans (congrArg (fun c : Embedding A D => c x) (hRigid b hSame))

/-- A physical A-copy contained in a true partite embedding image
inherits the original source's projected base copy. -/
private theorem projectsACopies_factor
    (A : RelStructure L UA) (D : RelStructure L P)
    (C : StructuralRamsey.Partite.System L P X)
    (E : StructuralRamsey.Partite.System L P Y)
    (g : StructuralRamsey.Partite.Embedding C E)
    (hC : ProjectsACopies A D C)
    (a : Embedding A E.toRelStructure)
    (hrange : ∀ x : UA, ∃ y : X, a x = g y) :
    ∃ b : Embedding A D, ∀ x : UA, b x = E.part (a x) := by
  classical
  let aC : Embedding A C.toRelStructure :=
    a.factorThroughRange g.toEmbedding hrange
  obtain ⟨b, hb⟩ := hC aC
  refine ⟨b, ?_⟩
  intro x
  calc
    b x = C.part (aC x) := hb x
    _ = E.part (g (aC x)) := (g.map_part (aC x)).symm
    _ = E.part (a x) := by
      congr 1
      exact (Classical.choose_spec (hrange x)).symm

/-- Free attachment preserves projection of A-copies. Irreducibility
of A factors each copy through the actual core or a standard copy;
nothing is inferred about arbitrary order-irreducible ambient sets. -/
theorem projectsACopies_freeAttachment
    (A : RelStructure L UA) (D : RelStructure L P)
    (C : StructuralRamsey.Partite.System L P X)
    (S : Set X) (E : StructuralRamsey.Partite.System L P Y)
    (f : I → StructuralRamsey.Partite.Embedding (C.induce S) E)
    (hA : A.Irreducible)
    (hOld : ProjectsACopies A D C)
    (hCore : ProjectsACopies A D E) :
    ProjectsACopies A D
      (StructuralRamsey.Partite.Attachment.attach C S E f) := by
  classical
  intro a
  let W := StructuralRamsey.Partite.Attachment.attach C S E f
  have hIrr : (W.toRelStructure.induce (Set.range a)).Irreducible :=
    hA.range_embedding a
  rcases RelStructure.Attachment.irreducible_core_or_copy
      (B := C.toRelStructure) (S := S) (D := E.toRelStructure)
      (f := fun i => (f i).toEmbedding)
      (Set.range a) hIrr with hInCore | ⟨i, hInCopy⟩
  · let g := StructuralRamsey.Partite.Attachment.coreEmbedding C S E f
    have hrange : ∀ x : UA, ∃ y : Y, a x = g y := by
      intro x
      obtain ⟨y, hy⟩ := hInCore ⟨a x, ⟨x, rfl⟩⟩
      exact ⟨y, hy⟩
    exact projectsACopies_factor A D E W g hCore a hrange
  · let g := StructuralRamsey.Partite.Attachment.copyEmbedding C S E f i
    have hrange : ∀ x : UA, ∃ y : X, a x = g y := by
      intro x
      obtain ⟨y, hy⟩ := hInCopy ⟨a x, ⟨x, rfl⟩⟩
      exact ⟨y, hy⟩
    exact projectsACopies_factor A D C W g hOld a hrange


/-- One genuine projected A-copy determines its base A-embedding using
the weak physical projection condition, without ordered
IsPartiteOver or coverage of arbitrary irreducibles. -/
theorem baseEmbedding_of_projectedACopy
    (A : RelStructure L UA) (D : RelStructure L P)
    (C : StructuralRamsey.Partite.System L P X)
    (hProjected : ProjectsACopies A D C)
    (α : UA ↪ P)
    (a : StructuralRamsey.Partite.ProjectedEmbedding A C α) :
    ∃ e : Embedding A D, e.toFunctionEmbedding = α := by
  obtain ⟨e, he⟩ := hProjected a.val
  refine ⟨e, ?_⟩
  apply Function.Embedding.ext
  intro x
  exact (he x).trans (a.property x)

/-- A-strongness of the actual active carrier needs only
physical A-copy projection, base linearity, and rigidity. -/
theorem activeCarrier_aStrong_of_projectedACopies
    (A : RelStructure L UA) (D : RelStructure L P)
    (C : StructuralRamsey.Partite.System L P X)
    (hProjected : ProjectsACopies A D C)
    (hLinear : ALinear A D)
    (e : Embedding A D)
    (hRigid : ∀ b : Embedding A D, SameCopy b e → b = e) :
    AStrong A C.toRelStructure
      (activeCarrier A C e.toFunctionEmbedding) := by
  classical
  intro a hMeet
  obtain ⟨b, hb⟩ := hProjected a
  have hBaseMeet :
      ¬(copyCarrier b ∩ copyCarrier e).Subsingleton := by
    rw [Set.not_subsingleton_iff] at hMeet ⊢
    rcases hMeet with ⟨x, hx, y, hy, hxy⟩
    rcases hx.1 with ⟨ax, hax⟩
    rcases hy.1 with ⟨ay, hay⟩
    have hxE : C.part x ∈ copyCarrier e :=
      activeCarrier_part_in_baseCopy A D C e hx.2
    have hyE : C.part y ∈ copyCarrier e :=
      activeCarrier_part_in_baseCopy A D C e hy.2
    have hbx : b ax = C.part x := by
      calc
        b ax = C.part (a ax) := hb ax
        _ = C.part x := congrArg C.part hax
    have hby : b ay = C.part y := by
      calc
        b ay = C.part (a ay) := hb ay
        _ = C.part y := congrArg C.part hay
    have hbxy : b ax ≠ b ay := by
      intro h
      have haxy : ax = ay := b.injective h
      apply hxy
      calc
        x = a ax := hax.symm
        _ = a ay := congrArg a haxy
        _ = y := hay
    refine ⟨b ax, ?_, b ay, ?_, hbxy⟩
    · constructor
      · exact ⟨ax, rfl⟩
      · rw [hbx]
        exact hxE
    · constructor
      · exact ⟨ay, rfl⟩
      · rw [hby]
        exact hyE
  have hSame : SameCopy b e := by
    by_contra hne
    exact hBaseMeet (hLinear b e hne)
  have hbe : b = e := hRigid b hSame
  let aProjected :
      StructuralRamsey.Partite.ProjectedEmbedding
        A C e.toFunctionEmbedding := {
    val := a
    property := by
      intro x
      have h := hb x
      rw [hbe] at h
      exact h.symm }
  intro z hz
  rcases hz with ⟨x, rfl⟩
  exact ⟨aProjected, x, rfl⟩

end StructuralRamsey.Girth
