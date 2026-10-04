import Girth.DesignatedPicture
import Girth.ActivePicture
import PartiteConstruction.Relational.Attachment

/-! # Preservation of designated-copy coverage

The generic partite invariant only remembers projections.  The main girth
construction tracks actual designated B-copies.  A core irreducible is first
covered by an A-copy inside one designated local copy; pulling that A-copy
back to the active subsystem lets the old designated B-cover be transported
through the corresponding standard copy.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {UA VB P X Y I : Type v}

/-- Local witness property used in the structural local-forest step: every
irreducible is contained in an A-copy, and that A-copy is itself contained in
one of the designated local copies of the active subsystem. -/
def LocalIrreduciblesCoveredByAInCopies
    (A : RelStructure L UA)
    (E : StructuralRamsey.Partite.System L P Y)
    {C : StructuralRamsey.Partite.System L P X}
    {S : Set X}
    (f : I → StructuralRamsey.Partite.Embedding (C.induce S) E) : Prop :=
  ∀ (T : Set Y), (E.toRelStructure.induce T).Irreducible →
    ∃ (i : I) (a : RelStructure.Embedding A E.toRelStructure),
      (∀ z : T, z.1 ∈ copyCarrier a) ∧
      copyCarrier a ⊆ copyCarrier (f i).toEmbedding

/-- Transport one old designated B-copy into a standard attached copy. -/
def DesignatedCopy.transportToStandard
    {B : RelStructure L VB} {D : RelStructure L P}
    {C : StructuralRamsey.Partite.System L P X}
    {family : Set (RelStructure.Embedding B D)}
    {S : Set X}
    {E : StructuralRamsey.Partite.System L P Y}
    (f : I → StructuralRamsey.Partite.Embedding (C.induce S) E)
    (i : I)
    (q : DesignatedCopy B D C family) :
    DesignatedCopy B D
      (StructuralRamsey.Partite.Attachment.attach C S E f) family where
  base := q.base
  base_mem := q.base_mem
  lift := q.lift.comp
    (StructuralRamsey.Partite.Attachment.copyEmbedding C S E f i)

/-- Actual designated-copy coverage is preserved by an active/free attachment
when every core irreducible lies in an A-copy inside one designated local
copy. -/
theorem designatedCoversIrreducibles_partiteAttachment
    (A : RelStructure L UA)
    (B : RelStructure L VB)
    (D : RelStructure L P)
    (C : StructuralRamsey.Partite.System L P X)
    (family : Set (RelStructure.Embedding B D))
    (S : Set X)
    (E : StructuralRamsey.Partite.System L P Y)
    (f : I → StructuralRamsey.Partite.Embedding (C.induce S) E)
    (hA : A.Irreducible)
    (hOld : DesignatedCoversIrreducibles B D C family)
    (hLocal : LocalIrreduciblesCoveredByAInCopies A E f) :
    DesignatedCoversIrreducibles B D
      (StructuralRamsey.Partite.Attachment.attach C S E f) family := by
  classical
  let Whole :=
    (StructuralRamsey.Partite.Attachment.attach C S E f).toRelStructure
  let core : RelStructure.Embedding E.toRelStructure Whole :=
    (StructuralRamsey.Partite.Attachment.coreEmbedding C S E f).toEmbedding
  let copy (i : I) : RelStructure.Embedding C.toRelStructure Whole :=
    (StructuralRamsey.Partite.Attachment.copyEmbedding C S E f i).toEmbedding
  let incS : RelStructure.Embedding (C.toRelStructure.induce S)
      C.toRelStructure :=
    RelStructure.inclusion C.toRelStructure S
  intro T hT
  let incT : RelStructure.Embedding (Whole.induce T) Whole :=
    RelStructure.inclusion Whole T
  have hsplit :=
    RelStructure.Attachment.irreducible_core_or_copy
      (B := C.toRelStructure) (S := S) (D := E.toRelStructure)
      (f := fun i => (f i).toEmbedding) T hT
  rcases hsplit with hcore | ⟨i, hcopy⟩
  · have hrangeE :
        ∀ z : T, ∃ y : Y, incT z = core y := by
      intro z
      rcases hcore z with ⟨y, hy⟩
      exact ⟨y, hy⟩
    let eE : RelStructure.Embedding (Whole.induce T) E.toRelStructure :=
      incT.factorThroughRange core hrangeE
    let RngE : Set Y := Set.range eE
    have hRngE : (E.toRelStructure.induce RngE).Irreducible :=
      hT.range_embedding eE
    obtain ⟨i, aE, hTE, hAE⟩ := hLocal RngE hRngE
    have hfactorA :
        ∀ a : UA, ∃ s : S, aE a = (f i).toEmbedding s := by
      intro a
      rcases hAE ⟨a, rfl⟩ with ⟨s, hs⟩
      exact ⟨s, hs.symm⟩
    let aS : RelStructure.Embedding A (C.toRelStructure.induce S) :=
      aE.factorThroughRange (f i).toEmbedding hfactorA
    have haS (a : UA) :
        aE a = (f i).toEmbedding (aS a) :=
      Classical.choose_spec (hfactorA a)
    let aC : RelStructure.Embedding A C.toRelStructure :=
      incS.comp aS
    let RngC : Set X := Set.range aC
    have hRngC : (C.toRelStructure.induce RngC).Irreducible :=
      hA.range_embedding aC
    obtain ⟨q, hq⟩ := hOld RngC hRngC
    refine ⟨q.transportToStandard f i, ?_⟩
    intro z
    have hzE := Classical.choose_spec (hrangeE z)
    let ze : RngE := ⟨eE z, ⟨z, rfl⟩⟩
    have hzeA := hTE ze
    rcases hzeA with ⟨a0, ha0⟩
    have ha0C : aC a0 ∈ RngC := ⟨a0, rfl⟩
    obtain ⟨b, hb⟩ := hq ⟨aC a0, ha0C⟩
    refine ⟨b, ?_⟩
    change z.1 =
      (StructuralRamsey.Partite.Attachment.copyEmbedding C S E f i)
        (q.embedding b)
    have hb' : (aS a0).1 = q.embedding b := by
      simpa [aC, incS] using hb
    have hqS : q.embedding b ∈ S := by
      rw [← hb']
      exact (aS a0).2
    let qs : S := ⟨q.embedding b, hqS⟩
    have hqsa : qs = aS a0 := by
      apply Subtype.ext
      exact hb'.symm
    have hcopyExt :=
      StructuralRamsey.Partite.Attachment.copy_extends
        C S E f i qs
    calc
      z.1 = core (eE z) := by
        exact hzE
      _ = core (aE a0) := congrArg core ha0.symm
      _ = core ((f i).toEmbedding (aS a0)) :=
        congrArg core (haS a0)
      _ = core ((f i).toEmbedding qs) := by rw [hqsa]
      _ = (copy i) (q.embedding b) := by
        exact hcopyExt.symm
  · have hrangeC :
        ∀ z : T, ∃ x : X, incT z = copy i x := by
      intro z
      rcases hcopy z with ⟨x, hx⟩
      exact ⟨x, hx⟩
    let eC : RelStructure.Embedding (Whole.induce T) C.toRelStructure :=
      incT.factorThroughRange (copy i) hrangeC
    let RngC : Set X := Set.range eC
    have hRngC : (C.toRelStructure.induce RngC).Irreducible :=
      hT.range_embedding eC
    obtain ⟨q, hq⟩ := hOld RngC hRngC
    refine ⟨q.transportToStandard f i, ?_⟩
    intro z
    let qz : RngC := ⟨eC z, ⟨z, rfl⟩⟩
    obtain ⟨b, hb⟩ := hq qz
    refine ⟨b, ?_⟩
    have hz := Classical.choose_spec (hrangeC z)
    change z.1 =
      (StructuralRamsey.Partite.Attachment.copyEmbedding C S E f i)
        (q.embedding b)
    calc
      z.1 = incT z := rfl
      _ = copy i (eC z) := hz
      _ = copy i (q.embedding b) := congrArg (copy i) hb

end StructuralRamsey.Girth
