import Girth.DesignatedPicture
import Girth.AttachmentGeometry

/-! # Boundary intersections with the active subsystem

The circulation proof repeatedly uses the following elementary consequence of
partite projection and A-strongness.  A transversal lifted copy meets the true
active subsystem either in at most one vertex or in one whole A-copy carried
by the lifted copy.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {UA VB P X Y I : Type v}

/-- Boundary dichotomy before the free attachment: if a projected B-copy has
A-strong base image, then its intersection with the active subsystem over a
base A-copy is subsingleton or exactly one A-copy inside B. -/
theorem projectedCopy_activeCarrier_intersection_classify
    (A : RelStructure L UA)
    (B : RelStructure L VB)
    (D : RelStructure L P)
    (C : StructuralRamsey.Partite.System L P X)
    (e : RelStructure.Embedding A D)
    (b : RelStructure.Embedding B D)
    (q : StructuralRamsey.Partite.ProjectedEmbedding B C b)
    (hStrong : AStrong A D (copyCarrier b)) :
    (copyCarrier q.val ∩
        activeCarrier A C e.toFunctionEmbedding).Subsingleton ∨
      ∃ aB : RelStructure.Embedding A B,
        copyCarrier q.val ∩
            activeCarrier A C e.toFunctionEmbedding =
          copyCarrier (q.val.comp aB) := by
  classical
  by_cases hsmall :
      (copyCarrier q.val ∩
        activeCarrier A C e.toFunctionEmbedding).Subsingleton
  · exact Or.inl hsmall
  · rw [Set.not_subsingleton_iff] at hsmall
    obtain ⟨x, hx, y, hy, hxy⟩ := hsmall
    have hxE : C.part x ∈ copyCarrier e :=
      activeCarrier_part_in_baseCopy A D C e hx.2
    have hyE : C.part y ∈ copyCarrier e :=
      activeCarrier_part_in_baseCopy A D C e hy.2
    rcases hx.1 with ⟨bx, hbx⟩
    rcases hy.1 with ⟨by0, hby⟩
    have hxB : C.part x ∈ copyCarrier b := by
      refine ⟨bx, ?_⟩
      calc
        b bx = C.part (q.val bx) := (q.property bx).symm
        _ = C.part x := congrArg C.part hbx
    have hyB : C.part y ∈ copyCarrier b := by
      refine ⟨by0, ?_⟩
      calc
        b by0 = C.part (q.val by0) := (q.property by0).symm
        _ = C.part y := congrArg C.part hby
    have hpartxy : C.part x ≠ C.part y := by
      intro hpart
      have hbxy : b bx = b by0 := by
        calc
          b bx = C.part x := by
            calc
              b bx = C.part (q.val bx) := (q.property bx).symm
              _ = C.part x := congrArg C.part hbx
          _ = C.part y := hpart
          _ = b by0 := by
            calc
              C.part y = C.part (q.val by0) :=
                (congrArg C.part hby).symm
              _ = b by0 := q.property by0
      have hb : bx = by0 := b.injective hbxy
      apply hxy
      calc
        x = q.val bx := hbx.symm
        _ = q.val by0 := congrArg q.val hb
        _ = y := hby
    have hbaseMeet :
        ¬(copyCarrier e ∩ copyCarrier b).Subsingleton := by
      rw [Set.not_subsingleton_iff]
      exact ⟨C.part x, ⟨hxE, hxB⟩,
        C.part y, ⟨hyE, hyB⟩, hpartxy⟩
    have hEsub : copyCarrier e ⊆ copyCarrier b :=
      hStrong e hbaseMeet
    have hFactor : ∀ a : UA, ∃ z : VB, e a = b z := by
      intro a
      rcases hEsub ⟨a, rfl⟩ with ⟨z, hz⟩
      exact ⟨z, hz.symm⟩
    let aB : RelStructure.Embedding A B :=
      e.factorThroughRange b hFactor
    have heB (a : UA) : e a = b (aB a) :=
      Classical.choose_spec (hFactor a)
    refine Or.inr ⟨aB, ?_⟩
    apply Set.Subset.antisymm
    · intro z hz
      rcases hz.1 with ⟨bz, hbz⟩
      have hzE :=
        activeCarrier_part_in_baseCopy A D C e hz.2
      rcases hzE with ⟨a, ha⟩
      have hbb : b bz = b (aB a) := by
        calc
          b bz = C.part (q.val bz) := (q.property bz).symm
          _ = C.part z := congrArg C.part hbz
          _ = e a := ha.symm
          _ = b (aB a) := heB a
      have hbza : bz = aB a := b.injective hbb
      refine ⟨a, ?_⟩
      change q.val (aB a) = z
      rw [← hbza]
      exact hbz
    · intro z hz
      rcases hz with ⟨a, rfl⟩
      constructor
      · exact ⟨aB a, rfl⟩
      · let aC :
            StructuralRamsey.Partite.ProjectedEmbedding
              A C e.toFunctionEmbedding :=
          { val := q.val.comp aB
            property := by
              intro u
              calc
                C.part ((q.val.comp aB) u) = b (aB u) :=
                  q.property (aB u)
                _ = e u := (heB u).symm }
        exact ⟨aC, a, rfl⟩


/-- In an A-linear structure, the carrier of each A-copy is A-strong.  Any
ambient A-copy meeting it in more than one vertex must be the same copy. -/
theorem aStrong_copyCarrier_of_aLinear
    {A : RelStructure L UA}
    {D : RelStructure L P}
    (hLinear : ALinear A D)
    (b : RelStructure.Embedding A D) :
    AStrong A D (copyCarrier b) := by
  intro e hMeet
  by_cases hSame : SameCopy e b
  · change copyCarrier e = copyCarrier b at hSame
    rw [hSame]
  · exact (hMeet (hLinear e b hSame)).elim

/-- Specialization of the boundary dichotomy to a lifted A-copy in an
A-linear base. -/
theorem projectedACopy_activeCarrier_intersection_classify
    (A : RelStructure L UA)
    (D : RelStructure L P)
    (C : StructuralRamsey.Partite.System L P X)
    (e b : RelStructure.Embedding A D)
    (q : StructuralRamsey.Partite.ProjectedEmbedding A C b)
    (hLinear : ALinear A D) :
    (copyCarrier q.val ∩
        activeCarrier A C e.toFunctionEmbedding).Subsingleton ∨
      ∃ aA : RelStructure.Embedding A A,
        copyCarrier q.val ∩
            activeCarrier A C e.toFunctionEmbedding =
          copyCarrier (q.val.comp aA) :=
  projectedCopy_activeCarrier_intersection_classify
    A A D C e b q (aStrong_copyCarrier_of_aLinear hLinear b)


/-- Transport the active-boundary dichotomy through one standard free
attachment.  The boundary of the transported projected B-copy against the
local core is subsingleton or exactly one transported A-copy. -/
theorem attachedProjectedCopy_core_intersection_classify
    (A : RelStructure L UA)
    (B : RelStructure L VB)
    (D : RelStructure L P)
    (C : StructuralRamsey.Partite.System L P X)
    (e : RelStructure.Embedding A D)
    (b : RelStructure.Embedding B D)
    (q : StructuralRamsey.Partite.ProjectedEmbedding B C b)
    (hStrong : AStrong A D (copyCarrier b))
    (E : StructuralRamsey.Partite.System L P Y)
    (f : I → StructuralRamsey.Partite.Embedding
      (C.induce (activeCarrier A C e.toFunctionEmbedding)) E)
    (i : I) :
    let S := activeCarrier A C e.toFunctionEmbedding
    let copyI :=
      (StructuralRamsey.Partite.Attachment.copyEmbedding C S E f i).toEmbedding
    let core :=
      (StructuralRamsey.Partite.Attachment.coreEmbedding C S E f).toEmbedding
    (copyCarrier (copyI.comp q.val) ∩ copyCarrier core).Subsingleton ∨
      ∃ aB : RelStructure.Embedding A B,
        copyCarrier (copyI.comp q.val) ∩ copyCarrier core =
          copyCarrier (copyI.comp (q.val.comp aB)) := by
  classical
  let S := activeCarrier A C e.toFunctionEmbedding
  let copyI :=
    (StructuralRamsey.Partite.Attachment.copyEmbedding C S E f i).toEmbedding
  let core :=
    (StructuralRamsey.Partite.Attachment.coreEmbedding C S E f).toEmbedding
  rcases
      projectedCopy_activeCarrier_intersection_classify
        A B D C e b q hStrong with
    hSmall | ⟨aB, hEq⟩
  · left
    intro x hx y hy
    rcases hx.1 with ⟨bx, hbx⟩
    rcases hy.1 with ⟨by0, hby⟩
    rcases hx.2 with ⟨dx, hdx⟩
    rcases hy.2 with ⟨dy, hdy⟩
    have hxS : q.val bx ∈ S := by
      apply
        RelStructure.Attachment.mem_of_copyMap_eq_inl
          (B := C.toRelStructure) (S := S) (D := E.toRelStructure)
          (f := fun k => (f k).toEmbedding)
      exact hbx.trans hdx.symm
    have hyS : q.val by0 ∈ S := by
      apply
        RelStructure.Attachment.mem_of_copyMap_eq_inl
          (B := C.toRelStructure) (S := S) (D := E.toRelStructure)
          (f := fun k => (f k).toEmbedding)
      exact hby.trans hdy.symm
    have hOld : q.val bx = q.val by0 :=
      hSmall
        ⟨⟨bx, rfl⟩, hxS⟩
        ⟨⟨by0, rfl⟩, hyS⟩
    calc
      x = copyI (q.val bx) := hbx.symm
      _ = copyI (q.val by0) := congrArg copyI hOld
      _ = y := hby
  · right
    refine ⟨aB, ?_⟩
    apply Set.Subset.antisymm
    · intro z hz
      rcases hz.1 with ⟨bz, hbz⟩
      rcases hz.2 with ⟨d, hd⟩
      have hzS : q.val bz ∈ S := by
        apply
          RelStructure.Attachment.mem_of_copyMap_eq_inl
            (B := C.toRelStructure) (S := S) (D := E.toRelStructure)
            (f := fun k => (f k).toEmbedding)
        exact hbz.trans hd.symm
      have hOld :
          q.val bz ∈ copyCarrier (q.val.comp aB) := by
        rw [← hEq]
        exact ⟨⟨bz, rfl⟩, hzS⟩
      rcases hOld with ⟨a, ha⟩
      refine ⟨a, ?_⟩
      exact (congrArg copyI ha).trans hbz
    · intro z hz
      rcases hz with ⟨a, rfl⟩
      constructor
      · exact ⟨aB a, rfl⟩
      · have hOld :
            q.val (aB a) ∈
              copyCarrier q.val ∩ S := by
          rw [hEq]
          exact ⟨a, rfl⟩
        let s : S := ⟨q.val (aB a), hOld.2⟩
        refine ⟨f i s, ?_⟩
        change core (f i s) =
          copyI (q.val (aB a))
        exact
          (StructuralRamsey.Partite.Attachment.copy_extends
            C S E f i s).symm

/-- A-copy specialization of the transported boundary dichotomy. -/
theorem attachedProjectedACopy_core_intersection_classify
    (A : RelStructure L UA)
    (D : RelStructure L P)
    (C : StructuralRamsey.Partite.System L P X)
    (e b : RelStructure.Embedding A D)
    (q : StructuralRamsey.Partite.ProjectedEmbedding A C b)
    (hLinear : ALinear A D)
    (E : StructuralRamsey.Partite.System L P Y)
    (f : I → StructuralRamsey.Partite.Embedding
      (C.induce (activeCarrier A C e.toFunctionEmbedding)) E)
    (i : I) :
    let S := activeCarrier A C e.toFunctionEmbedding
    let copyI :=
      (StructuralRamsey.Partite.Attachment.copyEmbedding C S E f i).toEmbedding
    let core :=
      (StructuralRamsey.Partite.Attachment.coreEmbedding C S E f).toEmbedding
    (copyCarrier (copyI.comp q.val) ∩ copyCarrier core).Subsingleton ∨
      ∃ aA : RelStructure.Embedding A A,
        copyCarrier (copyI.comp q.val) ∩ copyCarrier core =
          copyCarrier (copyI.comp (q.val.comp aA)) :=
  attachedProjectedCopy_core_intersection_classify
    A A D C e b q (aStrong_copyCarrier_of_aLinear hLinear b) E f i

end StructuralRamsey.Girth
