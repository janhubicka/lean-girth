import Girth.DesignatedPicture

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
variable {UA VB P X : Type v}

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

end StructuralRamsey.Girth
