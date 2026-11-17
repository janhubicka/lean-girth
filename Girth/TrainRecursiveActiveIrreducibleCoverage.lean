import Girth.ForestSelectedMixedCoverage

set_option autoImplicit false
set_option Elab.async false

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v

variable {L : RelLanguage.{u}} {UA VB P X : Type v}
variable {A : RelStructure L UA} {B : RelStructure L VB}
variable {D : RelStructure L P} {family : Set (Embedding B D)}

/-- Mixed coverage of the old picture gives A-coverage of every irreducible in a
true active subsystem, even at cutoff two. Project the entire irreducible
substructure to the base before using an old selected B-copy or ambient A-copy
that covers it. The projection is injective on this substructure. -/
theorem activeSubsystem_irreduciblesExtendTo_of_selectedMixedCoverage
    (C : StructuralRamsey.Partite.System L P X)
    (selected : Set (DesignatedCopy B D C family))
    (hPartite : C.IsPartiteOver D)
    (hMixed : SelectedBorACoversIrreducibles A B D C family selected)
    (hA : A.Irreducible) (hBaseLinear : ALinear A D)
    (hBaseStrong : ∀ b : DesignatedCopy B D C family,
      b ∈ selected → AStrong A D (copyCarrier b.base))
    (e : Embedding A D)
    (hRigid : ∀ a : Embedding A D, SameCopy a e → a = e)
    (hActive : (activeCarrier A C e.toFunctionEmbedding).Nonempty) :
    IrreduciblesExtendTo A (C.toRelStructure.induce
      (activeCarrier A C e.toFunctionEmbedding)) := by
  classical
  let S := activeCarrier A C e.toFunctionEmbedding
  let R := C.toRelStructure.induce S
  change IrreduciblesExtendTo A R
  intro T hT
  have projectCover
      (a : StructuralRamsey.Partite.ProjectedEmbedding A C e.toFunctionEmbedding)
      (hCover : ∀ z : T, (z.1 : S).1 ∈ copyCarrier a.val) :
      ∃ b : Embedding A R, ∀ z : T, ∃ u : UA, z.1 = b u := by
    let b := activeInduceProjected A a
      (projected_mem_activeCarrier A C e.toFunctionEmbedding a)
    refine ⟨b.val, ?_⟩
    intro z
    obtain ⟨u, hu⟩ := hCover z
    refine ⟨u, ?_⟩
    apply Subtype.ext
    exact hu.symm
  suffices h :
      ∃ a : StructuralRamsey.Partite.ProjectedEmbedding A C e.toFunctionEmbedding,
        ∀ z : T, (z.1 : S).1 ∈ copyCarrier a.val by
    obtain ⟨a, ha⟩ := h
    exact projectCover a ha
  by_cases hSmall : T.Subsingleton
  · by_cases hNonempty : T.Nonempty
    · obtain ⟨x, hx⟩ := hNonempty
      obtain ⟨a, ha⟩ := x.2
      obtain ⟨u, hu⟩ := ha
      exact ⟨a, fun z => ⟨u, hu.trans (congrArg Subtype.val (hSmall hx z.2))⟩⟩
    · obtain ⟨x, hx⟩ := hActive
      obtain ⟨a, _⟩ := hx
      exact ⟨a, fun z => (hNonempty ⟨z.1, z.2⟩).elim⟩
  let incl : Embedding (R.induce T) C.toRelStructure :=
    (RelStructure.inclusion C.toRelStructure S).comp (RelStructure.inclusion R T)
  let U : Set X := Set.range incl
  have hU : (C.toRelStructure.induce U).Irreducible := hT.range_embedding incl
  have hProj := C.part_injOn_irreducible U hU
  let point (z : T) : U := ⟨z.1.1, ⟨z, rfl⟩⟩
  have hPartIn (z : T) : C.part (point z).1 ∈ copyCarrier e :=
    activeCarrier_part_in_baseCopy A D C e z.1.2
  have pairIntersection {K : Set P}
      (hK : ∀ z : T, C.part (point z).1 ∈ K) :
      ¬ (copyCarrier e ∩ K).Subsingleton := by
    rw [Set.not_subsingleton_iff] at hSmall
    obtain ⟨x, hx, y, hy, hxy⟩ := hSmall
    let x' : T := ⟨x, hx⟩
    let y' : T := ⟨y, hy⟩
    intro hInter
    have hEq := hInter ⟨hPartIn x', hK x'⟩ ⟨hPartIn y', hK y'⟩
    exact hxy (Subtype.ext (hProj (point x').2 (point y').2 hEq))
  rcases hMixed U hU with ⟨b, hb, hB⟩ | ⟨a, hCovered⟩
  · have hInter := pairIntersection (K := copyCarrier b.base) (fun z => by
      obtain ⟨w, hw⟩ := hB (point z)
      exact ⟨w, (b.projects w).symm.trans (congrArg C.part hw).symm⟩)
    have hSub := hBaseStrong b hb e hInter
    have hFactor (u : UA) : ∃ x : VB, e u = b.base x := by
      obtain ⟨x, hx⟩ := hSub ⟨u, rfl⟩
      exact ⟨x, hx.symm⟩
    let eB := e.factorThroughRange b.base hFactor
    have hBase (u : UA) : e u = b.base (eB u) :=
      Classical.choose_spec (hFactor u)
    refine ⟨⟨b.embedding.comp eB, fun u => (b.projects (eB u)).trans
      (hBase u).symm⟩, ?_⟩
    intro z
    obtain ⟨x, hx⟩ := hB (point z)
    obtain ⟨u, hu⟩ := hPartIn z
    have hEq : eB u = x := b.base.injective
      ((hBase u).symm.trans (hu.trans
        ((congrArg C.part hx).trans (b.projects x))))
    exact ⟨u, by rw [RelStructure.Embedding.comp_apply, hEq]; exact hx.symm⟩
  · obtain ⟨aBase, hBase⟩ := hPartite.after_irreducible_embedding hA a
    have hInter := pairIntersection (K := copyCarrier aBase) (fun z => by
      obtain ⟨w, hw⟩ := hCovered (point z)
      exact ⟨w, (hBase w).trans (congrArg C.part hw).symm⟩)
    have hSame : SameCopy aBase e := by
      by_contra hn
      exact hInter (by simpa only [Set.inter_comm] using hBaseLinear aBase e hn)
    have haBase : aBase = e := hRigid aBase hSame
    refine ⟨⟨a, fun u => ?_⟩, fun z => ?_⟩
    · rw [← haBase]
      exact (hBase u).symm
    · obtain ⟨u, hu⟩ := hCovered (point z)
      exact ⟨u, hu.symm⟩

end StructuralRamsey.Girth
