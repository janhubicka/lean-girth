import Girth.LabelledWagonCutRestriction
import Girth.PartiteIrreducible

/-!
# Ordinary physical girth gives labelled girth for injective carriers

The recursive train's bottom level consists of genuine physical A-support
edges. Their natural labels are the edge sets themselves, with no
duplicates. The ordinary Berge-girth invariant of the bottom forest is
therefore a labelled girth invariant as well.

The implication fails for noninjective carrier maps: repeated distinct
wagon labels with the same set could create a labelled two-cycle.
Injectivity is stated and proved, never silently assumed. This is the
bottom-cut companion to the full-system-to-physical-cut theorem.
-/

namespace StructuralRamsey.Girth

universe u v
variable {I W : Type v}

/-- For an injectively tagged family, ordinary Berge girth of its
range is sufficient for the stronger labelled girth bound. -/
theorem labelledGirthGT_of_injective_carrier_rangeGirth
    (carrier : I → Set W) (hInj : Function.Injective carrier)
    (q : ℕ) (hGirth : GirthGT (Set.range carrier) q) :
    LabelledGirthGT carrier q := by
  rintro ⟨C, hBound⟩
  let B : BergeCycle (Set.range carrier) := {
    length := C.length
    hlength := C.hlength
    edge := fun i => carrier (C.label i)
    vertex := C.vertex
    edge_mem := fun i => ⟨C.label i, rfl⟩
    edge_injective := by
      intro i j h
      exact C.label_injective (hInj h)
    vertex_injective := C.vertex_injective
    left_mem := C.left_mem
    right_mem := C.right_mem
  }
  exact hGirth ⟨B, hBound⟩

/-- The physical A-support edge type is literally a subtype of the
set of real A-copy carriers. An ordinary girth bound on the entire
support is therefore also a labelled bound on every genuine edge
member, without arbitrary carrier labels or edge deletion. -/
theorem physicalASupport_labelledGirth_of_girth
    {L : RelLanguage.{u}} {UA X : Type v}
    (A : RelStructure L UA) (R : RelStructure L X)
    (q : ℕ)
    (hGirth : GirthGT (supportCopies A R) q) :
    LabelledGirthGT
      (fun e : OldACarrierEdge A R => e.val) q := by
  have hRange :
      Set.range (fun e : OldACarrierEdge A R => e.val) =
        supportCopies A R := by
    ext s
    constructor
    · rintro ⟨e, he⟩
      rw [← he]
      exact e.property
    · intro h
      exact ⟨⟨s, h⟩, rfl⟩
  apply labelledGirthGT_of_injective_carrier_rangeGirth
    (fun e : OldACarrierEdge A R => e.val) Subtype.val_injective q
  rw [hRange]
  exact hGirth

end StructuralRamsey.Girth
