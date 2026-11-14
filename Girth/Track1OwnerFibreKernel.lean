import PartiteConstruction.Structure.Basic
import Mathlib.Tactic

/-!
# Full unary owner fibres: two elementary Track 1 kernels

The manuscript uses an auxiliary unary partial function d arbitrary in the
ambient EHN class, prescribed only on the expanded source and target. The
following conclusions use only exact full function-embedding preservation.

DRAFT, NOT KERNEL-CHECKED: no local Lean 4 toolchain was available. Do not
promote any validation markers without compiling and inspecting axioms.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey

universe u v
variable {K : StructuralRamsey.Language.{u}}
variable {U V X : Type v}

private theorem imageSet_univ_eq_range (f : U → X) :
    StructuralRamsey.Structure.imageSet f Set.univ = Set.range f := by
  ext x
  constructor
  · rintro ⟨u, _, rfl⟩
    exact ⟨u, rfl⟩
  · rintro ⟨u, rfl⟩
    exact ⟨u, Set.mem_univ u, rfl⟩

/-- If two full embeddings carry the same vertex, and the specified unary
function returns the WHOLE source carrier at each of these preimages,
then the two image carriers coincide. In the application these are
marked vertices of two selected support edges. -/
theorem fullOwner_sameRange_of_shared_fullFibre
    (A : StructuralRamsey.Structure K U)
    (C : StructuralRamsey.Structure K X)
    (d : K.FuncSymbol)
    (e f : StructuralRamsey.Structure.Embedding A C)
    (u v : U)
    (hu : A.func d (fun _ : Fin (K.funcArity d) => u) = Set.univ)
    (hv : A.func d (fun _ : Fin (K.funcArity d) => v) = Set.univ)
    (hshared : e u = f v) :
    Set.range e = Set.range f := by
  have he : StructuralRamsey.Structure.imageSet e Set.univ =
      C.func d (fun _ : Fin (K.funcArity d) => e u) := by
    have hm := e.map_func d (fun _ : Fin (K.funcArity d) => u)
    rw [hu] at hm
    simpa [Function.comp_def] using hm
  have hf : StructuralRamsey.Structure.imageSet f Set.univ =
      C.func d (fun _ : Fin (K.funcArity d) => f v) := by
    have hm := f.map_func d (fun _ : Fin (K.funcArity d) => v)
    rw [hv] at hm
    simpa [Function.comp_def] using hm
  calc
    Set.range e = C.func d (fun _ => e u) :=
      (imageSet_univ_eq_range e).symm.trans he
    _ = C.func d (fun _ => f v) := by rw [hshared]
    _ = Set.range f := ((imageSet_univ_eq_range f).symm.trans hf).symm

/-- A vertex at which a full target embedding has undefined owner fibre
cannot simultaneously lie on a full edge whose source owner fibre is the
complete nonempty source edge. This covers marked isolated target vertices. -/
theorem fullOwner_undefined_not_shared_fullEdge
    (A : StructuralRamsey.Structure K U)
    (B : StructuralRamsey.Structure K V)
    (C : StructuralRamsey.Structure K X)
    (d : K.FuncSymbol)
    (e : StructuralRamsey.Structure.Embedding A C)
    (b : StructuralRamsey.Structure.Embedding B C)
    (u : U) (v : V)
    (hu : A.func d (fun _ : Fin (K.funcArity d) => u) = Set.univ)
    (hv : B.func d (fun _ : Fin (K.funcArity d) => v) = ∅)
    (hshared : e u = b v) : False := by
  have he : e u ∈ C.func d (fun _ : Fin (K.funcArity d) => e u) := by
    have hm := e.map_func d (fun _ : Fin (K.funcArity d) => u)
    rw [hu] at hm
    have hMem : e u ∈
        StructuralRamsey.Structure.imageSet e (Set.univ : Set U) :=
      ⟨u, Set.mem_univ u, rfl⟩
    rw [hm] at hMem
    simpa [Function.comp_def] using hMem
  have hb : C.func d (fun _ : Fin (K.funcArity d) => b v) = ∅ := by
    have hm := b.map_func d (fun _ : Fin (K.funcArity d) => v)
    rw [hv] at hm
    have hm' := hm.symm
    simpa [StructuralRamsey.Structure.imageSet, Function.comp_def] using hm'
  have he' : e u ∈ C.func d (fun _ : Fin (K.funcArity d) => b v) := by
    simpa only [hshared] using he
  rw [hb] at he'
  exact Set.not_mem_empty _ he'

#print axioms StructuralRamsey.Girth.fullOwner_sameRange_of_shared_fullFibre
#print axioms StructuralRamsey.Girth.fullOwner_undefined_not_shared_fullEdge

end StructuralRamsey.Girth
