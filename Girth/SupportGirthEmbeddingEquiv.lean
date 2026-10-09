import Girth.Berge
import Girth.ForestDesignatedBSupportTransport

/-!
# Girth is invariant under injective transport of support edges

The existing girthGT_mappedSupportCopies proves that girth of an old
support family implies girth of its image under an embedding.  The
reverse direction is elementary but important in the circulation:
a short old Berge cycle maps injectively to a short Berge cycle of
the full embedded support family.  We record this as a generic
equivalence, rather than requiring the picture-girth proof to build
an ad hoc pullback at every application.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {UA Src Tgt : Type v}

/-- An injective image of a support hypergraph has girth >g only if
the original support hypergraph does. -/
theorem girthGT_source_of_mappedSupportCopies
    (A : RelStructure L UA)
    (B : RelStructure L Src)
    (C : RelStructure L Tgt)
    (i : RelStructure.Embedding B C)
    (g : ℕ)
    (hMapped : GirthGT (mappedSupportCopies A B C i) g) :
    GirthGT (supportCopies A B) g := by
  classical
  rintro ⟨cyc, hLen⟩
  let φ : Src ↪ Tgt := i.toFunctionEmbedding
  have hImageInjective :
      Function.Injective (fun S : Set Src => φ '' S) := by
    intro S T heq
    apply Set.Subset.antisymm
    · intro x hx
      have hImg : φ x ∈ φ '' S := ⟨x, hx, rfl⟩
      have hImgT : φ x ∈ φ '' T :=
        Eq.mp (congrArg (fun V : Set Tgt => φ x ∈ V) heq) hImg
      obtain ⟨y, hy, hyx⟩ := hImgT
      have he : y = x := φ.injective hyx
      simpa [he] using hy
    · intro x hx
      have hImg : φ x ∈ φ '' T := ⟨x, hx, rfl⟩
      have hImgS : φ x ∈ φ '' S :=
        Eq.mpr (congrArg (fun V : Set Tgt => φ x ∈ V) heq) hImg
      obtain ⟨y, hy, hyx⟩ := hImgS
      have he : y = x := φ.injective hyx
      simpa [he] using hy
  have hImageEdge (j : Fin cyc.length) :
      φ '' cyc.edge j ∈ mappedSupportCopies A B C i := by
    obtain ⟨a, ha⟩ := cyc.edge_mem j
    refine ⟨a, ?_⟩
    change φ '' cyc.edge j = copyCarrier (i.comp a)
    rw [ha]
    exact (copyCarrier_comp_eq_image i a).symm
  let imageCycle : BergeCycle (mappedSupportCopies A B C i) := {
    length := cyc.length
    hlength := cyc.hlength
    edge := fun j => φ '' cyc.edge j
    vertex := fun j => φ (cyc.vertex j)
    edge_mem := hImageEdge
    edge_injective := by
      intro j k hEq
      apply cyc.edge_injective
      exact hImageInjective hEq
    vertex_injective := by
      intro j k hEq
      exact cyc.vertex_injective (φ.injective hEq)
    left_mem := by
      intro j
      exact ⟨cyc.vertex j, cyc.left_mem j, rfl⟩
    right_mem := by
      intro j
      exact ⟨cyc.vertex j, cyc.right_mem j, rfl⟩
  }
  exact hMapped ⟨imageCycle, hLen⟩

/-- An embedded support family has precisely the girth cutoff of its
source.  Both directions are proved for all finite cutoffs, including
those at which Berge 2-cycles must be excluded. -/
theorem girthGT_mappedSupportCopies_iff
    (A : RelStructure L UA)
    (B : RelStructure L Src)
    (C : RelStructure L Tgt)
    (i : RelStructure.Embedding B C)
    (g : ℕ) :
    GirthGT (mappedSupportCopies A B C i) g ↔
      GirthGT (supportCopies A B) g := by
  constructor
  · exact girthGT_source_of_mappedSupportCopies A B C i g
  · exact girthGT_mappedSupportCopies A B C i

end StructuralRamsey.Girth
