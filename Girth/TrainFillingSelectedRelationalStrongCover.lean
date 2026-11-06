import Girth.TrainFillingRelationalSelectedSupport
import Girth.TrainFillingSelectedStrongCover

set_option Elab.async false

/-!
# Exact selected filled physical edges from genuine relational strongness

The checked selected recursive M-copy is A-strongly induced in N.
The abstract filling range theorem previously assumed the old selected
copy's physical edge family was precisely the strongly induced
subfamily of ambient old edges.

Here this old edge-membership condition is CONSTRUCTED from the actual
strong relational embedding: an ambient A-edge that meets the selected
carrier twice is contained in that carrier by AStrong, and hence factors
through the induced relational copy M. The factorization gives an actual
source A-support edge mapping onto the entire ambient physical edge.

Combining that result with checked uniform filling makes the range of
the genuine selected filled-edge embedding exactly ALL ambient filled
edges lying inside the selected carrier. No ambient edge is pruned,
and no output copy-edge equality or arbitrary parent map is assumed.

This is a conditional application of the actual selected-stage strongness.
Constructing M from G0 and the entire selected train Ramsey witness remain
separate obligations.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}} {UA W V X : Type v}

/-- Genuine A-strong inducedness constructs the exact old physical
support-edge membership of any ambient edge meeting a selected copy
in at least two distinct vertices. -/
theorem selectedSupportOldEdge_mem_range_of_strong
    (A : RelStructure L UA)
    (M : RelStructure L W) (N : RelStructure L V)
    (b : Embedding M N)
    (hStrong : AStrong A N (copyCarrier b))
    (e : {F : Set V // F ∈ supportCopies A N})
    (hMeet : ¬ (e.1 ∩ copyCarrier b).Subsingleton) :
    e ∈ Set.range
      (fun s : {F : Set W // F ∈ supportCopies A M} =>
        (⟨b.toFunctionEmbedding '' s.1,
          supportCopy_image_mem A M N b s⟩ :
          {F : Set V // F ∈ supportCopies A N})) := by
  obtain ⟨a, ha⟩ := e.2
  have hInter : ¬ (copyCarrier a ∩ copyCarrier b).Subsingleton := by
    simpa only [← ha] using hMeet
  have hSub : copyCarrier a ⊆ copyCarrier b :=
    hStrong a hInter
  have hFactor : ∀ u : UA, ∃ w : W, a u = b w := by
    intro u
    obtain ⟨w, hw⟩ := hSub ⟨u, rfl⟩
    exact ⟨w, hw.symm⟩
  let q : Embedding A M := a.factorThroughRange b hFactor
  have hComp : b.comp q = a := by
    apply Embedding.ext
    intro u
    exact (Classical.choose_spec (hFactor u)).symm
  let s : {F : Set W // F ∈ supportCopies A M} :=
    ⟨copyCarrier q, ⟨q, rfl⟩⟩
  refine ⟨s, ?_⟩
  apply Subtype.ext
  change b.toFunctionEmbedding '' copyCarrier q = e.1
  calc
    b.toFunctionEmbedding '' copyCarrier q =
        copyCarrier (b.comp q) :=
      (copyCarrier_comp_eq_image b q).symm
    _ = copyCarrier a := congrArg copyCarrier hComp
    _ = e.1 := ha.symm

namespace UniformFillingData

variable (U : UniformFillingData V X)

/-- The complete actual selected filled-edge family is derived from
relational old strongness and the original uniform filling construction.
No independently postulated output copyEdges_eq is needed. -/
theorem selectedSupportFilledEdges_exact_of_strong
    (A : RelStructure L UA)
    (M : RelStructure L W) (N : RelStructure L V)
    (b : Embedding M N)
    (hOld : U.oldEdges = supportCopies A N)
    (hStrong : AStrong A N (copyCarrier b)) :
    Set.range (U.selectedSupportFilledEdgeEmbedding A M N b hOld) =
      {e : U.toTrainFilling.NewEdge |
        e.1 ⊆ copyCarrier b} := by
  change Set.range (U.selectedFilledEdgeEmbedding
      (U.selectedSupportOldEdgeEmbedding A M N b hOld)) =
      {e : U.toTrainFilling.NewEdge | e.1 ⊆ copyCarrier b}
  apply U.selectedFilledEdgeEmbedding_range_eq_contained
    (U.selectedSupportOldEdgeEmbedding A M N b hOld)
    (copyCarrier b)
  · intro s z hz
    rw [U.selectedSupportOldEdgeEmbedding_carrier A M N b hOld s] at hz
    obtain ⟨w, _hw, rfl⟩ := hz
    exact ⟨w, rfl⟩
  · intro f hMeet
    have hSupport : f.1 ∈ supportCopies A N := by
      rw [← hOld]
      exact f.2
    let f' : {F : Set V // F ∈ supportCopies A N} :=
      ⟨f.1, hSupport⟩
    obtain ⟨s, hs⟩ :=
      selectedSupportOldEdge_mem_range_of_strong
        A M N b hStrong f' hMeet
    refine ⟨s, ?_⟩
    apply Subtype.ext
    exact congrArg Subtype.val hs

end UniformFillingData
end StructuralRamsey.Girth
