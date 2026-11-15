import Girth.Track1SelectedSupportColourArrow
import Girth.Track1OwnerSelectedFromEmbedding
import Girth.ForestImage

/-!
# Numbered Track 1: canonical selected source-edge ownership data

The old physical edge family is the union of ACTUAL selected A-support
carriers. Each selected B embedding determines its own physical edge
map by composition of the genuine A-embeddings B -> C; no independent
edge labelling or ambient-edge coverage hypothesis is introduced.

Only the forbidden-degree-one assumption on the genuine B source
in marked predicates remains an explicit input.

STAGED DRAFT, uncompiled; no kernel certificate.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {UA VB V I Choice : Type v}

/-- Form the old coloured edge system using exactly the positive
A-support of the selected family, with no extraneous ambient edges. -/
def selectedSupportOwnerSystem
    (A : RelStructure L UA)
    {B : RelStructure L VB} {C : RelStructure L V}
    (family : Choice → Embedding B C)
    (predicate : V → I) (allowed : Set I) :
    ColouredEdgeOwnerSplit V I where
  edges := selectedSupportEdges A family
  predicate := predicate
  allowed := allowed

/-- Every source A-edge in B maps to an actual old selected physical
edge of the selected-support owner system, by construction. -/
theorem selectedSupportEdge_image_mem
    (A : RelStructure L UA)
    {B : RelStructure L VB} {C : RelStructure L V}
    (family : Choice → Embedding B C)
    (predicate : V → I) (allowed : Set I)
    (c : Choice) (e : Set VB)
    (he : e ∈ supportCopies A B) :
    (family c).toFunctionEmbedding '' e ∈
      (selectedSupportOwnerSystem A family predicate allowed).edges := by
  rcases he with ⟨a, rfl⟩
  change (family c).toFunctionEmbedding '' copyCarrier a ∈
    selectedSupportEdges A family
  refine ⟨c, a, ?_⟩
  exact (copyCarrier_comp_eq_image (family c) a).symm

/-- From each actual selected B embedding build precisely the edge-owner
input required by the already checked selected lift/strongness machinery.
There is no extra choice of physical edge labels: the mapping is the
image of an actual source A-copy under the displayed B embedding. -/
noncomputable def actualSelectedOwnerCopy
    (A : RelStructure L UA)
    {B : RelStructure L VB} {C : RelStructure L V}
    (family : Choice → Embedding B C)
    (predicate : V → I) (allowed : Set I)
    (c : Choice)
    (hForbidden : ∀ (w : VB)
      (e f : {e : Set VB // e ∈ supportCopies A B}),
      predicate (family c w) ∉ allowed →
      w ∈ e.1 → w ∈ f.1 → e = f) :
    ColouredOwnerSelectedCopy (W := VB)
      (selectedSupportOwnerSystem A family predicate allowed) :=
  ColouredOwnerSelectedCopy.ofEdgeEmbedding
    (selectedSupportOwnerSystem A family predicate allowed)
    (supportCopies A B)
    (family c).toFunctionEmbedding
    (selectedSupportEdge_image_mem A family predicate allowed c)
    hForbidden

#print axioms StructuralRamsey.Girth.selectedSupportEdge_image_mem
#print axioms StructuralRamsey.Girth.actualSelectedOwnerCopy

end StructuralRamsey.Girth
