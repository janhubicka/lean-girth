import Girth.Decoration
import Girth.DesignatedAttachment

/-! # Structural local-forest witness as an active-picture local witness

The hypergraph local lemma supplies a family of strong support embeddings.
When that family covers every target support edge, the decorated relational
witness has exactly the local designated-copy properties required by the
active picture step.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {UA X Y : Type v}

/-- Every target support edge lies inside the image of one designated strong
support copy. -/
def StrongSupportCoversEdges
    (H : Set (Set X)) (K : Set (Set Y))
    (family : Set (StrongSupportEmbedding H K)) : Prop :=
  ∀ E : Set Y, E ∈ K →
    ∃ f : StrongSupportEmbedding H K, f ∈ family ∧
      ∃ e : Set X, e ∈ H ∧ E = f '' e

/-- The local partite embedding associated with one designated strong support
copy. -/
def localForestPartiteCopy
    (A : RelStructure L UA)
    {H : Set (Set X)} {K : Set (Set Y)}
    {partX : X → UA} {partY : Y → UA}
    (hTransH : EdgeTransversal H partX)
    (hTransK : EdgeTransversal K partY)
    (hH : H.Nonempty)
    (hCoverX : ∀ x : X, ∃ e : Set X, e ∈ H ∧ x ∈ e)
    (family : Set (StrongSupportEmbedding H K))
    (hParts :
      ∀ f : StrongSupportEmbedding H K, f ∈ family →
        ∀ x : X, partY (f x) = partX x)
    (q : {f : StrongSupportEmbedding H K // f ∈ family}) :
    StructuralRamsey.Partite.Embedding
      (decorateSupportSystem A H partX hTransH)
      (decorateSupportSystem A K partY hTransK) :=
  decorateSupportSystemEmbedding
    A hTransH hTransK q.1 (hParts q.1 q.2) hH hCoverX

/-- Exact high-girth decoration gives actual irreducible coverage by A-copies. -/
theorem decorateSupport_irreduciblesExtendTo
    (A : RelStructure L UA)
    [Finite UA]
    {K : Set (Set Y)} {partY : Y → UA}
    (hA : A.Irreducible)
    (hTransK : EdgeTransversal K partY)
    (hgtK : GirthGT K 3)
    (hK : K.Nonempty)
    (hCoverY : ∀ y : Y, ∃ e : Set Y, e ∈ K ∧ y ∈ e) :
    RelStructure.IrreduciblesExtendTo A
      (decorateSupport A K partY) := by
  have hExact :=
    decorateSupport_exact A hA hTransK hgtK hK hCoverY
  intro S hS
  obtain ⟨e, he, hSe⟩ := hExact.2 S hS
  let a := decorateSupport_edgeEmbedding A hTransK he
  refine ⟨a, ?_⟩
  intro z
  have hz : z.1 ∈ copyCarrier a := by
    rw [decorateSupport_edgeCarrier A hTransK he]
    exact hSe z
  rcases hz with ⟨u, hu⟩
  exact ⟨u, hu.symm⟩

/-- If the strong support family covers every target edge, every ambient
A-copy of the decorated witness is contained in one designated local copy. -/
theorem localForest_ACopiesCovered
    (A : RelStructure L UA)
    {H : Set (Set X)} {K : Set (Set Y)}
    {partX : X → UA} {partY : Y → UA}
    (hTransH : EdgeTransversal H partX)
    (hTransK : EdgeTransversal K partY)
    (hSupportK :
      supportCopies A (decorateSupport A K partY) = K)
    (hH : H.Nonempty)
    (hCoverX : ∀ x : X, ∃ e : Set X, e ∈ H ∧ x ∈ e)
    (family : Set (StrongSupportEmbedding H K))
    (hParts :
      ∀ f : StrongSupportEmbedding H K, f ∈ family →
        ∀ x : X, partY (f x) = partX x)
    (hFamilyCover : StrongSupportCoversEdges H K family) :
    ACopiesCoveredByLocalCopies A
      (decorateSupportSystem A K partY hTransK)
      (fun q => localForestPartiteCopy
        A hTransH hTransK hH hCoverX family hParts q) := by
  intro a
  have haK : copyCarrier a ∈ K :=
    copyCarrier_mem_of_support_eq hSupportK a
  obtain ⟨f, hf, e, he, hEq⟩ :=
    hFamilyCover (copyCarrier a) haK
  let q : {f : StrongSupportEmbedding H K // f ∈ family} :=
    ⟨f, hf⟩
  refine ⟨q, ?_⟩
  intro y hy
  have hyImg : y ∈ f '' e := by
    rw [← hEq]
    exact hy
  rcases hyImg with ⟨x, hx, rfl⟩
  refine ⟨x, rfl⟩

/-- Complete local designated-coverage hypothesis supplied by a high-girth
structural local-forest witness whose designated family covers every support
edge. -/
theorem localForest_localIrreduciblesCovered
    (A : RelStructure L UA)
    [Finite UA]
    {H : Set (Set X)} {K : Set (Set Y)}
    {partX : X → UA} {partY : Y → UA}
    (hA : A.Irreducible)
    (hTransH : EdgeTransversal H partX)
    (hTransK : EdgeTransversal K partY)
    (hgtK : GirthGT K 3)
    (hH : H.Nonempty)
    (hK : K.Nonempty)
    (hCoverX : ∀ x : X, ∃ e : Set X, e ∈ H ∧ x ∈ e)
    (hCoverY : ∀ y : Y, ∃ e : Set Y, e ∈ K ∧ y ∈ e)
    (family : Set (StrongSupportEmbedding H K))
    (hParts :
      ∀ f : StrongSupportEmbedding H K, f ∈ family →
        ∀ x : X, partY (f x) = partX x)
    (hFamilyCover : StrongSupportCoversEdges H K family) :
    LocalIrreduciblesCoveredByAInCopies A
      (decorateSupportSystem A K partY hTransK)
      (fun q => localForestPartiteCopy
        A hTransH hTransK hH hCoverX family hParts q) := by
  have hIrr :=
    decorateSupport_irreduciblesExtendTo
      A hA hTransK hgtK hK hCoverY
  have hSupportK :
      supportCopies A (decorateSupport A K partY) = K :=
    (decorateSupport_exact A hA hTransK hgtK hK hCoverY).1
  have hACover :=
    localForest_ACopiesCovered
      A hTransH hTransK hSupportK hH hCoverX
      family hParts hFamilyCover
  exact localIrreduciblesCovered_of_extendTo_and_ACopyCover
    A (decorateSupportSystem A K partY hTransK)
    (fun q => localForestPartiteCopy
      A hTransH hTransK hH hCoverX family hParts q)
    hIrr hACover

end StructuralRamsey.Girth
