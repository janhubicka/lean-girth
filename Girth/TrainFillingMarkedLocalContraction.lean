import Girth.TrainFillingOrderedContraction
import Girth.TrainFillingMarkedLocalCopies
import Girth.TrainFillingProjectedFirstWagon
import Girth.TrainFillingMarkedSparseSupport

set_option autoImplicit false
set_option Elab.async false

namespace StructuralRamsey.Girth.TrainRecursiveWitness

open StructuralRamsey.RelStructure
open StructuralRamsey.Partite (System)
open StructuralRamsey.Girth.IndexedPrivateChoice

universe u v w
variable {K : RelLanguage.{u}} {A V O I P : Type v} [LinearOrder A]
variable (A₀ : RelStructure K A) (Target : System K.withOrder A V) (carrier : P → Set V)
variable (H : ColouredEdgeOwnerSplit O A)
variable (selected : I → ColouredOwnerSelectedCopy (W := FirstWagonUnionVertex carrier) H)

local notation "Small" => A₀.ordered
local notation "W" => firstWagonSparseSystem Target carrier
local notation "Used" => H.selectedLiftCarrierFor selected

variable (R : System K.withOrder A (H.selectedLiftCarrierFor selected))
variable (marked : I → StructuralRamsey.Partite.Embedding (firstWagonSparseSystem Target carrier) R)
variable (hMark : ∀ i x, marked i x = H.markedUsedLift selected i x)
variable (hSource : ∀ i, (selected i).sourceEdges =
  supportCopies A₀.ordered (firstWagonSparseSystem Target carrier).toRelStructure)
variable (hSupport : supportCopies A₀.ordered R.toRelStructure =
  Set.range (H.markedUsedEdgeCarrier selected))

/-- The local first-wagon embedding uses the literal sparse summand and
the same marked embedding that supplies the Ramsey arrow. -/
def cutoffTwoMarkedLocalCopy (i : I) (p : P) :
    Embedding (Target.toRelStructure.induce (carrier p)) R.toRelStructure :=
  (marked i).toEmbedding.comp (firstWagonSparseSummand Target carrier p)

omit [LinearOrder A] in
theorem cutoffTwoMarkedLocalCopy_part (i : I) (p : P)
    (x : {v : V // v ∈ carrier p}) :
    R.part (cutoffTwoMarkedLocalCopy Target carrier H selected R marked i p x) = Target.part x.1 :=
  (marked i).map_part (firstWagonSparseSummand Target carrier p x)

/-- The auxiliary order of the sparse summand only depends on its
predicate and the literal tagged vertex map. -/
theorem firstWagonSparseSummand_strictMono [LinearOrder P] [LinearOrder V]
    (hBlocks : ∀ x y : V, Target.part x ≠ Target.part y → x < y → Target.part x < Target.part y)
    (p : P) :
    letI := firstWagonUnionOrder carrier Target.part
    StrictMono (firstWagonSparseSummand Target carrier p) := by
  change ∀ x y : {v : V // v ∈ carrier p}, x < y →
    firstWagonUnionOrderKey carrier Target.part ⟨p, x⟩ <
      firstWagonUnionOrderKey carrier Target.part ⟨p, y⟩
  intro x y hxy
  apply Prod.Lex.toLex_lt_toLex.mpr
  by_cases hEq : Target.part x.1 = Target.part y.1
  · exact Or.inr ⟨hEq, Prod.Lex.toLex_lt_toLex.mpr (Or.inr ⟨rfl, hxy⟩)⟩
  · exact Or.inl (hBlocks x.1 y.1 hEq hxy)

include hMark in
theorem cutoffTwoMarkedLocalCopy_strictMono [LinearOrder V]
    [LinearOrder (FirstWagonUnionVertex carrier)]
    (order : LinearOrder H.Vertex)
    (hMarkedOrder : ∀ i,
      @StrictMono _ _ (inferInstance : Preorder (FirstWagonUnionVertex carrier))
        (H.markedUsedAuxOrder selected order).toPreorder (H.markedUsedLift selected i))
    (hSummandOrder : ∀ p, StrictMono (firstWagonSparseSummand Target carrier p))
    (i : I) (p : P) :
    @StrictMono _ _ (inferInstance : Preorder {v : V // v ∈ carrier p})
      (H.markedUsedAuxOrder selected order).toPreorder
      (cutoffTwoMarkedLocalCopy Target carrier H selected R marked i p) := by
  intro x y hxy
  change @LT.lt Used (H.markedUsedAuxOrder selected order).toLT
    (marked i (firstWagonSparseSummand Target carrier p x))
    (marked i (firstWagonSparseSummand Target carrier p y))
  rw [hMark, hMark]
  exact hMarkedOrder i (hSummandOrder p hxy)

include hMark hSource hSupport in
theorem cutoffTwoMarkedLocalCopy_strong
    (hSpanning : HasSpanningRelation Small)
    (hStrong : ∀ i (f : H.OldEdge) (x y : H.Vertex),
      x ≠ y → x ∈ H.splitEdge f → y ∈ H.splitEdge f →
      x ∈ Set.range (selected i).lift → y ∈ Set.range (selected i).lift →
      ∃ a : (selected i).SourceEdge, (selected i).physicalEdge a = f)
    (i : I) (p : P) :
    AStrong Small R.toRelStructure
      (copyCarrier (cutoffTwoMarkedLocalCopy Target carrier H selected R marked i p)) := by
  apply aStrong_comp_of_aStrong Small _ (W).toRelStructure R.toRelStructure
    (firstWagonSparseSummand Target carrier p) (marked i).toEmbedding
    (firstWagonSparseSummand_aStrong Small Target carrier hSpanning p)
  intro a hMeet
  obtain ⟨x, hx, y, hy, hxy⟩ := Set.not_subsingleton_iff.mp hMeet
  obtain ⟨x₀, hx₀⟩ := hx.2
  obtain ⟨y₀, hy₀⟩ := hy.2
  have hx₀' : H.markedUsedLift selected i x₀ = x := (hMark i x₀).symm.trans hx₀
  have hy₀' : H.markedUsedLift selected i y₀ = y := (hMark i y₀).symm.trans hy₀
  have hNe : x₀ ≠ y₀ := fun h => hxy (hx₀'.symm.trans (h ▸ hy₀'))
  obtain ⟨a₀, he⟩ := H.markedUsedLift_strong_of_exactSupport selected A₀ W hSource hStrong
    i (copyCarrier a) (hSupport ▸ ⟨a, rfl⟩) x₀ y₀ hNe (hx₀' ▸ hx.1) (hy₀' ▸ hy.1)
  rw [he]
  rintro _ ⟨z, _, rfl⟩
  exact ⟨z, hMark i z⟩

include hMark hSource hSupport in
/-- Edge colourings of the restored template are read on exactly the
split edges used by the marked Ramsey theorem. -/
theorem cutoffTwoMarked_wordArrow (κ : Type w)
    (a₀ : Embedding Small (W).toRelStructure)
    (hArrow : ∀ χ : H.SplitPhysicalEdge → κ, ∃ i,
      ∀ a b : (selected i).SourceEdge,
        χ (H.physicalSplitEdge ((selected i).physicalEdge a)) =
          χ (H.physicalSplitEdge ((selected i).physicalEdge b))) :
    ∀ word : {s : Set Used // s ∈ supportCopies Small R.toRelStructure} → κ,
      ∃ i colour, ∀ a : Embedding Small (W).toRelStructure,
        word (actualEdge ((marked i).toEmbedding.comp a)) = colour := by
  intro word
  let edge (s : H.SplitPhysicalEdge) : OldACarrierEdge Small R.toRelStructure := by
    refine ⟨H.markedUsedEdgeCarrier selected s, ?_⟩
    change H.markedUsedEdgeCarrier selected s ∈ supportCopies Small R.toRelStructure
    rw [hSupport]
    exact ⟨s, rfl⟩
  let χ (s : H.SplitPhysicalEdge) := word (edge s)
  obtain ⟨i, hi⟩ := hArrow χ
  let sourceEdge (a : Embedding Small (W).toRelStructure) : (selected i).SourceEdge :=
    ⟨copyCarrier a, (hSource i).symm ▸ ⟨a, rfl⟩⟩
  have hRead (a : Embedding Small (W).toRelStructure) :
      edge (H.physicalSplitEdge ((selected i).physicalEdge (sourceEdge a))) =
        actualEdge ((marked i).toEmbedding.comp a) := by
    apply Subtype.ext
    change H.markedUsedEdgeCarrier selected
      (H.physicalSplitEdge ((selected i).physicalEdge (sourceEdge a))) = _
    rw [H.markedUsedLift_image_sourceEdge selected i (sourceEdge a)]
    ext z
    constructor
    · rintro ⟨_, ⟨x, rfl⟩, hx⟩
      exact ⟨x, (hMark i (a x)).trans hx⟩
    · rintro ⟨x, rfl⟩
      exact ⟨a x, ⟨x, rfl⟩, (hMark i (a x)).symm⟩
  refine ⟨i, word (actualEdge ((marked i).toEmbedding.comp a₀)), ?_⟩
  intro a
  have h := hi (sourceEdge a) (sourceEdge a₀)
  change word (edge _) = word (edge _) at h
  simpa only [hRead] using h

/-- Restrict the marked source's monochromatic family to the actual
selected edges of each original first-wagon summand. -/
theorem cutoffTwoMarked_privateWordArrow
    (κ : Type w)
    (hLocalStrong : ∀ i p, AStrong Small R.toRelStructure
      (copyCarrier (cutoffTwoMarkedLocalCopy Target carrier H selected R marked i p)))
    (hLocalCover : ∀ p (x : {v : V // v ∈ carrier p}),
      ∃ a : Embedding Small (Target.toRelStructure.induce (carrier p)), x ∈ copyCarrier a)
    (hWord : ∀ word : {s : Set Used // s ∈ supportCopies Small R.toRelStructure} → κ,
      ∃ i colour, ∀ a : Embedding Small (W).toRelStructure,
        word (actualEdge ((marked i).toEmbedding.comp a)) = colour) :
    let choices := fun i => privateChoiceOfLocalCopies Small Target.toRelStructure R.toRelStructure
      carrier (cutoffTwoMarkedLocalCopy Target carrier H selected R marked i) (hLocalStrong i) hLocalCover
    ∀ word : {s : Set Used // s ∈ supportCopies Small R.toRelStructure} → κ,
      ∃ i colour, ∀ p e,
        e ∈ selectedCommonEdges choices (supportCopies Small R.toRelStructure) (fun _ => rfl) i p →
        word e = colour := by
  intro choices word
  obtain ⟨i, colour, hi⟩ := hWord word
  refine ⟨i, colour, ?_⟩
  rintro p e ⟨localEdge, ⟨s, hs⟩, he⟩
  obtain ⟨a, ha⟩ := s.2
  let b := (firstWagonSparseSummand Target carrier p).comp a
  have hE : e = actualEdge ((marked i).toEmbedding.comp b) := by
    apply Subtype.ext
    have he' : localEdge.1 = e.1 := congrArg Subtype.val he
    change e.1 = copyCarrier ((marked i).toEmbedding.comp b)
    rw [← he', hs, ha]
    exact (UniformPrivateTemplate.image_copyCarrier_comp Small
      (Target.toRelStructure.induce (carrier p)) R.toRelStructure
      (cutoffTwoMarkedLocalCopy Target carrier H selected R marked i p) a)
  exact hE.symm ▸ hi b

include hSupport in
theorem cutoffTwoMarkedTemplate_cover
    (hPoints : ∀ z : Used, ∃ e : H.SplitPhysicalEdge, z.1 ∈ e.1)
    (z : Used) : ∃ a : Embedding Small R.toRelStructure, z ∈ copyCarrier a := by
  obtain ⟨e, hz⟩ := hPoints z
  have hEdge : H.markedUsedEdgeCarrier selected e ∈ supportCopies Small R.toRelStructure :=
    hSupport.symm ▸ ⟨e, rfl⟩
  obtain ⟨a, ha⟩ := hEdge
  exact ⟨a, ha ▸ hz⟩

include hSupport in
/-- The split edge intersections keep their linearity and their actual
marked predicates on the same restored template. -/
theorem cutoffTwoMarkedTemplate_intersections
    (allowed : Set A) (hPart : R.part = fun z : Used => H.newPredicate z.1)
    (hGirth : GirthGT H.splitPhysicalEdges 2)
    (hMarked : ∀ e f : H.SplitPhysicalEdge, e ≠ f →
      e.1 ∩ f.1 ⊆ {z | H.newPredicate z ∈ allowed})
    (a b : OldACarrierEdge Small R.toRelStructure) (hNe : a ≠ b) :
    (a.1 ∩ b.1).Subsingleton ∧ a.1 ∩ b.1 ⊆ R.part ⁻¹' allowed := by
  obtain ⟨e, he⟩ : a.1 ∈ Set.range (H.markedUsedEdgeCarrier selected) := hSupport ▸ a.2
  obtain ⟨f, hf⟩ : b.1 ∈ Set.range (H.markedUsedEdgeCarrier selected) := hSupport ▸ b.2
  have hDifferent : e ≠ f := fun h => hNe (Subtype.ext (he.symm.trans (h ▸ hf)))
  have hMeet (x : Used) (hx : x ∈ a.1 ∩ b.1) : x.1 ∈ e.1 ∩ f.1 := by
    have hxE : x ∈ H.markedUsedEdgeCarrier selected e := he.symm ▸ hx.1
    have hxF : x ∈ H.markedUsedEdgeCarrier selected f := hf.symm ▸ hx.2
    exact ⟨hxE, hxF⟩
  constructor
  · intro x hx y hy
    exact Subtype.ext (pairwise_subsingleton_of_girthGT_two hGirth e.2 f.2
      (fun h => hDifferent (Subtype.ext h)) (hMeet x hx) (hMeet y hy))
  · intro x hx
    change R.part x ∈ allowed
    rw [hPart]
    exact hMarked e f hDifferent (hMeet x hx)

end StructuralRamsey.Girth.TrainRecursiveWitness
