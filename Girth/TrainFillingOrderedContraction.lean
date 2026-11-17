import Girth.TrainFillingConditionalCutoffTwoCore
import Girth.TrainFillingOrderedShortenedSupport

set_option autoImplicit false
set_option Elab.async false

namespace StructuralRamsey.Girth.TrainRecursiveWitness

open StructuralRamsey.RelStructure
open StructuralRamsey.Partite (System)
open StructuralRamsey.Girth.IndexedPrivateChoice

universe u v
variable {K : RelLanguage.{u}} {A V X C : Type v} {k : ℕ} {tail : List ℕ}
variable [LinearOrder A]
variable {A₀ : RelStructure K A} {Target : System K.withOrder A V}
variable {R : System K.withOrder A X} {enumerate : X ≃ ULift.{v} (Fin k)}
variable {original : EdgeTrainLevels (OldACarrierEdge A₀.ordered Target.toRelStructure)
  (tail.length + 1)}

namespace CutoffTwoContraction

variable (prep : CutoffTwoContraction (C := C) A₀ Target R enumerate original)

/-- Each contracted placement gives a physical edge of the shortened target. -/
theorem supportNonempty [Nonempty (C × original.FirstWagon)] :
    Nonempty (OldACarrierEdge (cutoffTwoShortSource R.part enumerate) prep.system) := by
  exact ⟨actualEdge (prep.source (Classical.choice inferInstance))⟩

/-- Each original vertex belongs to the contraction of its edge's first wagon,
and each private vertex belongs to the contraction that inserted it. -/
theorem supportCovers (z : Vertex (cutoffTwoChoices A₀ Target R original
    prep.localCopy prep.localStrong prep.localCover)) :
    ∃ e : OldACarrierEdge (cutoffTwoShortSource R.part enumerate) prep.system, z ∈ e.1 := by
  let choices := cutoffTwoChoices A₀ Target R original
    prep.localCopy prep.localStrong prep.localCover
  have hOldCover (c : C) (x : V) : ∃ p : original.FirstWagon, x ∈ (choices c).oldCarrier p := by
    obtain ⟨a, ha⟩ := prep.targetCover x
    exact ⟨original.firstWagon (actualEdge a), original.edge_subset_ownerWagonCarrier
      Subtype.val (0 : Fin (tail.length + 1)).succ (actualEdge a) ha⟩
  obtain ⟨cp, hz⟩ := contractedFamily_covers choices hOldCover z
  refine ⟨⟨contractedCarrier choices cp, ?_⟩, hz⟩
  change contractedCarrier choices cp ∈ supportCopies (cutoffTwoShortSource R.part enumerate) prep.system
  rw [prep.support]
  exact ⟨cp, rfl⟩

section Ordered

variable [LinearOrder V] [Fintype V] [LinearOrder X] [LinearOrder C]

@[instance_reducible]
private noncomputable def firstWagonOrder : LinearOrder original.FirstWagon := by
  letI : Finite (OldACarrierEdge A₀.ordered Target.toRelStructure) :=
    Finite.of_injective (fun e : OldACarrierEdge A₀.ordered Target.toRelStructure => e.1)
      Subtype.val_injective
  exact original.wagonQuotientLinearOrder (0 : Fin (tail.length + 1)).succ

/-- The auxiliary linear order on the shortened target uses one insertion
order for the whole choice union. -/
@[instance_reducible]
noncomputable def insertionOrder : LinearOrder (Vertex (cutoffTwoChoices A₀ Target R
    original prep.localCopy prep.localStrong prep.localCover)) :=
  letI := firstWagonOrder (original := original)
  colouredChoiceInsertionOrder (cutoffTwoChoices A₀ Target R original
    prep.localCopy prep.localStrong prep.localCover) Target.part R.part

variable
  (localCopy : ∀ (_ : C) (p : original.FirstWagon),
    Embedding (Target.toRelStructure.induce (cutoffTwoFirstCarrier original Subtype.val p))
      R.toRelStructure)
  (localStrong : ∀ (c : C) (p : original.FirstWagon),
    AStrong A₀.ordered R.toRelStructure (copyCarrier (localCopy c p)))
  (localCover : ∀ (p : original.FirstWagon)
    (x : {v : V // v ∈ cutoffTwoFirstCarrier original Subtype.val p}),
    ∃ a : Embedding A₀.ordered
      (Target.toRelStructure.induce (cutoffTwoFirstCarrier original Subtype.val p)), x ∈ copyCarrier a)
  (firstLinear : ∀ p q : original.FirstWagon, p ≠ q →
    (cutoffTwoFirstCarrier original Subtype.val p ∩
      cutoffTwoFirstCarrier original Subtype.val q).Subsingleton)
  (templateCover : ∀ x : X, ∃ a : Embedding A₀.ordered R.toRelStructure, x ∈ copyCarrier a)
  (targetCover : ∀ x : V, ∃ a : Embedding A₀.ordered Target.toRelStructure, x ∈ copyCarrier a)
  (hColour : ∀ (c : C) (p : original.FirstWagon)
    (x : {v : V // v ∈ cutoffTwoFirstCarrier original Subtype.val p}),
    Target.part x.1 = R.part (localCopy c p x))
  (hCoordinates : ∀ c p, StrictMono (localCopy c p))
  (hEnumerate : StrictMono (fun i : Fin k => enumerate.symm (ULift.up i)))
  (hXBlocks : ∀ x y : X, R.part x ≠ R.part y → x < y → R.part x < R.part y)

/-- Construct the shortened target from the private placements of the induced
first-wagon copies. Its physical edges are exactly those placements. -/
noncomputable def ofLocalCopies : CutoffTwoContraction (C := C) A₀ Target R enumerate original := by
  letI := firstWagonOrder (original := original)
  let choices := cutoffTwoChoices A₀ Target R original localCopy localStrong localCover
  let enumX : Fin k ≃ X := Equiv.ulift.symm.trans enumerate.symm
  let edge := orderedShortenedEdgeEmbedding choices enumX hEnumerate
    Target.part R.part hColour hCoordinates hXBlocks
  refine {
    localCopy := localCopy
    localStrong := localStrong
    localCover := localCover
    system := orderedShortenedTarget choices Target.part R.part
    source := edge
    source_apply := ?_
    support := orderedShortenedTarget_support_eq choices enumX hEnumerate
      Target.part R.part hColour hCoordinates hXBlocks
    firstLinear := firstLinear
    templateCover := templateCover
    targetCover := targetCover
  }
  intro c p x
  have hIndex : ULift.up (enumX.symm x) = enumerate x := by
    change ULift.up (enumerate x).down = enumerate x
    rfl
  rw [← hIndex]
  exact orderedShortenedEdgeEmbedding_apply choices enumX hEnumerate Target.part R.part
    hColour hCoordinates hXBlocks (c, p) x

local notation "Constructed" => ofLocalCopies (enumerate := enumerate) localCopy localStrong
  localCover firstLinear templateCover targetCover hColour hCoordinates hEnumerate hXBlocks

/-- The full ordered expansion of the shortened target extends its auxiliary
insertion order. -/
theorem ofLocalCopies_extendsOrder :
    @ExtendsOrder (colouredOrderedEdgeLanguage A k) _ (Constructed).system
      (Constructed).insertionOrder.toLT := by
  exact letI := firstWagonOrder (original := original)
    orderedShortenedTarget_extendsOrder
      (cutoffTwoChoices A₀ Target R original localCopy localStrong localCover) Target.part R.part

end Ordered
end CutoffTwoContraction
end StructuralRamsey.Girth.TrainRecursiveWitness
