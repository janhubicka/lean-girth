import Girth.TrainUntouchedActiveDecomposition
import Girth.ForestActualRecursiveSupport
import Girth.ForestMixedLocalForestBridge
import Girth.IncidenceCompression
import Girth.LabelledWagonCutRestriction

set_option Elab.async false

/-!
# Labelled girth of untouched children with distinct standard owners

The new children in the refinement argument are subcarriers of untouched
standard subsystems.  A family having at most one child from each standard
inherits the local forest cutoff: every connector between different
standards lies in the core and in the single common base part.  The true
local gluing forest restricted to that part has an acyclic labelled
incidence graph.

The proof retains the actual child labels and the original physical
connectors.  It requests foresthood only for the at-most-g gluing indices
used by the alleged cycle, not for the whole local witness.  Transversality
of actual irreducible A-edges supplies the one-part hypothesis; a global
transversal system over every base part is unnecessary.

The injective child-to-standard owner map is an explicit input.  Thus this
checks the child-girth mechanism once the children of one output parent
have that property.  Constructing the appended refinement partitions,
their parent maps and permitted-part bounds, and the full remaining-fibre
readiness invariant is separate.  No output girth is assumed.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}} {UA P X Y I J Z : Type v}

/-- Actual irreducible A-support edges meet the inverse image of a
subsingleton set of parts in at most one vertex.  This is sufficient for
the restricted-forest argument, even when some base parts are empty. -/
theorem relationalSupportPieces_meet_subsingleton_parts
    (A : RelStructure L UA) (hA : A.Irreducible)
    (E : StructuralRamsey.Partite.System L P Y)
    {B : RelStructure L Z} (f : I → Embedding B E.toRelStructure)
    (parts : Set P) (hParts : parts.Subsingleton) :
    EdgesMeetPartAtMostOne (fun i => bSupportPiece A (f i))
      (E.part ⁻¹' parts) := by
  intro i edge hEdge x hx y hy
  obtain ⟨a, ha, _⟩ := hEdge
  apply E.part_injOn_irreducible (copyCarrier a) (hA.range_embedding a)
  · rw [ha]
    exact hx.1
  · rw [ha]
    exact hy.1
  · exact hParts hx.2 hy.2

section UntouchedChildren

variable (A₀ : RelStructure L UA) [LinearOrder UA] [Finite UA]
local notation "A" => A₀.ordered
variable (D : RelStructure L.withOrder P)
variable (C : StructuralRamsey.Partite.System L.withOrder P X)
variable (α β : Embedding A₀.ordered D)
variable (E : StructuralRamsey.Partite.System L.withOrder P Y)
variable (f : I → StructuralRamsey.Partite.Embedding
  (C.induce (activeCarrier A₀.ordered C α.toFunctionEmbedding)) E)

local notation "S" => activeCarrier A C α.toFunctionEmbedding
local notation "Out" => StructuralRamsey.Partite.Attachment.attach C S E f
local notation "Std" => StructuralRamsey.Partite.Attachment.copyEmbedding C S E f
local notation "Core" => StructuralRamsey.Partite.Attachment.coreEmbedding C S E f
local notation "F" => fun i : I => bSupportPiece A₀.ordered
  (StructuralRamsey.Partite.Embedding.toEmbedding (f i))

/-- A labelled family of untouched subcarriers with distinct standard
owners has girth greater than the local gluing-forest cutoff.  The
subcarriers themselves need not lie in one part; only their cross-standard
intersections do.  The owner injection is kept explicit. -/
theorem untouchedSubcarriers_labelledGirth_of_localForest
    (hBaseLinear : ALinear A D) (hDifferent : α ≠ β)
    (carrier : J → Set (StructuralRamsey.Partite.Attachment.Vertex S (W := Y) (I := I)))
    (owner : J ↪ I)
    (hContained : ∀ j : J, carrier j ⊆
      copyCarrier (standardActiveEmbedding A C S E f β.toFunctionEmbedding
        (owner j)).toEmbedding)
    (g : ℕ) (hLocal : LocalForestThrough F g) :
    LabelledGirthGT carrier g := by
  classical
  rintro ⟨cycle, hLength⟩
  have hCommon : (copyCarrier α ∩ copyCarrier β).Subsingleton :=
    hBaseLinear α β (fun hSame =>
      hDifferent (ordered_embedding_eq_of_sameCopy α β hSame))
  let Q : Set Y := E.part ⁻¹' (copyCarrier α ∩ copyCarrier β)
  have hPart : EdgesMeetPartAtMostOne F Q :=
    relationalSupportPieces_meet_subsingleton_parts A
      (RelStructure.ordered_hereditarilyIrreducible A₀).irreducible E
      (fun i => (f i).toEmbedding) _ hCommon
  let ownerAt : Fin cycle.length → I := fun k => owner (cycle.label k)
  let Used : Type v := Set.range ownerAt
  let picked : Fin cycle.length → Used := fun k => ⟨ownerAt k, ⟨k, rfl⟩⟩
  have hSurj : Function.Surjective picked := by
    rintro ⟨i, ⟨k, hk⟩⟩
    exact ⟨k, Subtype.ext hk⟩
  let : Finite Used := Finite.of_surjective picked hSurj
  let : Fintype Used := Fintype.ofFinite Used
  let zero : Fin cycle.length := ⟨0, by have := cycle.hlength; omega⟩
  let one : Fin cycle.length := ⟨1, by have := cycle.hlength; omega⟩
  let : Nonempty Used := ⟨picked zero⟩
  have hPicked : Function.Injective picked := by
    intro k l hkl
    exact cycle.label_injective (owner.injective (congrArg Subtype.val hkl))
  have hCard : Fintype.card Used ≤ g := by
    have hLe := Fintype.card_le_of_surjective picked hSurj
    exact hLe.trans (by simpa only [Fintype.card_fin] using hLength)
  let incl : Used ↪ I := ⟨Subtype.val, Subtype.val_injective⟩
  have hForest : ForestOfCopies (fun i : Used => (F) i.val) :=
    hLocal Used incl hCard
  have hPartUsed : EdgesMeetPartAtMostOne (fun i : Used => (F) i.val) Q :=
    fun i _ hEdge => hPart i.val hEdge
  let core := (Core).toEmbedding.toFunctionEmbedding
  have hBoundary : ∀ k : Fin cycle.length,
      picked k ≠ picked (cyclicSucc k) →
      cycle.vertex k ∈ core '' (((F) (picked k).val).restrictCarrier Q).carrier ∧
      cycle.vertex k ∈
        core '' (((F) (picked (cyclicSucc k)).val).restrictCarrier Q).carrier := by
    intro k hNe
    have hOwners : ownerAt k ≠ ownerAt (cyclicSucc k) :=
      fun h => hNe (Subtype.ext h)
    have hLeft := hContained (cycle.label k) (cycle.left_mem k)
    have hRight := hContained (cycle.label (cyclicSucc k)) (cycle.right_mem k)
    obtain ⟨x, hx⟩ := hLeft
    obtain ⟨y, hy⟩ := hRight
    have hLeftStd : cycle.vertex k ∈ copyCarrier (Std (ownerAt k)).toEmbedding :=
      ⟨x.1, hx⟩
    have hRightStd : cycle.vertex k ∈
        copyCarrier (Std (ownerAt (cyclicSucc k))).toEmbedding := ⟨y.1, hy⟩
    obtain ⟨z, hz, hzLeft, hzRight⟩ := attachment_shared_point_in_both_local_images
      C.toRelStructure S E.toRelStructure (fun i => (f i).toEmbedding)
      hOwners hLeftStd hRightStd
    have hOutputPart : (Out).part (cycle.vertex k) ∈ copyCarrier α ∩ copyCarrier β :=
      standardActiveCarriers_inter_part A₀ D C α β E f hOwners
        ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
    have hzQ : z ∈ Q := by
      change E.part z ∈ copyCarrier α ∩ copyCarrier β
      have hPartEq : E.part z = (Out).part (cycle.vertex k) := by
        calc
          E.part z = (Out).part (Core z) := ((Core).map_part z).symm
          _ = (Out).part (cycle.vertex k) := congrArg (Out).part hz
      rw [hPartEq]
      exact hOutputPart
    exact ⟨⟨z, ⟨hzLeft, hzQ⟩, hz⟩, ⟨z, ⟨hzRight, hzQ⟩, hz⟩⟩
  let raw : RawCyclicIncidenceData
      (fun i : Used => core '' (((F) i.val).restrictCarrier Q).carrier) := {
    length := cycle.length
    hlength := cycle.hlength
    label := picked
    connector := cycle.vertex
    connector_injective := cycle.vertex_injective
    boundary_mem := hBoundary
    nonconstant := by
      refine ⟨zero, one, ?_⟩
      intro hEq
      have hVal := congrArg Fin.val (hPicked hEq)
      change 0 = 1 at hVal
      omega
  }
  exact CyclicIncidenceData.no_cyclicIncidenceData_of_mapped_forest_part
    hForest Q hPartUsed core raw.compress

/-- The actual finite-set mixed forest invariant supplies the preceding
child-girth mechanism when the indexed physical gluing pieces are
injective.  No global forest of the whole gluing family is requested. -/
theorem untouchedSubcarriers_labelledGirth_of_finiteMixed
    (hBaseLinear : ALinear A D) (hDifferent : α ≠ β)
    (carrier : J → Set (StructuralRamsey.Partite.Attachment.Vertex S (W := Y) (I := I)))
    (owner : J ↪ I)
    (hContained : ∀ j : J, carrier j ⊆
      copyCarrier (standardActiveEmbedding A C S E f β.toFunctionEmbedding
        (owner j)).toEmbedding)
    (g : ℕ) (hInjective : Function.Injective F)
    (hMixed : FiniteMixedForestThrough
      (RelationalMixedSupportTest A (fun i => (f i).toEmbedding)) g) :
    LabelledGirthGT carrier g := by
  apply untouchedSubcarriers_labelledGirth_of_localForest
    A₀ D C α β E f hBaseLinear hDifferent carrier owner hContained g
  exact FiniteMixedForestThrough.toLocalForestThrough F hInjective
    (RelationalMixedSupportTest A (fun i => (f i).toEmbedding)) g
    (fun i => Or.inl ⟨i, rfl⟩) hMixed

end UntouchedChildren
end StructuralRamsey.Girth
