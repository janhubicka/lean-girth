import Girth.Track1ColouredSupportBridge
import Girth.ActualActivePartitePresentation
import Girth.ForestDesignatedBSupportTransport
import Girth.ForestCompleteBSupportIntrinsic
import Girth.ForestActualRecursiveSupport
import Girth.ForestRecursiveOutputGirth

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v w

variable {L : RelLanguage.{u}} {U P X Y I : Type v}

section ActiveFibre

variable (A₀ : RelStructure L U) [LinearOrder U] [Finite U]
variable (D : RelStructure L.withOrder P)
variable (C : Partite.System L.withOrder P X) (hPartite : C.IsPartiteOver D)
variable (e : Embedding A₀.ordered D)

local notation "A" => A₀.ordered
local notation "α" => e.toFunctionEmbedding
local notation "S" => activeCarrier A C α
local notation "source" => Partite.System.induce C S
local notation "edges" => supportCopies A (Partite.System.toRelStructure source)
local notation "partS" => activeSourcePart A C α

variable {K : Set (Set Y)} {partK : Y → U} (hTrans : EdgeTransversal K partK)

local notation "core" => Partite.System.relabel (decorateSupportSystem A K partK hTrans) α

/-- The selected strong support embedding of the true active carrier
becomes a part-preserving gluing map over the original base. Its point
map is the selected support lift. -/
noncomputable def actualActiveFibreSupportLift
    (hActive : (S).Nonempty) (hGen : AGenerated A (source).toRelStructure)
    (f : StrongSupportEmbedding edges K)
    (hParts : ∀ x : S, partK (f x) = partS x) :
    Partite.Embedding source core := by
  let lift := decorateSupportSystemEmbedding A
    (actualActiveSupport_edgeTransversal A₀ D C hPartite e) hTrans
    f hParts (actualActiveSupport_nonempty A C α hActive)
    (actualActiveSupport_vertexCovered A C α)
  let active := actualActiveSubsystem_toDecorated A₀ D C hPartite e hGen
  refine ⟨lift.toEmbedding.comp active.toEmbedding, ?_⟩
  intro x
  exact (congrArg α (hParts x)).trans (activeSourcePart_spec A C α x)

/-- The selected partite lift carries the complete induced support piece of
the active source, including every edge inside the selected image. -/
theorem actualActiveFibreSupportLift_piece
    (hActive : (S).Nonempty) (hGen : AGenerated A (source).toRelStructure)
    (f : StrongSupportEmbedding edges K)
    (hParts : ∀ x : S, partK (f x) = partS x) :
    let lift := (actualActiveFibreSupportLift A₀ D C hPartite e hTrans
      hActive hGen f hParts).toEmbedding
    bSupportPiece A lift = f.supportPiece := by
  let lift := (actualActiveFibreSupportLift A₀ D C hPartite e hTrans
    hActive hGen f hParts).toEmbedding
  change bSupportPiece A lift = f.supportPiece
  rw [bSupportPiece_eq_embeddedACopySupportPiece]
  have hEdges : (embeddedACopySupportPiece A lift).edges = f.supportPiece.edges := by
    ext F
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨copyCarrier a, ⟨a, rfl⟩, copyCarrier_comp_eq_image lift a⟩
    · rintro ⟨_, ⟨a, rfl⟩, hF⟩
      exact ⟨a, hF.trans (copyCarrier_comp_eq_image lift a).symm⟩
  have hCarrier : (embeddedACopySupportPiece A lift).carrier = f.supportPiece.carrier := rfl
  generalize embeddedACopySupportPiece A lift = F at *
  generalize f.supportPiece = G at *
  cases F
  cases G
  simp_all

/-- The genuine lifted relational supports satisfy the finite-set mixed
forest bound consumed by the cutoff-three picture increment. -/
theorem actualActiveFibreSupportLift_mixedForest
    (hActive : (S).Nonempty) (hGen : AGenerated A (source).toRelStructure)
    (f : I → StrongSupportEmbedding edges K)
    (hParts : ∀ i x, partK (f i x) = partS x)
    (hSupport : supportCopies A (core).toRelStructure = K)
    (m : ℕ)
    (hMixed : LocalForestThrough
      (mixedOwnerSmall (fun i => (f i).supportPiece)
        (fun E : {E : Set Y // E ∈ K} => E.1)) m) :
    FiniteMixedForestThrough (RelationalMixedSupportTest A (fun i =>
      (actualActiveFibreSupportLift A₀ D C hPartite e hTrans
        hActive hGen (f i) (hParts i)).toEmbedding)) m := by
  apply hMixed.toFiniteMixedForestThrough_of_representatives
  intro T hT
  rcases hT with ⟨i, rfl⟩ | ⟨a, rfl⟩
  · exact ⟨Sum.inl i, (actualActiveFibreSupportLift_piece A₀ D C hPartite e hTrans
      hActive hGen (f i) (hParts i)).symm⟩
  · have ha : copyCarrier a ∈ K := by
      have hMem : copyCarrier a ∈ supportCopies A (core).toRelStructure := ⟨a, rfl⟩
      rw [hSupport] at hMem
      exact hMem
    exact ⟨Sum.inr ⟨copyCarrier a, ha⟩, rfl⟩

/-- A selected Ramsey family on the actual active support stabilizes
the actual processed projection. The relabelled core has exactly the
provided support and inherits its girth bound. -/
theorem actualActiveFibreSupportLift_girth_and_projectedArrow
    (hActive : (S).Nonempty) (hGen : AGenerated A (source).toRelStructure)
    (f : I → StrongSupportEmbedding edges K)
    (hParts : ∀ i x, partK (f i x) = partS x)
    (g : ℕ) (hGirth : GirthGT K g)
    (R : L.withOrder.Symbol) (t : Fin (L.withOrder.arity R) → U)
    (hTuple : (A).rel R t) (hFull : Function.Surjective t)
    (κ : Type w)
    (hArrow : ∀ χ : {E : Set Y // E ∈ K} → κ,
      ∃ i, ∀ x y : {E : Set S // E ∈ edges},
        χ ((f i).mapEdge x) = χ ((f i).mapEdge y)) :
    let lift := fun i => actualActiveFibreSupportLift A₀ D C hPartite e hTrans
      hActive hGen (f i) (hParts i)
    supportCopies A (core).toRelStructure = K ∧
    GirthGT (supportCopies A (core).toRelStructure) g ∧
    ∀ χ : Partite.ProjectedEmbedding A core α → κ,
      ∃ i, ∀ a b : Partite.ProjectedEmbedding A C α,
        χ ((activeInduceProjected A a (projected_mem_activeCarrier A C α a)).comp
          (lift i)) =
        χ ((activeInduceProjected A b (projected_mem_activeCarrier A C α b)).comp
          (lift i)) := by
  let lift := fun i => actualActiveFibreSupportLift A₀ D C hPartite e hTrans
    hActive hGen (f i) (hParts i)
  have hSupport : supportCopies A (core).toRelStructure = K :=
    decorateSupport_supportCopies_of_fullTuple A K partK hTrans R t hTuple hFull
  refine ⟨hSupport, by rw [hSupport]; exact hGirth, ?_⟩
  intro χ
  let named (E : {E : Set Y // E ∈ K}) : Partite.ProjectedEmbedding A core α :=
    ⟨decorateSupport_edgeEmbedding A hTrans E.2,
      fun x => congrArg α (hTrans.part_vertex E.2 x)⟩
  obtain ⟨i, hi⟩ := hArrow (fun E => χ (named E))
  let edge (a : Partite.ProjectedEmbedding A C α) : {E : Set S // E ∈ edges} :=
    ⟨copyCarrier (activeInduceProjected A a (projected_mem_activeCarrier A C α a)).val,
      ⟨(activeInduceProjected A a (projected_mem_activeCarrier A C α a)).val, rfl⟩⟩
  have route (a : Partite.ProjectedEmbedding A C α) :
      named ((f i).mapEdge (edge a)) =
        (activeInduceProjected A a (projected_mem_activeCarrier A C α a)).comp (lift i) := by
    apply Subtype.ext
    apply ordered_embedding_eq_of_sameCopy
    change copyCarrier (decorateSupport_edgeEmbedding A hTrans ((f i).mapEdge (edge a)).2) =
      copyCarrier ((lift i).toEmbedding.comp
        (activeInduceProjected A a (projected_mem_activeCarrier A C α a)).val)
    rw [decorateSupport_edgeCarrier, copyCarrier_comp_eq_image] <;> rfl
  refine ⟨i, ?_⟩
  intro a b
  change χ ((activeInduceProjected A a (projected_mem_activeCarrier A C α a)).comp (lift i)) =
    χ ((activeInduceProjected A b (projected_mem_activeCarrier A C α b)).comp (lift i))
  rw [← route a, ← route b]
  exact hi (edge a) (edge b)

/-- The genuine active attachment of the selected local support witness
preserves the three-member mixed forest invariant and ordinary girth. -/
theorem actualActiveFibreSupportLift_cutoffThree
    {VB : Type v} [Fintype Y]
    (B : RelStructure L.withOrder VB) (hBaseLinear : ALinear A D)
    (baseFamily : Set (Embedding B D))
    (selectedOld : Set (DesignatedCopy B D C baseFamily))
    (hBaseStrong : ∀ q ∈ selectedOld, AStrong A D (copyCarrier q.base))
    (hActive : (S).Nonempty) (hGen : AGenerated A (source).toRelStructure)
    (f : I → StrongSupportEmbedding edges K)
    (hParts : ∀ i x, partK (f i x) = partS x)
    (hSupport : supportCopies A (core).toRelStructure = K)
    (hGirth : GirthGT K 3)
    (hTwoEdges : ∃ a b : Set S, a ∈ edges ∧ b ∈ edges ∧ a ≠ b)
    (hSelectedInj : Function.Injective (fun i => (f i).supportPiece))
    (hMixed : LocalForestThrough
      (mixedOwnerSmall (fun i => (f i).supportPiece)
        (fun edge : {edge : Set Y // edge ∈ K} => edge.1)) 2)
    (testedOld : HypergraphPiece X → Prop)
    (hOld : FiniteMixedForestThrough testedOld 3)
    (hTestA : ∀ a : Embedding A C.toRelStructure,
      testedOld (HypergraphPiece.oneEdge (copyCarrier a)))
    (hTestB : ∀ q ∈ selectedOld, testedOld (bSupportPiece A q.embedding)) :
    let lift := fun i => actualActiveFibreSupportLift A₀ D C hPartite e hTrans
      hActive hGen (f i) (hParts i)
    let attached := Partite.Attachment.attach C S core lift
    let tested : HypergraphPiece (Partite.Attachment.Vertex S (W := Y) (I := I)) → Prop :=
      fun T => (∃ a : Embedding A attached.toRelStructure,
        T = HypergraphPiece.oneEdge (copyCarrier a)) ∨
      ∃ i, ∃ q ∈ selectedOld,
        T = bSupportPiece A (q.transportToStandard lift i).embedding
    FiniteMixedForestThrough tested 3 ∧ GirthGT (supportCopies A attached.toRelStructure) 3 := by
  let lift := fun i => actualActiveFibreSupportLift A₀ D C hPartite e hTrans
    hActive hGen (f i) (hParts i)
  have hPiece (i : I) : bSupportPiece A (lift i).toEmbedding = (f i).supportPiece :=
    actualActiveFibreSupportLift_piece A₀ D C hPartite e hTrans hActive hGen (f i) (hParts i)
  have hInj : Function.Injective (fun i => bSupportPiece A (lift i).toEmbedding) := by
    intro i j h
    apply hSelectedInj
    exact (hPiece i).symm.trans (h.trans (hPiece j))
  have hLocal := actualActiveFibreSupportLift_mixedForest A₀ D C hPartite e hTrans
    hActive hGen f hParts hSupport 2 hMixed
  exact actualPartiteDesignatedAB_forest_and_girth_of_localGeometry
    A (ordered_hereditarilyIrreducible A₀).irreducible B D C hPartite hBaseLinear
    baseFamily selectedOld e (fun a h => ordered_embedding_eq_of_sameCopy a e h)
    hActive core lift hBaseStrong 3 (by decide) (by intro h; omega)
    (Or.inr ⟨hTwoEdges, hInj, hLocal⟩) (by rw [hSupport]; exact hGirth)
    testedOld hOld hTestA hTestB

end ActiveFibre

#print axioms StructuralRamsey.Girth.actualActiveFibreSupportLift
#print axioms StructuralRamsey.Girth.actualActiveFibreSupportLift_piece
#print axioms StructuralRamsey.Girth.actualActiveFibreSupportLift_mixedForest
#print axioms StructuralRamsey.Girth.actualActiveFibreSupportLift_girth_and_projectedArrow
#print axioms StructuralRamsey.Girth.actualActiveFibreSupportLift_cutoffThree

end StructuralRamsey.Girth
