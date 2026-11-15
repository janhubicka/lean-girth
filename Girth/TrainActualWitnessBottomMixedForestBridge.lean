import Girth.TrainActualWitnessBottomForestGeometry
import Girth.ForestActualRecursiveSupport
import Girth.ForestMixedLocalForestBridge
import Girth.ForestToSupremeActualGeometry

set_option autoImplicit false
set_option Elab.async false

/-!
# Honest finite-SET mixed forests give the actual local bottom forest

The forest Ramsey witness promises every SET of at most q distinct
selected complete A-supports and ambient one-edge supports is a
forest. The one-step bottom preservation theorem asks instead for
LocalForestThrough of the TRUE gluing witness OrderOneData.

These are equivalent on a genuinely injective selected family with
at least two different source A-support edges in its target. The
complete selected gluing-support pieces are not abstract surrogate
ones: they are definitionally the full A-support pieces of the
actual embedded source copies. Ambient edge labels are the true
physical carrier subsets and are never pruned.

This supplies a concrete interface from F_t to the one-step bottom
theorem. In particular it does NOT assume the forest property for
an arbitrarily duplicated B-support piece.
-/

namespace StructuralRamsey.Girth
open StructuralRamsey.RelStructure

universe u v

/-- A COMPLETE A-support piece is determined by its vertex carrier:
it contains precisely all ambient A-copies wholly carried by those
vertices. In particular a support-piece injective selected family
has injective vertex images; this matches the genuine checked lower
ForestTailStage input, rather than asking for a second injectivity
certificate. -/
theorem bSupportPiece_eq_of_same_carrier
    {L : RelLanguage.{u}} {UA VB W : Type v}
    (A : RelStructure L UA)
    {B : RelStructure L VB} {R : RelStructure L W}
    (f g : RelStructure.Embedding B R)
    (hCarrier : copyCarrier f = copyCarrier g) :
    bSupportPiece A f = bSupportPiece A g := by
  have hEdges :
      (bSupportPiece A f).edges = (bSupportPiece A g).edges := by
    ext edge
    change
      (∃ a : RelStructure.Embedding A R,
        copyCarrier a = edge ∧ copyCarrier a ⊆ copyCarrier f) ↔
      (∃ a : RelStructure.Embedding A R,
        copyCarrier a = edge ∧ copyCarrier a ⊆ copyCarrier g)
    rw [hCarrier]
  have hCarriers :
      (bSupportPiece A f).carrier = (bSupportPiece A g).carrier :=
    hCarrier
  cases hf : bSupportPiece A f
  cases hg : bSupportPiece A g
  dsimp at hCarriers hEdges
  cases hCarriers
  cases hEdges
  rfl

section ActualWitnessMixedForestBridge

variable {L : RelLanguage.{u}} {UA P X Y I : Type v}
variable (A : RelStructure L UA)
variable (C : StructuralRamsey.Partite.System L P X)
variable (α : UA → P) (R : RelStructure L Y)
variable (f : I → RelStructure.Embedding
  (C.toRelStructure.induce (activeCarrier A C α)) R)
variable {m : ℕ} (U : EdgeTrainLevels (OldACarrierEdge A R) m)

local notation "S" => activeCarrier A C α
local notation "B" => (C.toRelStructure.induce S)
local notation "CoreEdge" => OldACarrierEdge A R
local notation "μBottom" => (⟨0, Nat.zero_lt_succ m⟩ : Fin (m + 1))
local notation "Local" => activeGluingWitnessOrderOneData
  A C α R f U μBottom

private theorem witnessBottomPiece_ext
    {F G : HypergraphPiece Y}
    (hc : F.carrier = G.carrier) (he : F.edges = G.edges) :
    F = G := by
  cases F
  cases G
  dsimp at hc he
  cases hc
  cases he
  rfl

/-- The complete designated gluing piece at the bottom is exactly
the complete intrinsic A-support of f_i, without assuming the local
witness is finite or has full system girth. -/
theorem activeGluingWitness_bottom_piece_designated
    (H : (Local).BottomForestGeometry) (i : I) :
    (Local).bottomForestPiece H (.inl i) = bSupportPiece A (f i) := by
  apply witnessBottomPiece_ext
  · rfl
  · ext s
    constructor
    · rintro ⟨edge, hSub, rfl⟩
      obtain ⟨a, ha⟩ := edge.2
      refine ⟨a, ha.symm, ?_⟩
      rw [← ha]
      exact hSub
    · rintro ⟨a, ha, hSub⟩
      refine ⟨⟨s, ⟨a, ha.symm⟩⟩, ?_, rfl⟩
      change s ⊆ copyCarrier (f i)
      simpa only [ha] using hSub

/-- The one-edge bottom label is exactly the physical singleton
support piece on its whole actual carrier. -/
theorem activeGluingWitness_bottom_piece_edge
    (H : (Local).BottomForestGeometry) (edge : CoreEdge) :
    (Local).bottomForestPiece H (.inr edge) =
      HypergraphPiece.oneEdge edge.1 := by
  apply witnessBottomPiece_ext
  · rfl
  · ext s
    constructor
    · rintro ⟨edge', hEdge, hs⟩
      have heq : edge' = edge := hEdge
      subst edge'
      exact hs.symm
    · intro hs
      have heq : s = edge.1 := hs
      exact ⟨edge, rfl, heq.symm⟩

/-- The whole literal bottom family is the mixed family of selected
complete A-supports and ALL ambient physical A-edge pieces. -/
theorem activeGluingWitness_bottom_pieces_eq_mixed
    (H : (Local).BottomForestGeometry) :
    (Local).bottomForestPiece H =
      mixedOwnerSmall (fun i : I => bSupportPiece A (f i))
        (fun edge : CoreEdge => edge.1) := by
  funext a
  cases a with
  | inl i =>
      exact activeGluingWitness_bottom_piece_designated
        A C α R f U H i
  | inr edge =>
      exact activeGluingWitness_bottom_piece_edge
        A C α R f U H edge

/-- Two distinct A-copies in the source active subsystem ensure every
selected gluing support has at least two distinct physical A-edges.
There is no extra assumption on the number of vertices in a copy. -/
theorem activeGluingWitness_not_oneEdge_of_two_sourceCopies
    (a b : RelStructure.Embedding A B)
    (hDistinct : ¬ SameCopy a b)
    (i : I) :
    ¬ (bSupportPiece A (f i)).IsOneEdge := by
  apply HypergraphPiece.not_isOneEdge_of_twoEdges
    (bSupportPiece A (f i))
    (copyCarrier ((f i).comp a))
    (copyCarrier ((f i).comp b))
  · refine ⟨(f i).comp a, rfl, ?_⟩
    rintro x ⟨u, rfl⟩
    exact ⟨a u, rfl⟩
  · refine ⟨(f i).comp b, rfl, ?_⟩
    rintro x ⟨u, rfl⟩
    exact ⟨b u, rfl⟩
  · intro h
    exact hDistinct (sameCopy_of_comp (f i) h)

/-- Selecting one gluing embedding per actual VERTEX IMAGE suffices
for distinct complete A-support pieces: those pieces remember their
entire vertex carrier, not just their family of A-edges. No A-strongness,
girth, rigidity or extra choice of support-piece labels is needed. -/
theorem activeGluingWitness_supportPiece_injective_of_distinct_images
    (hImages : Function.Injective
      (fun i : I => copyCarrier (f i))) :
    Function.Injective (fun i : I => bSupportPiece A (f i)) := by
  intro i j heq
  apply hImages
  exact congrArg HypergraphPiece.carrier heq

/-- The checked lower stage's selected physical injectivity
already supplies distinct vertex images: two identical carriers
have identical COMPLETE supports. No image-choice axiom
or independent enumeration is required. -/
theorem activeGluingWitness_distinct_images_of_supportPiece_injective
    (hSupports : Function.Injective
      (fun i : I => bSupportPiece A (f i))) :
    Function.Injective (fun i : I => copyCarrier (f i)) := by
  intro i j hCarriers
  apply hSupports
  exact bSupportPiece_eq_of_same_carrier A (f i) (f j) hCarriers

/-- Faithfully pass from the finite SET-based mixed-forest theorem
to the TRUE bottom gluing-witness indexed family at the SAME cutoff q.
No multiset/duplicate-B assumption and no lower q-1 substitution. -/
theorem activeGluingWitness_bottom_localForest_of_finiteMixed
    (H : (Local).BottomForestGeometry)
    (a b : RelStructure.Embedding A B)
    (hDistinct : ¬ SameCopy a b)
    (hCopies : Function.Injective
      (fun i : I => bSupportPiece A (f i)))
    (q : ℕ)
    (hMixed : FiniteMixedForestThrough
      (RelationalMixedSupportTest A f) q) :
    LocalForestThrough ((Local).bottomForestPiece H) q := by
  rw [activeGluingWitness_bottom_pieces_eq_mixed A C α R f U H]
  apply localForestThrough_mixedOwners_of_finiteMixed
    (fun i : I => bSupportPiece A (f i))
    (fun edge : CoreEdge => edge.1)
    hCopies Subtype.val_injective
    (fun i => activeGluingWitness_not_oneEdge_of_two_sourceCopies
      A C α R f a b hDistinct i)
    (RelationalMixedSupportTest A f) q
  · intro i
    exact Or.inl ⟨i, rfl⟩
  · intro edge
    obtain ⟨c, hc⟩ := edge.2
    exact Or.inr ⟨c, congrArg HypergraphPiece.oneEdge hc⟩
  · exact hMixed


end ActualWitnessMixedForestBridge
end StructuralRamsey.Girth
