import Girth.ForestToSupremeBottom
import Girth.ForestToSupremeCycle
import Girth.TrainSelectedPictureTwoStandard
import Girth.ForestActualRecursiveSupport

/-!
# Actual selected-picture geometry at the bottom train coordinate

At level zero wagon equality is physical edge equality, by the train's
bottom axiom. Every actual A-edge is nontrivial when A has two vertices,
and ambient A-linearity is precisely physical edge linearity. These facts
instantiate the forest-to-supreme geometry without any cycle assumption.

The physical bottom pieces are identified with complete designated
B-support pieces and actual one-edge A pieces. The last theorem carefully
requires distinct physical designated pieces, and excludes the one-edge
target case before combining their labels with ambient edge labels.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v

/-- At the bottom level wagon linearity follows from physical edge
linearity and injectivity of the edge-to-wagon map. -/
theorem OrderOneData.BottomForestGeometry.linearPretrain
    {V E Q W : Type v} (O : OrderOneData V E Q W)
    (H : O.BottomForestGeometry) : O.LinearPretrain := by
  refine ⟨H.edge_linear, ?_⟩
  intro p q hpq x hx y hy
  obtain ⟨e, hep, hxe⟩ := hx.1
  obtain ⟨f, hfq, hxf⟩ := hx.2
  obtain ⟨e', he'p, hye'⟩ := hy.1
  obtain ⟨f', hf'q, hyf'⟩ := hy.2
  have hee' : e = e' := H.parent_injective (hep.trans he'p.symm)
  have hff' : f = f' := H.parent_injective (hfq.trans hf'q.symm)
  subst e'
  subst f'
  have hef : e ≠ f := by
    intro h
    exact hpq (hep.symm.trans ((congrArg O.parent h).trans hfq))
  exact H.edge_linear e f hef ⟨hxe, hxf⟩ ⟨hye', hyf'⟩

variable {L : RelLanguage.{u}} {UA VB P X : Type v}
variable (A : RelStructure L UA) (B : RelStructure L VB)
variable (D : RelStructure L P) (C : StructuralRamsey.Partite.System L P X)
variable (family : Set (RelStructure.Embedding B D))
variable (selected : Set (DesignatedCopy B D C family))
variable {m : ℕ} (T : EdgeTrainLevels (OldACarrierEdge A C.toRelStructure) m)

local notation "O" => selectedPictureOrderOneData A B D C family selected T 0
local notation "Copy" => {q : DesignatedCopy B D C family // q ∈ selected}
local notation "Edge" => OldACarrierEdge A C.toRelStructure

/-- The actual bottom incidence record satisfies all physical hypotheses
of the forest-to-supreme conversion. -/
theorem selectedPicture_bottomForestGeometry [Nontrivial UA]
    (hLinear : ALinear A C.toRelStructure) : (O).BottomForestGeometry where
  edge_subset := by
    intro a edge hEdge
    cases a with
    | inl q => exact hEdge
    | inr edge' =>
        have hEq : edge = edge' := hEdge
        subst edge'
        exact Set.Subset.rfl
  edge_nontrivial := by
    intro edge
    obtain ⟨a, ha⟩ := edge.2
    change edge.1.Nontrivial
    rw [ha]
    obtain ⟨u, v, huv⟩ := exists_pair_ne UA
    exact ⟨a u, ⟨u, rfl⟩, a v, ⟨v, rfl⟩,
      fun h => huv (a.injective h)⟩
  edge_linear := by
    intro edge edge' hne
    obtain ⟨a, ha⟩ := edge.2
    obtain ⟨b, hb⟩ := edge'.2
    have hCopies : ¬ SameCopy a b := by
      intro h
      apply hne
      exact Subtype.ext (ha.trans (h.trans hb.symm))
    change (edge.1 ∩ edge'.1).Subsingleton
    rw [ha, hb]
    exact hLinear a b hCopies
  parent_injective := by
    intro edge edge' hEq
    exact (T.bottom edge edge').mp (Quotient.exact hEq)

private theorem bottomActualPiece_ext
    {F G : HypergraphPiece X}
    (hc : F.carrier = G.carrier) (he : F.edges = G.edges) : F = G := by
  cases F
  cases G
  dsimp at hc he
  cases hc
  cases he
  rfl

/-- A designated bottom piece is its full relational B-support. -/
theorem selectedPicture_bottom_piece_designated
    (H : (O).BottomForestGeometry) (q : Copy) :
    (O).bottomForestPiece H (.inl q) = bSupportPiece A q.1.embedding := by
  apply bottomActualPiece_ext
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
      change s ⊆ copyCarrier q.1.embedding
      simpa only [ha] using hSub

/-- An ambient edge label is the actual one-edge piece on its carrier. -/
theorem selectedPicture_bottom_piece_edge
    (H : (O).BottomForestGeometry) (edge : Edge) :
    (O).bottomForestPiece H (.inr edge) = HypergraphPiece.oneEdge edge.1 := by
  apply bottomActualPiece_ext
  · rfl
  · ext s
    constructor
    · rintro ⟨edge', hEdge, hs⟩
      have hEq : edge' = edge := hEdge
      subst edge'
      exact hs.symm
    · intro hs
      have hEq : s = edge.1 := hs
      exact ⟨edge, rfl, hEq.symm⟩

/-- The physical bottom-piece family is exactly the mixed family already
used by the finite-set forest bridge. -/
theorem selectedPicture_bottom_pieces_eq_mixed
    (H : (O).BottomForestGeometry) :
    (O).bottomForestPiece H =
      mixedOwnerSmall (fun q : Copy => bSupportPiece A q.1.embedding)
        (fun edge : Edge => edge.1) := by
  funext a
  cases a with
  | inl q => exact selectedPicture_bottom_piece_designated A B D C family selected T H q
  | inr edge => exact selectedPicture_bottom_piece_edge A B D C family selected T H edge

/-- A designated copy is determined by its actual picture embedding. Its
base projection is then determined pointwise, not chosen independently. -/
theorem actualDesignatedCopy_embedding_injective :
    Function.Injective (fun q : DesignatedCopy B D C family => q.embedding) := by
  intro q r hEmbedding
  have hBase : q.base = r.base := by
    apply Embedding.ext
    intro b
    calc
      q.base b = C.part (q.embedding b) := (q.projects b).symm
      _ = C.part (r.embedding b) :=
        congrArg C.part (congrArg (fun f : Embedding B C.toRelStructure => f b) hEmbedding)
      _ = r.base b := r.projects b
  cases q with
  | mk qb qmem qlift =>
      cases r with
      | mk rb rmem rlift =>
          dsimp at hBase hEmbedding
          cases hBase
          have hLift : qlift = rlift := Subtype.ext hEmbedding
          cases hLift
          rfl

/-- Rigidity of the source on its image turns distinct designated labels
into distinct physical support pieces. Ordered finite B supplies this
rigidity through `ordered_embedding_eq_of_sameCopy`. -/
theorem selectedPicture_designatedSupports_injective_of_rigid
    (hRigid : ∀ b c : Embedding B C.toRelStructure, SameCopy b c → b = c) :
    Function.Injective (fun q : Copy => bSupportPiece A q.1.embedding) := by
  intro q r hPieces
  apply Subtype.ext
  apply actualDesignatedCopy_embedding_injective B D C family
  apply hRigid
  exact congrArg HypergraphPiece.carrier hPieces

/-- In the manuscript's finite ordered setting, no separate rigidity
hypothesis or normalization of designated B-embedding labels is needed. -/
theorem selectedPicture_designatedSupports_injective_ordered
    (A₀ : RelStructure L.withOrder UA) (B₀ : RelStructure L VB)
    [LinearOrder VB] [Finite VB]
    (D₀ : RelStructure L.withOrder P)
    (C₀ : StructuralRamsey.Partite.System L.withOrder P X)
    (family₀ : Set (Embedding B₀.ordered D₀))
    (selected₀ : Set (DesignatedCopy B₀.ordered D₀ C₀ family₀)) :
    Function.Injective (fun q : {q : DesignatedCopy B₀.ordered D₀ C₀ family₀ //
        q ∈ selected₀} => bSupportPiece A₀ q.1.embedding) := by
  apply selectedPicture_designatedSupports_injective_of_rigid
    A₀ B₀.ordered D₀ C₀ family₀ selected₀
  intro b c h
  exact ordered_embedding_eq_of_sameCopy b c h

/-- Two distinct actual source A-copies remain two distinct support edges
in every designated B-copy. No source strongness premise is required. -/
theorem actualBSupport_notOneEdge_of_two_sourceCopies
    (a b : Embedding A B) (hne : ¬ SameCopy a b)
    (f : Embedding B C.toRelStructure) : ¬ (bSupportPiece A f).IsOneEdge := by
  apply HypergraphPiece.not_isOneEdge_of_twoEdges
    (bSupportPiece A f) (copyCarrier (f.comp a)) (copyCarrier (f.comp b))
  · refine ⟨f.comp a, rfl, ?_⟩
    rintro x ⟨u, rfl⟩
    exact ⟨a u, rfl⟩
  · refine ⟨f.comp b, rfl, ?_⟩
    rintro x ⟨u, rfl⟩
    exact ⟨b u, rfl⟩
  · intro h
    exact hne (sameCopy_of_comp f h)

/-- Transport the genuine mixed finite-set forest bound to the actual
bottom labels. Distinct multi-edge designated copies must remain distinct;
no arbitrary duplication or hereditary deletion is invoked. -/
theorem selectedPicture_bottom_localForest_of_finiteMixed
    (H : (O).BottomForestGeometry)
    (hCopies : Function.Injective (fun q : Copy => bSupportPiece A q.1.embedding))
    (hNotOne : ∀ q : Copy, ¬ (bSupportPiece A q.1.embedding).IsOneEdge)
    (q : ℕ)
    (hForest : FiniteMixedForestThrough
      (RelationalMixedSupportTest A (fun q : Copy => q.1.embedding)) q) :
    LocalForestThrough ((O).bottomForestPiece H) q := by
  rw [selectedPicture_bottom_pieces_eq_mixed A B D C family selected T H]
  apply localForestThrough_mixedOwners_of_finiteMixed
    (fun q : Copy => bSupportPiece A q.1.embedding) (fun edge : Edge => edge.1)
    hCopies Subtype.val_injective hNotOne
    (RelationalMixedSupportTest A (fun q : Copy => q.1.embedding)) q
  · intro copy
    exact Or.inl ⟨copy, rfl⟩
  · intro edge
    obtain ⟨a, ha⟩ := edge.2
    exact Or.inr ⟨a, congrArg HypergraphPiece.oneEdge ha⟩
  · exact hForest

/-- The actual multi-edge target case needs only source rigidity and two
distinct A-copies to discharge all label-injectivity side conditions. -/
theorem selectedPicture_bottom_localForest_of_rigid_multiEdge
    (H : (O).BottomForestGeometry)
    (hRigid : ∀ b c : Embedding B C.toRelStructure, SameCopy b c → b = c)
    (a b : Embedding A B) (hne : ¬ SameCopy a b)
    (q : ℕ)
    (hForest : FiniteMixedForestThrough
      (RelationalMixedSupportTest A (fun q : Copy => q.1.embedding)) q) :
    LocalForestThrough ((O).bottomForestPiece H) q := by
  apply selectedPicture_bottom_localForest_of_finiteMixed A B D C family selected T H
  · exact selectedPicture_designatedSupports_injective_of_rigid A B D C family selected hRigid
  · intro copy
    exact actualBSupport_notOneEdge_of_two_sourceCopies A B C a b hne copy.1.embedding
  · exact hForest

/-- The conversion applied to an actual selected-picture bottom cycle.
The forest budget is a bound on its occurrence length; a separate
segmentation argument must justify that budget in an order-bound use. -/
theorem selectedPicture_bottom_cycle_supreme_of_mixedForest
    [Nontrivial UA] (hLinear : ALinear A C.toRelStructure)
    (hRigid : ∀ b c : Embedding B C.toRelStructure, SameCopy b c → b = c)
    (a b : Embedding A B) (hne : ¬ SameCopy a b)
    (q : ℕ)
    (hForest : FiniteMixedForestThrough
      (RelationalMixedSupportTest A (fun q : Copy => q.1.embedding)) q)
    {n : ℕ} (cycle : (O).BigCycle n) (hAccept : cycle.Acceptable)
    (hLength : n ≤ q) : cycle.HasSimultaneousSupreme := by
  let H := selectedPicture_bottomForestGeometry A B D C family selected T hLinear
  exact cycle.hasSimultaneousSupreme_of_bottomLocalForest (O) H hAccept q
    (selectedPicture_bottom_localForest_of_rigid_multiEdge
      A B D C family selected T H hRigid a b hne q hForest) hLength

end StructuralRamsey.Girth
