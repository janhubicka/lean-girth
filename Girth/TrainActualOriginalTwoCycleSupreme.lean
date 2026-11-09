import Girth.TrainActualTwoCycleCoreConnectors
import Girth.TrainTwoCycleOriginalShortSupreme
import Girth.TrainTwoCycleOriginalDesignatedOfLinear
import Girth.TrainTwoCycleMixedActualBridges
import Girth.TrainActualSupremeCutBoundarySupport
import Girth.TrainActualGeometricDesignatedOwnerUnique
import Girth.TrainActualTwoCutDoubleWagonExclusion

set_option autoImplicit false
set_option Elab.async false

/-!
# Original length-two source closure

Physical source labels are retained. The mixed case uses an actual old edge
probe in the original selected copy. The theorem assumes genuine old
SupremeCycleBound q and witness FullSystemGirthGT q. It does not establish
any standalone weakening with only a chosen reduced supreme plan or bridge
alternative: the wagon/wagon exclusion here uses the full witness bound.
-/

namespace StructuralRamsey.Girth
open StructuralRamsey.RelStructure

universe u v
section OriginalTwoCycleSupreme

variable {L : RelLanguage.{u}} {UA VB P X Y I : Type v}
variable (A : RelStructure L UA) (hA : A.Irreducible)
variable (B : RelStructure L VB) (D : RelStructure L P)
variable (C : StructuralRamsey.Partite.System L P X)
variable (family : Set (RelStructure.Embedding B D))
variable (selected : Set (DesignatedCopy B D C family))
variable (e : RelStructure.Embedding A D) (R : RelStructure L Y)
variable (f : I → RelStructure.Embedding
  (C.toRelStructure.induce (activeCarrier A C e.toFunctionEmbedding)) R)
variable {m : ℕ}
variable (T : EdgeTrainLevels (OldACarrierEdge A C.toRelStructure) m)
variable (U : EdgeTrainLevels (OldACarrierEdge A R) m)
variable (hShared : ∀ _i : I, Nonempty (SharedOldACarrierEdge A C.toRelStructure
  (activeCarrier A C e.toFunctionEmbedding)))
variable (hRel : ∀ (ν : Fin (m + 1)) (j : I)
  (p q : SharedOldACarrierEdge A C.toRelStructure
    (activeCarrier A C e.toFunctionEmbedding)),
  T.rel ν p.1 q.1 ↔
    U.rel ν (sharedOldACarrierCoreEmbedding A C.toRelStructure
      (activeCarrier A C e.toFunctionEmbedding) R f j p)
      (sharedOldACarrierCoreEmbedding A C.toRelStructure
        (activeCarrier A C e.toFunctionEmbedding) R f j q))
variable (μ : Fin (m + 1))

local notation "S" => activeCarrier A C e.toFunctionEmbedding
local notation "CoreEdge" => OldACarrierEdge A R
local notation "CoreEmb" =>
  RelStructure.Attachment.coreEmbedding C.toRelStructure S R f
local notation "CoreWagon" => generatedActualASupportTrain_coreWagonEmbedding
  A hA C.toRelStructure S R f T U
  (fun ν j p q h => Iff.mp (hRel ν j p q) h) hShared μ
local notation "Out" => attachedSelectedPictureOrderOneData
  A hA B D C family selected e R f T U hShared μ
local notation "GeomAllowed" => selectedOutputGeometricOwnerAllowed
  A hA B D C family selected e R f T U hShared μ
local notation "CutConnector" => attachedSelectedPicture_cutConnector
  A hA B D C family selected e R f T U hShared hRel μ

local notation "OldEdge" => OldACarrierEdge A C.toRelStructure
local notation "ActualEdge" => OldACarrierEdge A
  (RelStructure.Attachment.attach C.toRelStructure S R f)
local notation "Selected" => {r : DesignatedCopy B D C family // r ∈ selected}
local notation "Std" => RelStructure.Attachment.copyEmbedding C.toRelStructure S R f
local notation "Emb" => sharedOldACarrierCoreEmbedding A C.toRelStructure S R f
local notation "Eqv" => actualAPictureEdgeEquiv A hA C.toRelStructure S R f
local notation "StdEdge" => (fun (i : I) (r : OldEdge) => Eqv
  (physicalStandardEdge (sharedOldACarrierInclusion A C.toRelStructure S) Emb i r))
local notation "CoreActual" => (fun (r : CoreEdge) => Eqv
  (physicalCoreEdge (sharedOldACarrierInclusion A C.toRelStructure S) I r))
local notation "Old" => selectedPictureOrderOneData A B D C family selected T μ
local notation "Wit" => sharedWitnessOrderOneData U μ Emb (Subtype.val : CoreEdge → Set Y)
local notation "Train" => generatedActualASupportTrain A hA C.toRelStructure S R f T U hShared

include hRel

omit hRel in
/-- Two distinct core vertices in an original designated label have an
actual common source edge of THAT label, by the active boundary dichotomy. -/
theorem attachedSelectedPicture_original_designated_core_pair
    (hStrong : ∀ r : RelStructure.Embedding B D, r ∈ family →
      AStrong A D (copyCarrier r))
    (i : I) (r : Selected) (x y : Y) (hxy : x ≠ y)
    (hx : CoreEmb x ∈ (Out).carrier (.inl (i, r)))
    (hy : CoreEmb y ∈ (Out).carrier (.inl (i, r))) :
    ∃ a : ActualEdge, a ∈ (Out).edges (.inl (i, r)) ∧
      CoreEmb x ∈ a.1 ∧ CoreEmb y ∈ a.1 := by
  obtain ⟨u, hu, hux⟩ := hx
  obtain ⟨v, hv, hvy⟩ := hy
  have huS : u ∈ S := RelStructure.Attachment.mem_of_copyMap_eq_inl hux
  have hvS : v ∈ S := RelStructure.Attachment.mem_of_copyMap_eq_inl hvy
  have huv : u ≠ v := by
    intro h
    apply hxy
    apply (CoreEmb).injective
    exact hux.symm.trans ((congrArg (fun z => Std i z) h).trans hvy)
  rcases projectedCopy_activeCarrier_intersection_classify
      A B D C e r.1.base r.1.lift (hStrong r.1.base r.1.base_mem) with
    hSmall | ⟨aB, hBoundary⟩
  · exact (huv (hSmall ⟨hu, huS⟩ ⟨hv, hvS⟩)).elim
  · let a : OldEdge := ⟨copyCarrier (r.1.embedding.comp aB),
      ⟨r.1.embedding.comp aB, rfl⟩⟩
    have ha : a.1 ⊆ copyCarrier r.1.embedding := by
      change copyCarrier (r.1.embedding.comp aB) ⊆ copyCarrier r.1.embedding
      rw [← hBoundary]
      exact Set.inter_subset_left
    have hua : u ∈ a.1 := by
      change u ∈ copyCarrier (r.1.embedding.comp aB)
      rw [← hBoundary]
      exact ⟨hu, huS⟩
    have hva : v ∈ a.1 := by
      change v ∈ copyCarrier (r.1.embedding.comp aB)
      rw [← hBoundary]
      exact ⟨hv, hvS⟩
    refine ⟨StdEdge i a, ?_, ?_, ?_⟩
    · change (StdEdge i a).1 ⊆ (fun z => Std i z) '' copyCarrier r.1.embedding
      rw [actualAPictureEdgeEquiv_standard_carrier]
      rintro z ⟨w, hw, rfl⟩
      exact ⟨w, ha hw, rfl⟩
    · rw [actualAPictureEdgeEquiv_standard_carrier]
      exact ⟨u, hua, hux⟩
    · rw [actualAPictureEdgeEquiv_standard_carrier]
      exact ⟨v, hva, hvy⟩

/-- A witness bridge in the correct standard yields a bridge in the
original designated copy. The old order-one edge probe is essential. -/
theorem attachedSelectedPicture_original_designated_mixed_bridge
    (hOldBound : (Old).Bound)
    (i : I) (r : Selected) (x : Y) (p : Quotient (U.wagonSetoid μ))
    (hx : CoreEmb x ∈ (Out).carrier (.inl (i, r)))
    (hMeet : (Out).Meets (.inl (i, r)) (CoreWagon p))
    (hBridge : (Wit).Bridge (.inl i) x p) :
    (Out).Bridge (.inl (i, r)) (CoreEmb x) (CoreWagon p) := by
  obtain ⟨b, hb, hbp, hxb⟩ := hBridge
  change b ∈ Set.range (Emb i) at hb
  obtain ⟨s, rfl⟩ := hb
  have hImage : StdEdge i s.1 = CoreActual (Emb i s) :=
    congrArg (fun z : ActualAPicturePushoutEdge A C.toRelStructure S R I => Eqv z)
      (physicalStandardEdge_shared
        (sharedOldACarrierInclusion A C.toRelStructure S) Emb i s)
  have hVertex : CoreEmb x ∈ (StdEdge i s.1).1 := by
    rw [hImage, actualAPictureEdgeEquiv_core_carrier]
    exact ⟨x, hxb, rfl⟩
  have hParent : (Out).parent (StdEdge i s.1) = CoreWagon p := by
    rw [hImage]
    change Quotient.mk ((Train).wagonSetoid μ) (CoreActual (Emb i s)) = CoreWagon p
    rw [← generatedActualASupportTrain_coreWagonEmbedding_mk
      A hA C.toRelStructure S R f T U
      (fun ν j a b h => Iff.mp (hRel ν j a b) h) hShared μ (Emb i s)]
    exact congrArg CoreWagon hbp
  obtain ⟨u, hu, hux⟩ := hx
  have hus : u ∈ s.1.1 := by
    rw [actualAPictureEdgeEquiv_standard_carrier] at hVertex
    obtain ⟨v, hv, hvx⟩ := hVertex
    have hvu : v = u := (Std i).injective (hvx.trans hux.symm)
    exact hvu ▸ hv
  have hEdgeMeet : (Out).Meets
      (attachedSelectedPictureLabel A hA B D C family selected e R f i (.inr s.1))
      (CoreWagon p) := ⟨StdEdge i s.1, rfl, hParent⟩
  obtain ⟨a, hCopyOld, hEdgeOld, haOut⟩ := attachedSelectedPicture_block_pullback
    A hA B D C family selected e R f T U hShared μ hRel
    i (.inl r) (.inr s.1) (CoreWagon p) hMeet hEdgeMeet
  have hOldBridge : (Old).Bridge (.inl r) u ((Old).parent a) :=
    (Old).bridge_of_incident_edge hOldBound (.inl r) u ((Old).parent a)
      hu hCopyOld s.1
      (by obtain ⟨b, hb, hp⟩ := hEdgeOld; have hbs : b = s.1 := hb; exact hbs ▸ hp)
      hus
  obtain ⟨b, hb, hba, hub⟩ := hOldBridge
  refine ⟨StdEdge i b, ?_, ?_, ?_⟩
  · exact (attachedSelectedPicture_edges A hA B D C family selected e R f
      T U hShared μ i (.inl r) (StdEdge i b)).mpr ⟨b, hb, rfl⟩
  · have hRelOld : T.rel μ b a := Quotient.exact hba
    have hRelOut : (Train).rel μ (StdEdge i b) (StdEdge i a) :=
      (generatedActualASupportTrain_restrict_standard
        A hA C.toRelStructure S R f T U hRel hShared μ i b a).mpr hRelOld
    exact (Quotient.sound hRelOut).trans haOut
  · change CoreEmb x ∈ (StdEdge i b).1
    rw [actualAPictureEdgeEquiv_standard_carrier]
    exact ⟨u, hub, hux⟩

/-- Every acceptable ORIGINAL source two-cycle with two geometric cuts has
an actual simultaneous supreme plan. VV uses its own designated boundary
edge; mixed uses the witness bridge and the old physical edge probe; WW
is excluded by the witness. No source label is replaced by an owner label. -/
theorem attachedSelectedPicture_original_two_cycle_supreme_of_owner_bridges
    [Finite UA]
    (q : ℕ) (hq : 1 ≤ q)
    (hStrong : ∀ r : RelStructure.Embedding B D, r ∈ family →
      AStrong A D (copyCarrier r))
    (hTwoCopies : ∀ r : Selected, ∃ a b : OldEdge,
      a ≠ b ∧ a.1 ⊆ copyCarrier r.1.embedding ∧ b.1 ⊆ copyCarrier r.1.embedding)
    (hOldSupreme : (Old).SupremeCycleBound q)
    (K : (Out).BigCycle 2) (hAccept : K.Acceptable)
    (hLinear : (Out).LinearPretrain)
    (owner : Fin 2 → I ⊕ CoreEdge)
    (hAllowed : ∀ j, GeomAllowed (K.label j) (owner j))
    (hTwo : cyclicOwnerChanges owner = 2)
    (_hOrder : K.twiceOrder ≤ 2 * q)
    (hMixedBridges : ∀ (x : Y) (p : Quotient (U.wagonSetoid μ)),
      ((K.connector 0 = Sum.inl (CoreEmb x) ∧ K.connector 1 = Sum.inr (CoreWagon p)) ∨
       (K.connector 0 = Sum.inr (CoreWagon p) ∧ K.connector 1 = Sum.inl (CoreEmb x))) →
      (∀ k, (Wit).Incident (owner k) (Sum.inl x)) →
      (∀ k, (Wit).Incident (owner k) (Sum.inr p)) →
      ∀ k, (Wit).Bridge (owner k) x p)
    (hNoWW : ∀ (p t : Quotient (U.wagonSetoid μ)),
      K.connector 0 = Sum.inr (CoreWagon p) →
      K.connector 1 = Sum.inr (CoreWagon t) → False) : K.HasSimultaneousSupreme := by
  classical
  obtain ⟨target, hTarget⟩ := K.two_has_designated_of_linear Out hAccept hLinear
  obtain ⟨i, r, hLabel⟩ : ∃ (i : I) (r : Selected), K.label target = Sum.inl (i, r) := by
    cases h : K.label target with
    | inl ir => exact ⟨ir.1, ir.2, rfl⟩
    | inr a => simp [OrderOneData.designated, h] at hTarget
  have hInc (k : Fin 2) : (Out).Incident (.inl (i, r)) (K.connector k) := by
    rw [← hLabel]
    exact K.two_every_label_incident_every_connector Out target k
  have hCuts (k : Fin 2) : owner k ≠ owner (cyclicSucc k) := by
    let j : Fin (cyclicOwnerChanges owner) := ⟨k.val, by omega⟩
    have hIndex : cyclicOwnerCutIndex owner j = k :=
      Fin.ext (cyclicOwnerCutIndex_val_eq_of_source_two owner hTwo j)
    simpa only [hIndex] using cyclicOwnerCutIndex_is_change owner j
  have hOwner : owner target = Sum.inl i := by
    obtain ⟨j, hj⟩ := attachedSelectedPicture_geometric_designated_has_standard_owner
      A hA B D C family selected e R f T U hShared μ K owner hAllowed target i r hLabel
    have hij : i = j := attachedSelectedPicture_designated_occurrence_owner_eq
      A hA B D C family selected e R f T U hShared μ
      (fun r => hStrong r.1.base r.1.base_mem) hTwoCopies
      K owner hAllowed target i j r hLabel hj
    exact hj.trans (congrArg Sum.inl hij.symm)
  rcases attachedSelectedPicture_two_cycle_core_connector_cases
      A hA B D C family selected e R f T U hShared hRel μ
      K owner hAllowed hTwo with hVV | hVW | hWW
  · obtain ⟨x, y, h0, h1⟩ := hVV
    have hxy : x ≠ y := by
      intro heq
      have hC : K.connector 0 = K.connector 1 := by rw [h0, h1, heq]
      exact (by decide : (0 : Fin 2) ≠ 1) (K.connector_injective hC)
    have hx : CoreEmb x ∈ (Out).carrier (.inl (i, r)) := by
      simpa only [h0, OrderOneData.Incident] using hInc 0
    have hy : CoreEmb y ∈ (Out).carrier (.inl (i, r)) := by
      simpa only [h1, OrderOneData.Incident] using hInc 1
    obtain ⟨a, ha, hxa, hya⟩ := attachedSelectedPicture_original_designated_core_pair
      A hA B D C family selected e R f T U hShared μ hStrong i r x y hxy hx hy
    apply K.hasSimultaneousSupreme_of_hasSupremeAt Out target
    apply K.two_hasSupremeAt_of_common_short Out hAccept hLinear target hTarget a
    · simpa only [hLabel] using ha
    · intro k
      fin_cases k
      · change (Out).Incident (.inr a) (K.connector 0)
        rw [h0]
        exact hxa
      · change (Out).Incident (.inr a) (K.connector 1)
        rw [h1]
        exact hya
  · obtain ⟨x, p, hMixed⟩ := hVW
    have hV : ∀ k : Fin 2, (Wit).Incident (owner k) (Sum.inl x) := by
      rcases hMixed with h | h
      · have hs := attachedSelectedPicture_geometric_vertex_cut_target_incidence
          A hA B D C family selected e R f T U hShared μ
          K owner hAllowed 0 x h.1 (hCuts 0)
        intro k; fin_cases k
        · exact hs.1
        · simpa [cyclicSucc] using hs.2
      · have hs := attachedSelectedPicture_geometric_vertex_cut_target_incidence
          A hA B D C family selected e R f T U hShared μ
          K owner hAllowed 1 x h.2 (hCuts 1)
        intro k; fin_cases k
        · simpa [cyclicSucc] using hs.2
        · exact hs.1
    have hW : ∀ k : Fin 2, (Wit).Incident (owner k) (Sum.inr p) := by
      rcases hMixed with h | h
      · have hs := attachedSelectedPicture_geometric_wagon_cut_target_incidence
          A hA B D C family selected e R f T U hShared hRel μ
          K owner hAllowed 1 p h.2 (hCuts 1)
        intro k; fin_cases k
        · simpa [cyclicSucc] using hs.2
        · exact hs.1
      · have hs := attachedSelectedPicture_geometric_wagon_cut_target_incidence
          A hA B D C family selected e R f T U hShared hRel μ
          K owner hAllowed 0 p h.1 (hCuts 0)
        intro k; fin_cases k
        · exact hs.1
        · simpa [cyclicSucc] using hs.2
    have hBridge : (Wit).Bridge (.inl i) x p := by
      have h := hMixedBridges x p hMixed hV hW target
      simpa only [hOwner] using h
    have hx : CoreEmb x ∈ (Out).carrier (.inl (i, r)) := by
      rcases hMixed with h | h
      · simpa only [h.1, OrderOneData.Incident] using hInc 0
      · simpa only [h.2, OrderOneData.Incident] using hInc 1
    have hp : (Out).Meets (.inl (i, r)) (CoreWagon p) := by
      rcases hMixed with h | h
      · simpa only [h.2, OrderOneData.Incident] using hInc 1
      · simpa only [h.1, OrderOneData.Incident] using hInc 0
    have hOldBound : (Old).Bound := (Old).bound_of_localPieceSystemBound
      ((Old).localPieceSystemBound_of_supremeCycleBound 1
        (by intro n Z hA hO; exact hOldSupreme n Z hA (by omega)))
    obtain ⟨a, ha, hap, hxa⟩ := attachedSelectedPicture_original_designated_mixed_bridge
      A hA B D C family selected e R f T U hShared hRel μ
      hOldBound i r x p hx hp hBridge
    apply K.hasSimultaneousSupreme_of_hasSupremeAt Out target
    apply K.two_hasSupremeAt_of_common_short Out hAccept hLinear target hTarget a
    · simpa only [hLabel] using ha
    · have hAV : (Out).Incident (.inr a) (Sum.inl (CoreEmb x)) := hxa
      have hAW : (Out).Incident (.inr a) (Sum.inr (CoreWagon p)) := ⟨a, rfl, hap⟩
      intro k
      rcases hMixed with h | h
      · fin_cases k
        · simpa [h.1] using hAV
        · simpa [h.2] using hAW
      · fin_cases k
        · simpa [h.1] using hAW
        · simpa [h.2] using hAV
  · obtain ⟨p, t, h0, h1⟩ := hWW
    exact (hNoWW p t h0 h1).elim

/-- The ordinary witness induction bound discharges the two explicit local
obligations above. No output system-girth or source supremeness is assumed. -/
theorem attachedSelectedPicture_original_two_cycle_supreme
    [Finite UA]
    (q : ℕ) (hq : 1 ≤ q)
    (hStrong : ∀ r : RelStructure.Embedding B D, r ∈ family →
      AStrong A D (copyCarrier r))
    (hTwoCopies : ∀ r : Selected, ∃ a b : OldEdge,
      a ≠ b ∧ a.1 ⊆ copyCarrier r.1.embedding ∧ b.1 ⊆ copyCarrier r.1.embedding)
    (hOldSupreme : (Old).SupremeCycleBound q)
    (hWitness : (Wit).FullSystemGirthGT q)
    (K : (Out).BigCycle 2) (hAccept : K.Acceptable)
    (hLinear : (Out).LinearPretrain)
    (owner : Fin 2 → I ⊕ CoreEdge)
    (hAllowed : ∀ j, GeomAllowed (K.label j) (owner j))
    (hTwo : cyclicOwnerChanges owner = 2)
    (hOrder : K.twiceOrder ≤ 2 * q) : K.HasSimultaneousSupreme := by
  apply attachedSelectedPicture_original_two_cycle_supreme_of_owner_bridges
    A hA B D C family selected e R f T U hShared hRel μ
    q hq hStrong hTwoCopies hOldSupreme K hAccept hLinear owner hAllowed hTwo hOrder
  · intro x p _hMixed hV hW
    have hOwnerNe : owner 0 ≠ owner 1 := by
      let j : Fin (cyclicOwnerChanges owner) := ⟨0, by omega⟩
      have hIndex : cyclicOwnerCutIndex owner j = (0 : Fin 2) := by
        apply Fin.ext
        exact cyclicOwnerCutIndex_val_eq_of_source_two owner hTwo j
      simpa [hIndex, cyclicSucc] using cyclicOwnerCutIndex_is_change owner j
    have hBound : (Wit).Bound := (Wit).orderOneBound_of_fullSystemGirth_positive hq hWitness
    obtain ⟨hB0, hB1⟩ := (Wit).both_bridges hBound (owner 0) (owner 1)
      x p hOwnerNe (hV 0) (hV 1) (hW 0) (hW 1)
    intro k
    fin_cases k
    · exact hB0
    · exact hB1
  · intro p t h0 h1
    have hFour : K.twiceOrder = 4 := by
      simp [OrderOneData.BigCycle.twiceOrder, Fin.sum_univ_two,
        cyclicSucc, OrderOneData.connectorKind, twiceOccurrenceWeight, h0, h1]
    have hq2 : 2 ≤ q := by omega
    apply attachedSelectedPicture_two_cut_double_wagon_absurd_of_witness
      A hA B D C family selected e R f T U hShared hRel μ
      K owner hAllowed hTwo ?_ hWitness hq2
    intro j
    generalize hk : cyclicOwnerCutIndex owner j = k
    fin_cases k
    · exact ⟨CoreWagon p, h0⟩
    · exact ⟨CoreWagon t, h1⟩

end OriginalTwoCycleSupreme
end StructuralRamsey.Girth
