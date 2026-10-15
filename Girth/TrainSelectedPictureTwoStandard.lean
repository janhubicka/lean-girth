import Girth.TrainActualTwoStandardDesignatedBlock

/-!
# Two-standard obstruction for a selected designated family

Only the prescribed selected B-copies are designated labels. Physical A-edges
and old wagon quotients are unchanged. In particular, no system-girth bound
for all projected lifts is inferred from a bound for the selected family.

A generic four-occurrence argument identifies the wagon of a retained block
with that of a long pair. The actual attachment geometry pulls back the same
physical endpoints and absorbs old pair edges into the core. Two applications,
followed by the old-core-old generator chain, give the obstruction.

Source and witness FULL system-girth bounds are hypotheses. Witness-copy
memberships, local-piece bounds, old frames and all label inequalities are
not hypotheses. Shared-train reflection and genuine source block incidences
remain explicit. Recovering those incidences from a full output-cycle record,
and general cycle transfer, are separate obligations.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v

/-- The four-occurrence argument is independent of the chosen copy index type.
A block and a pair of incident edges cannot use different wagons if no edge
joins the endpoints and every designated copy containing both supplies one.
Even distinctness of the two retained labels follows from these hypotheses. -/
theorem OrderOneData.block_parent_eq_of_no_pairEdge
    {V E Q W : Type v} (D : OrderOneData V E Q W)
    (hFull : D.FullSystemGirthGT 2) (hCompat : D.CopyEdgeCarrierCompatible)
    (a b : Q ⊕ E) (e f : E) (p : W) (x y : V)
    (hxy : x ≠ y)
    (ha : D.Meets a p) (hb : D.Meets b p)
    (hxB : x ∈ D.carrier b) (hxE : x ∈ D.edgeCarrier e)
    (hyF : y ∈ D.edgeCarrier f) (hyA : y ∈ D.carrier a)
    (hf : D.parent f = D.parent e) (hNoPair : ¬ D.PairEdge x y)
    (hBoundary : ∀ q : Q, x ∈ D.copyCarrier q → y ∈ D.copyCarrier q →
      D.PairEdge x y) : p = D.parent e := by
  classical
  by_contra hpq
  have hab : a ≠ b := by
    intro h
    have hxA : x ∈ D.carrier a := h.symm ▸ hxB
    cases a with
    | inl q => exact hNoPair (hBoundary q hxA hyA)
    | inr edge => exact hNoPair ⟨edge, hxA, hyA⟩
  have hef : e ≠ f := by
    intro h
    exact hNoPair ⟨e, hxE, h.symm ▸ hyF⟩
  let F := OrderOneData.FourWagonFrame.of_distinct_wagons
    D a b e f p (D.parent e) x y hab hef hpq hxy
    ha hb hxB hxE rfl hf hyF hyA
  exact hNoPair (F.pairEdge_of_system_bound_and_boundary D hFull hCompat hBoundary)

section SelectedPicture

variable {L : RelLanguage.{u}} {UA VB P X Y I : Type v}
variable (A : RelStructure L UA) (B : RelStructure L VB)
variable (D : RelStructure L P) (C : StructuralRamsey.Partite.System L P X)
variable (family : Set (RelStructure.Embedding B D))
variable (selected : Set (DesignatedCopy B D C family))
variable {m : ℕ} (T : EdgeTrainLevels (OldACarrierEdge A C.toRelStructure) m)
variable (μ : Fin (m + 1))

/-- The old incidence model with precisely the selected designated labels. -/
def selectedPictureOrderOneData :
    OrderOneData X (OldACarrierEdge A C.toRelStructure)
      {q : DesignatedCopy B D C family // q ∈ selected}
      (Quotient (T.wagonSetoid μ)) where
  edgeCarrier := fun edge => edge.1
  copyCarrier := fun q => copyCarrier q.1.embedding
  copyEdges := fun q => {edge | edge.1 ⊆ copyCarrier q.1.embedding}
  parent := Quotient.mk (T.wagonSetoid μ)

local notation "O" => selectedPictureOrderOneData A B D C family selected T μ
local notation "OldEdge" => OldACarrierEdge A C.toRelStructure
local notation "Label" => ({q : DesignatedCopy B D C family // q ∈ selected} ⊕ OldEdge)

/-- Restricting designated labels does not change source-edge coherence. -/
theorem selectedPictureOrderOneData_copyEdgeCarrierCompatible :
    (O).CopyEdgeCarrierCompatible := by
  intro q edge hEdge
  exact hEdge

variable (e : RelStructure.Embedding A D) (R : RelStructure L Y)
variable (f : I → RelStructure.Embedding
  (C.toRelStructure.induce (activeCarrier A C e.toFunctionEmbedding)) R)

local notation "S" => activeCarrier A C e.toFunctionEmbedding
local notation "Shared" => SharedOldACarrierEdge A C.toRelStructure S
local notation "Vertex" => RelStructure.Attachment.Vertex S (W := Y) (I := I)
local notation "Std" => RelStructure.Attachment.copyEmbedding C.toRelStructure S R f
local notation "Emb" => sharedOldACarrierCoreEmbedding A C.toRelStructure S R f
local notation "CoreCar" => attachedCoreAEdgeCarrier A C.toRelStructure S R f

/-- The retained labels belong to the selected family; all physical endpoints
are pulled back along the actual standard embedding. No old frame or label
inequality is assumed. -/
theorem selectedPicture_block_rel_shared_of_no_core_pair
    (i : I)
    (hStrong : ∀ b : RelStructure.Embedding B D, b ∈ family →
      AStrong A D (copyCarrier b))
    (hActive : AStrong A C.toRelStructure S) (hFull : (O).FullSystemGirthGT 2)
    (a b : Label) (r : OldEdge) (sx sy : Shared) (x y : Vertex)
    (hxy : x ≠ y)
    (ha : (O).Meets a ((O).parent r)) (hb : (O).Meets b ((O).parent r))
    (hLong : T.rel μ sx.1 sy.1)
    (hyA : y ∈ (fun z : X => Std i z) '' (O).carrier a)
    (hxB : x ∈ (fun z : X => Std i z) '' (O).carrier b)
    (hxS : x ∈ attachedOldAEdgeCarrier A C.toRelStructure S R f i sx.1)
    (hyS : y ∈ attachedOldAEdgeCarrier A C.toRelStructure S R f i sy.1)
    (hNoEdge : ¬ ∃ edge : OldACarrierEdge A R, x ∈ CoreCar edge ∧ y ∈ CoreCar edge) :
    T.rel μ r sx.1 := by
  change x ∈ (fun z : X => Std i z) '' sx.1.1 at hxS
  change y ∈ (fun z : X => Std i z) '' sy.1.1 at hyS
  obtain ⟨u, hu, hux⟩ := hxS
  obtain ⟨w, hw, hwy⟩ := hyS
  have huw : u ≠ w := by
    intro h
    exact hxy (hux.symm.trans ((congrArg (fun z : X => Std i z) h).trans hwy))
  have huB : u ∈ (O).carrier b := by
    obtain ⟨z, hz, hzx⟩ := hxB
    exact (Std i).injective (hzx.trans hux.symm) ▸ hz
  have hwA : w ∈ (O).carrier a := by
    obtain ⟨z, hz, hzy⟩ := hyA
    exact (Std i).injective (hzy.trans hwy.symm) ▸ hz
  have hNoPair : ¬ (O).PairEdge u w := by
    rintro ⟨edge, huEdge, hwEdge⟩
    let shared : Shared := ⟨edge, oldACarrier_subset_of_two_mem_aStrong
      A C.toRelStructure S hActive edge u w huw huEdge hwEdge (sx.2 hu) (sy.2 hw)⟩
    have huCore : Std i u ∈ CoreCar (Emb i shared) :=
      Eq.mp (congrArg (fun carrier => Std i u ∈ carrier)
        (attachedSharedAEdgeCarrier_eq A C.toRelStructure S R f i shared))
        ⟨u, huEdge, rfl⟩
    have hwCore : Std i w ∈ CoreCar (Emb i shared) :=
      Eq.mp (congrArg (fun carrier => Std i w ∈ carrier)
        (attachedSharedAEdgeCarrier_eq A C.toRelStructure S R f i shared))
        ⟨w, hwEdge, rfl⟩
    exact hNoEdge ⟨Emb i shared,
      Eq.mp (congrArg (fun z => z ∈ CoreCar (Emb i shared)) hux) huCore,
      Eq.mp (congrArg (fun z => z ∈ CoreCar (Emb i shared)) hwy) hwCore⟩
  have hParent : (O).parent sy.1 = (O).parent sx.1 := (Quotient.sound hLong).symm
  have hEq : (O).parent r = (O).parent sx.1 :=
    OrderOneData.block_parent_eq_of_no_pairEdge O hFull
      (selectedPictureOrderOneData_copyEdgeCarrierCompatible A B D C family selected T μ)
      a b sx.1 sy.1 ((O).parent r) u w huw ha hb huB hu hw hwA hParent hNoPair
      (fun q hxCopy hyCopy => standardPictureOrderOneData_pairEdge_of_two_active
        A B D C family T μ hStrong e q.1 u w huw hxCopy hyCopy (sx.2 hu) (sy.2 hw))
  exact Quotient.exact hEq

variable (U : EdgeTrainLevels (OldACarrierEdge A R) m)
local notation "Witness" => sharedWitnessOrderOneData U μ Emb CoreCar

/-- Actual two-standard obstruction using the SELECTED source system-girth
bound and the FULL witness bound. The latter supplies its own linearity and
local pieces. Both old frames, all label inequalities and all witness
memberships are constructed. -/
theorem selectedPicture_twoStandard_force_core_pairEdge
    (hA : A.Irreducible) (hShared : ∀ _i : I, Nonempty Shared)
    (hStrong : ∀ b : RelStructure.Embedding B D, b ∈ family →
      AStrong A D (copyCarrier b))
    (hActive : AStrong A C.toRelStructure S)
    (hFull : (O).FullSystemGirthGT 2) (hCore : (Witness).FullSystemGirthGT 2)
    (i j : I) (a b c d : Label) (r s : OldEdge) (x y : Vertex)
    (hij : i ≠ j) (hxy : x ≠ y)
    (ha : (O).Meets a ((O).parent r)) (hb : (O).Meets b ((O).parent r))
    (hc : (O).Meets c ((O).parent s)) (hd : (O).Meets d ((O).parent s))
    (hReflect : ∀ (k : I) (p q : Shared),
      U.rel μ (Emb k p) (Emb k q) → T.rel μ p.1 q.1)
    (hyA : y ∈ (fun z : X => Std i z) '' (O).carrier a)
    (hxB : x ∈ (fun z : X => Std i z) '' (O).carrier b)
    (hyC : y ∈ (fun z : X => Std j z) '' (O).carrier c)
    (hxD : x ∈ (fun z : X => Std j z) '' (O).carrier d)
    (hDistinct : ¬ (generatedActualASupportTrain A hA C.toRelStructure S R f T U hShared).rel μ
      (actualAPictureEdgeEquiv A hA C.toRelStructure S R f
        (physicalStandardEdge (sharedOldACarrierInclusion A C.toRelStructure S) Emb i r))
      (actualAPictureEdgeEquiv A hA C.toRelStructure S R f
        (physicalStandardEdge (sharedOldACarrierInclusion A C.toRelStructure S) Emb j s))) :
    (Witness).PairEdge x y := by
  classical
  have hXi : x ∈ copyCarrier (Std i) := by
    obtain ⟨z, _, hz⟩ := hxB
    exact ⟨z, hz⟩
  have hYi : y ∈ copyCarrier (Std i) := by
    obtain ⟨z, _, hz⟩ := hyA
    exact ⟨z, hz⟩
  have hXj : x ∈ copyCarrier (Std j) := by
    obtain ⟨z, _, hz⟩ := hxD
    exact ⟨z, hz⟩
  have hYj : y ∈ copyCarrier (Std j) := by
    obtain ⟨z, _, hz⟩ := hyC
    exact ⟨z, hz⟩
  have hXCore := attachment_copy_copy_intersection_subset_core
    C.toRelStructure S R f hij ⟨hXi, hXj⟩
  have hYCore := attachment_copy_copy_intersection_subset_core
    C.toRelStructure S R f hij ⟨hYi, hYj⟩
  have hIx := activeAttached_mem_sharedWitness_of_standard_core
    A C e.toFunctionEmbedding R f U μ i x hXi hXCore
  have hIy := activeAttached_mem_sharedWitness_of_standard_core
    A C e.toFunctionEmbedding R f U μ i y hYi hYCore
  have hJx := activeAttached_mem_sharedWitness_of_standard_core
    A C e.toFunctionEmbedding R f U μ j x hXj hXCore
  have hJy := activeAttached_mem_sharedWitness_of_standard_core
    A C e.toFunctionEmbedding R f U μ j y hYj hYCore
  by_contra hNoEdge
  obtain ⟨sx, sy, tx, ty, hLongI, hLongJ, hCross, hxsi, hysi, hxtj, hytj⟩ :=
    sharedWitness_twoCopy_common_shared_pairs U μ Emb CoreCar hCore.1
      ((Witness).localPieceSystemBound_of_supremeCycleBound 2 hCore.2)
      i j x y hij hxy hIx hIy hJx hJy hNoEdge
  have toOld (k : I) (t : Shared) (z : Vertex) (hz : z ∈ CoreCar (Emb k t)) :
      z ∈ attachedOldAEdgeCarrier A C.toRelStructure S R f k t.1 :=
    Eq.mpr (congrArg (fun carrier => z ∈ carrier)
      (attachedSharedAEdgeCarrier_eq A C.toRelStructure S R f k t)) hz
  have hOldI := selectedPicture_block_rel_shared_of_no_core_pair
    A B D C family selected T μ e R f i hStrong hActive hFull a b r sx sy x y
    hxy ha hb (hReflect i sx sy hLongI) hyA hxB
    (toOld i sx x hxsi) (toOld i sy y hysi) hNoEdge
  have hOldJ := selectedPicture_block_rel_shared_of_no_core_pair
    A B D C family selected T μ e R f j hStrong hActive hFull c d s tx ty x y
    hxy hc hd (hReflect j tx ty hLongJ) hyC hxD
    (toOld j tx x hxtj) (toOld j ty y hytj) hNoEdge
  have hOldJq : Quotient.mk (T.wagonSetoid μ) s =
      Quotient.mk (T.wagonSetoid μ) tx.1 := Quotient.sound hOldJ
  exact hDistinct (generatedActualASupportTrain_three_link
    A hA C.toRelStructure S R f T U hShared μ i j r s sx tx
    hOldI hCross (Quotient.exact hOldJq.symm))

end SelectedPicture
end StructuralRamsey.Girth
