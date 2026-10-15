import Girth.TrainSelectedPictureOutputIncidence

/-!
# Geometrically contained mixed blocks, without assumed copy provenance

A prescribed output label can be contained in a standard other than its
inherited owner only when its whole carrier is in the active core. For finite
A, boundary classification shows that every edge of such a label contains
every vertex of the label. Its actual wagon-incidence edge is therefore a
legal mixed replacement, and factors through whichever standard contains it.

This localises ONE vertex-wagon occurrence. It does not preserve designation,
prove acceptability of a replaced cycle, or claim a simultaneous replacement.
The two-standard obstruction needs none of these: its checked incidence version
does not assume label inequalities or acceptability. Hence it applies directly
to geometrically contained blocks of the literal four-occurrence output cycle.

Only finiteness of A is added to the earlier interface. No nonemptiness or
nontriviality is assumed: in the singleton-boundary case, an actual active
vertex supplies the needed element of A. The prescribed family is never enlarged.
General segmentation and cycle transfer remain separate.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v

/-- Finite copies of the same structure cannot have properly nested carriers.
The proof factors one embedding through the other and uses surjectivity of a
finite injective self-map; neither ambient finiteness nor rigidity is needed. -/
theorem oldACarrierEdge_eq_of_subset
    {L : RelLanguage.{u}} {UA X : Type v} [Finite UA]
    (A : RelStructure L UA) (C : RelStructure L X)
    (r s : OldACarrierEdge A C) (hSub : r.1 ⊆ s.1) : r = s := by
  classical
  obtain ⟨a, ha⟩ := r.2
  obtain ⟨b, hb⟩ := s.2
  have hFactor : ∀ u : UA, ∃ w : UA, a u = b w := by
    intro u
    have hu : a u ∈ r.1 :=
      Eq.mpr (congrArg (fun Z : Set X => a u ∈ Z) ha) ⟨u, rfl⟩
    obtain ⟨w, hw⟩ := Eq.mp
      (congrArg (fun Z : Set X => a u ∈ Z) hb) (hSub hu)
    exact ⟨w, hw.symm⟩
  let t : RelStructure.Embedding A A := a.factorThroughRange b hFactor
  have ht (u : UA) : b (t u) = a u := by
    change b (Classical.choose (hFactor u)) = a u
    exact (Classical.choose_spec (hFactor u)).symm
  have hSurj : Function.Surjective (fun u : UA => t u) :=
    Finite.surjective_of_injective t.injective
  apply Subtype.ext
  apply Set.Subset.antisymm hSub
  intro z hz
  obtain ⟨u, hu⟩ := Eq.mp (congrArg (fun Z : Set X => z ∈ Z) hb) hz
  obtain ⟨w, hw⟩ := hSurj u
  have haz : a w = z := (ht w).symm.trans ((congrArg (fun v => b v) hw).trans hu)
  exact Eq.mpr (congrArg (fun Z : Set X => z ∈ Z) ha) ⟨w, haz⟩

/-- A prescribed copy wholly in the active subsystem has no vertex outside
any one of its actual A-edges. The small-boundary case includes singleton A;
the non-small case uses the boundary A-edge and finite carrier antichain. -/
theorem designated_active_vertex_mem_source_edge
    {L : RelLanguage.{u}} {UA VB P X : Type v} [Finite UA]
    (A : RelStructure L UA) (B : RelStructure L VB)
    (D : RelStructure L P) (C : StructuralRamsey.Partite.System L P X)
    (family : Set (RelStructure.Embedding B D))
    (e : RelStructure.Embedding A D) (q : DesignatedCopy B D C family)
    (hStrong : AStrong A D (copyCarrier q.base))
    (hSub : copyCarrier q.embedding ⊆ activeCarrier A C e.toFunctionEmbedding)
    (r : OldACarrierEdge A C.toRelStructure)
    (hr : r.1 ⊆ copyCarrier q.embedding) (x : X) (hx : x ∈ copyCarrier q.embedding) :
    x ∈ r.1 := by
  rcases projectedCopy_activeCarrier_intersection_classify
    A B D C e q.base q.lift hStrong with hSmall | ⟨aB, hBoundary⟩
  · obtain ⟨_a, u, _hu⟩ := hSub hx
    obtain ⟨ar, har⟩ := r.2
    have hu : ar u ∈ r.1 :=
      Eq.mpr (congrArg (fun Z : Set X => ar u ∈ Z) har) ⟨u, rfl⟩
    have hxu : x = ar u := hSmall ⟨hx, hSub hx⟩ ⟨hr hu, hSub (hr hu)⟩
    exact Eq.mpr (congrArg (fun z : X => z ∈ r.1) hxu) hu
  · let edge : OldACarrierEdge A C.toRelStructure :=
      ⟨copyCarrier (q.embedding.comp aB), ⟨q.embedding.comp aB, rfl⟩⟩
    have hQ : copyCarrier q.embedding = edge.1 :=
      (Set.inter_eq_left.mpr hSub).symm.trans hBoundary
    have hRE : r = edge := oldACarrierEdge_eq_of_subset A C.toRelStructure r edge
      (fun z hz => Eq.mp (congrArg (fun Z : Set X => z ∈ Z) hQ) (hr hz))
    have hxE : x ∈ edge.1 := Eq.mp (congrArg (fun Z : Set X => x ∈ Z) hQ) hx
    exact Eq.mpr
      (congrArg (fun edge : OldACarrierEdge A C.toRelStructure => x ∈ edge.1) hRE) hxE

section Attachment

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
variable (μ : Fin (m + 1))

local notation "S" => activeCarrier A C e.toFunctionEmbedding
local notation "Vertex" => RelStructure.Attachment.Vertex S (W := Y) (I := I)
local notation "OldEdge" => OldACarrierEdge A C.toRelStructure
local notation "ActualEdge" => OldACarrierEdge A (RelStructure.Attachment.attach C.toRelStructure S R f)
local notation "Selected" => {q : DesignatedCopy B D C family // q ∈ selected}
local notation "Label" => Selected ⊕ OldEdge
local notation "OutLabel" => (I × Selected) ⊕ ActualEdge
local notation "Std" => RelStructure.Attachment.copyEmbedding C.toRelStructure S R f
local notation "Emb" => sharedOldACarrierCoreEmbedding A C.toRelStructure S R f
local notation "CoreCar" => attachedCoreAEdgeCarrier A C.toRelStructure S R f
local notation "StdEdge" => (fun (i : I) (a : OldEdge) =>
  actualAPictureEdgeEquiv A hA C.toRelStructure S R f
    (physicalStandardEdge (sharedOldACarrierInclusion A C.toRelStructure S) Emb i a))
local notation "Train" => generatedActualASupportTrain A hA C.toRelStructure S R f T U hShared
local notation "Old" => selectedPictureOrderOneData A B D C family selected T μ
local notation "Witness" => sharedWitnessOrderOneData U μ Emb CoreCar
local notation "Out" => attachedSelectedPictureOrderOneData
  A hA B D C family selected e R f T U hShared μ
local notation "LabelMap" => attachedSelectedPictureLabel
  A hA B D C family selected e R f

/-- An actual edge in a standard factors through it, preserving a chosen
vertex and its arbitrary output wagon. This does not involve designated labels. -/
theorem attachedSelectedPicture_edge_localize
    (i : I) (edge : ActualEdge) (z : Vertex)
    (W : Quotient ((Train).wagonSetoid μ))
    (hSub : edge.1 ⊆ copyCarrier (Std i))
    (hz : z ∈ edge.1) (hW : (Out).parent edge = W) :
    ∃ r : OldEdge, z ∈ (Out).carrier (LabelMap i (.inr r)) ∧
      (Out).Meets (LabelMap i (.inr r)) W := by
  have hImage : edge.1 ⊆ (fun x : X => Std i x) '' (Set.univ : Set X) := by
    intro x hx
    obtain ⟨y, hy⟩ := hSub hx
    exact ⟨y, Set.mem_univ y, hy⟩
  obtain ⟨r, _hr, hImageEq⟩ := oldACarrierEdge_pullback_of_subset_image
    A C.toRelStructure (RelStructure.Attachment.attach C.toRelStructure S R f)
    (Std i) Set.univ edge hImage
  have hEq : StdEdge i r = edge := Subtype.ext
    ((actualAPictureEdgeEquiv_standard_carrier A hA C.toRelStructure S R f i r).trans hImageEq)
  refine ⟨r, ?_, ?_⟩
  · change z ∈ (StdEdge i r).1
    exact Eq.mpr (congrArg (fun a : ActualEdge => z ∈ a.1) hEq) hz
  · change ∃ a : ActualEdge, a = StdEdge i r ∧ (Out).parent a = W
    exact ⟨edge, hEq.symm, hW⟩

/-- Localise a mixed occurrence by geometric containment, NOT by assuming that
its designated label is inherited from the chosen standard. A foreign prescribed
label lies wholly in the active subsystem of its own standard. Its actual
wagon-incidence edge contains the chosen vertex and can be used instead.
This is only a mixed-incidence replacement; designation is not preserved. -/
theorem attachedSelectedPicture_mixed_localize [Finite UA]
    (hStrong : ∀ b : RelStructure.Embedding B D, b ∈ family → AStrong A D (copyCarrier b))
    (i : I) (a : OutLabel) (z : Vertex) (W : Quotient ((Train).wagonSetoid μ))
    (hSub : (Out).carrier a ⊆ copyCarrier (Std i))
    (hz : z ∈ (Out).carrier a) (hMeet : (Out).Meets a W) :
    ∃ b : Label, z ∈ (Out).carrier (LabelMap i b) ∧ (Out).Meets (LabelMap i b) W := by
  classical
  cases a with
  | inr edge =>
      obtain ⟨a, ha, hW⟩ := hMeet
      have hae : a = edge := ha
      subst a
      obtain ⟨r, hr, hM⟩ := attachedSelectedPicture_edge_localize
        A hA B D C family selected e R f T U hShared μ i edge z W hSub hz hW
      exact ⟨.inr r, hr, hM⟩
  | inl iq =>
      obtain ⟨k, q⟩ := iq
      by_cases hki : k = i
      · subst k
        exact ⟨.inl q, hz, hMeet⟩
      · have hActive : copyCarrier q.1.embedding ⊆ S := by
          intro w hw
          have hOther : Std k w ∈ copyCarrier (Std i) := hSub ⟨w, hw, rfl⟩
          obtain ⟨v, hv⟩ := hOther
          by_contra hwNot
          have hMaps :
              RelStructure.Attachment.copyMap C.toRelStructure S R f k w =
                RelStructure.Attachment.copyMap C.toRelStructure S R f i v := hv.symm
          exact hki (RelStructure.Attachment.index_eq_of_outside hwNot hMaps)
        obtain ⟨r, hr, hW⟩ := (attachedSelectedPicture_meets_iff
          A hA B D C family selected e R f T U hShared μ k (.inl q) W).mp hMeet
        obtain ⟨w, hw, hwz⟩ := hz
        have hwR : w ∈ r.1 := designated_active_vertex_mem_source_edge
          A B D C family e q.1 (hStrong q.1.base q.1.base_mem) hActive r hr w hw
        have hzR : z ∈ (StdEdge k r).1 :=
          Eq.mpr (congrArg (fun Z : Set Vertex => z ∈ Z)
            (actualAPictureEdgeEquiv_standard_carrier A hA C.toRelStructure S R f k r))
            ⟨w, hwR, hwz⟩
        have hRSub : (StdEdge k r).1 ⊆ copyCarrier (Std i) := by
          intro z hz
          obtain ⟨w, hw, hwz⟩ := Eq.mp (congrArg (fun Z : Set Vertex => z ∈ Z)
            (actualAPictureEdgeEquiv_standard_carrier A hA C.toRelStructure S R f k r)) hz
          exact hSub ⟨w, hr hw, hwz⟩
        obtain ⟨s, hs, hM⟩ := attachedSelectedPicture_edge_localize
          A hA B D C family selected e R f T U hShared μ i (StdEdge k r) z W hRSub hzR hW
        exact ⟨.inr s, hs, hM⟩

/-- The two-standard obstruction for arbitrary output labels geometrically
contained in the two assigned standards. Four mixed localisations suffice;
there is no need to claim the replacement word is a big cycle or acceptable. -/
theorem attachedSelectedPicture_containedBlocks_force_core_pairEdge [Finite UA]
    (hPartite : C.IsPartiteOver D) (hBaseLinear : ALinear A D)
    (hRigid : ∀ b : RelStructure.Embedding A D, SameCopy b e → b = e)
    (hStrong : ∀ b : RelStructure.Embedding B D, b ∈ family → AStrong A D (copyCarrier b))
    (hFull : (Old).FullSystemGirthGT 2) (hCore : (Witness).FullSystemGirthGT 2)
    (hRel : ∀ (ν : Fin (m + 1)) (k : I)
      (p q : SharedOldACarrierEdge A C.toRelStructure S),
      T.rel ν p.1 q.1 ↔ U.rel ν (Emb k p) (Emb k q))
    (i j : I) (a b c d : OutLabel) (x y : Vertex)
    (W₁ W₂ : Quotient ((Train).wagonSetoid μ))
    (hij : i ≠ j) (hxy : x ≠ y) (hW : W₁ ≠ W₂)
    (haSub : (Out).carrier a ⊆ copyCarrier (Std i))
    (hbSub : (Out).carrier b ⊆ copyCarrier (Std i))
    (hcSub : (Out).carrier c ⊆ copyCarrier (Std j))
    (hdSub : (Out).carrier d ⊆ copyCarrier (Std j))
    (ha : (Out).Meets a W₁) (hb : (Out).Meets b W₁)
    (hc : (Out).Meets c W₂) (hd : (Out).Meets d W₂)
    (hyA : y ∈ (Out).carrier a) (hxB : x ∈ (Out).carrier b)
    (hyC : y ∈ (Out).carrier c) (hxD : x ∈ (Out).carrier d) :
    (Witness).PairEdge x y := by
  obtain ⟨a', hyA', ha'⟩ := attachedSelectedPicture_mixed_localize
    A hA B D C family selected e R f T U hShared μ hStrong i a y W₁ haSub hyA ha
  obtain ⟨b', hxB', hb'⟩ := attachedSelectedPicture_mixed_localize
    A hA B D C family selected e R f T U hShared μ hStrong i b x W₁ hbSub hxB hb
  obtain ⟨c', hyC', hc'⟩ := attachedSelectedPicture_mixed_localize
    A hA B D C family selected e R f T U hShared μ hStrong j c y W₂ hcSub hyC hc
  obtain ⟨d', hxD', hd'⟩ := attachedSelectedPicture_mixed_localize
    A hA B D C family selected e R f T U hShared μ hStrong j d x W₂ hdSub hxD hd
  exact attachedSelectedPicture_twoStandard_force_core_pairEdge
    A hA B D C family selected e R f T U hShared μ
    hPartite hBaseLinear hRigid hStrong hFull hCore hRel
    i j a' b' c' d' x y W₁ W₂ hij hxy hW ha' hb' hc' hd' hyA' hxB' hyC' hxD'

/-- Literal four-occurrence output cycle with GEOMETRIC block containment.
No inherited-label presentation, label inequalities, or acceptability is assumed.
The four containment hypotheses have exactly the meaning of the displayed
blocks lying in two distinct standards. -/
theorem attachedSelectedPicture_contained_cycle_force_core_pairEdge [Finite UA]
    (hPartite : C.IsPartiteOver D) (hBaseLinear : ALinear A D)
    (hRigid : ∀ b : RelStructure.Embedding A D, SameCopy b e → b = e)
    (hStrong : ∀ b : RelStructure.Embedding B D, b ∈ family → AStrong A D (copyCarrier b))
    (hFull : (Old).FullSystemGirthGT 2) (hCore : (Witness).FullSystemGirthGT 2)
    (hRel : ∀ (ν : Fin (m + 1)) (k : I)
      (p q : SharedOldACarrierEdge A C.toRelStructure S),
      T.rel ν p.1 q.1 ↔ U.rel ν (Emb k p) (Emb k q))
    (K : (Out).BigCycle 4) (i j : I) (x y : Vertex)
    (W₁ W₂ : Quotient ((Train).wagonSetoid μ)) (hij : i ≠ j)
    (hConnectors : K.connector = ![Sum.inr W₁, Sum.inl x, Sum.inr W₂, Sum.inl y])
    (h0 : (Out).carrier (K.label 0) ⊆ copyCarrier (Std i))
    (h1 : (Out).carrier (K.label 1) ⊆ copyCarrier (Std i))
    (h2 : (Out).carrier (K.label 2) ⊆ copyCarrier (Std j))
    (h3 : (Out).carrier (K.label 3) ⊆ copyCarrier (Std j)) :
    (Witness).PairEdge x y := by
  have hxy : x ≠ y := by
    intro h
    have hc : K.connector (1 : Fin 4) = K.connector (3 : Fin 4) := by
      simp [hConnectors, h]
    have hi := K.connector_injective hc
    norm_num at hi
  have hW : W₁ ≠ W₂ := by
    intro h
    have hc : K.connector (0 : Fin 4) = K.connector (2 : Fin 4) := by
      simp [hConnectors, h]
    have hi := K.connector_injective hc
    norm_num at hi
  apply attachedSelectedPicture_containedBlocks_force_core_pairEdge
    A hA B D C family selected e R f T U hShared μ
    hPartite hBaseLinear hRigid hStrong hFull hCore hRel
    i j (K.label 0) (K.label 1) (K.label 3) (K.label 2) x y W₁ W₂
    hij hxy hW h0 h1 h3 h2
  · simpa [hConnectors, OrderOneData.Incident, cyclicSucc] using K.left_incident (0 : Fin 4)
  · simpa [hConnectors, OrderOneData.Incident, cyclicSucc] using K.right_incident (0 : Fin 4)
  · simpa [hConnectors, OrderOneData.Incident, cyclicSucc] using K.right_incident (2 : Fin 4)
  · simpa [hConnectors, OrderOneData.Incident, cyclicSucc] using K.left_incident (2 : Fin 4)
  · simpa [hConnectors, OrderOneData.Incident, cyclicSucc] using K.right_incident (3 : Fin 4)
  · simpa [hConnectors, OrderOneData.Incident, cyclicSucc] using K.left_incident (1 : Fin 4)
  · simpa [hConnectors, OrderOneData.Incident, cyclicSucc] using K.left_incident (3 : Fin 4)
  · simpa [hConnectors, OrderOneData.Incident, cyclicSucc] using K.right_incident (1 : Fin 4)

end Attachment
end StructuralRamsey.Girth
