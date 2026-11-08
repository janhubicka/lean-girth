import Girth.TrainTwoWagonFullSystemObstruction
import Girth.TrainActualCutIndexedBigCycle
import Mathlib.Tactic

set_option autoImplicit false
set_option Elab.async false

/-!
# Two actual geometric owner cuts cannot both be wagon connectors

The genuine geometric cut-indexed witness BigCycle retains every
actual source cut connector under the verified injective vertex/
wagon map. If the original two geometric cut connectors are BOTH
wagon-labelled, their two reduced witness connectors must likewise
be wagons. The reduced source has exactly two occurrences, regardless
of how long the original output source was.

The generic no-two-wagon-witness theorem then contradicts genuine
witness FullSystemGirthGT q at q>=2. No FullSystemGirthGT or
SupremeCycleBound of the ATTACHED OUTPUT is used: this is a physical
case exclusion for the remaining two-cut theorem.

No source B-label is identified with its geometric owner, no
short/long reduced plan is assumed, and no physical ambient edge
or wagon quotient label is removed. Circulation only; no appendix.
-/

namespace StructuralRamsey.Girth

namespace OrderOneData

universe v
variable {V E I P : Type v} (D : OrderOneData V E I P)

/-- The two-wagon witness contradiction remains valid when the
source is indexed by an abstract n with a certified equality n=2. -/
theorem BigCycle.two_wagon_absurd_of_fullSystemGirth_of_length_eq_two
    {q n : ℕ}
    (hFull : D.FullSystemGirthGT q) (hq : 2 ≤ q)
    (Z : D.BigCycle n) (hn : n = 2)
    (hWagons : ∀ j : Fin n, ∃ p : P, Z.connector j = Sum.inr p) :
    False := by
  subst n
  obtain ⟨p, hp⟩ := hWagons (0 : Fin 2)
  obtain ⟨r, hr⟩ := hWagons (1 : Fin 2)
  exact Z.two_wagon_absurd_of_fullSystemGirth
    D hFull hq p r hp hr

end OrderOneData

open StructuralRamsey.RelStructure

universe u v
section ActualTwoCutDoubleWagon

variable {L : RelLanguage.{u}} {UA VB P X Y I : Type v}
variable (A : RelStructure L UA) (hA : A.Irreducible)
variable (B : RelStructure L VB) (D : RelStructure L P)
variable (C : StructuralRamsey.Partite.System L P X)
variable (family : Set (Embedding B D))
variable (selected : Set (DesignatedCopy B D C family))
variable (e : Embedding A D) (R : RelStructure L Y)
variable (f : I → Embedding
  (C.toRelStructure.induce (activeCarrier A C e.toFunctionEmbedding)) R)
variable {m : ℕ}
variable (T : EdgeTrainLevels (OldACarrierEdge A C.toRelStructure) m)
variable (U : EdgeTrainLevels (OldACarrierEdge A R) m)
variable (hShared : ∀ _i : I, Nonempty
  (SharedOldACarrierEdge A C.toRelStructure
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
local notation "Emb" => sharedOldACarrierCoreEmbedding
  A C.toRelStructure S R f
local notation "CoreEmb" => RelStructure.Attachment.coreEmbedding
  C.toRelStructure S R f
local notation "Train" => generatedActualASupportTrain
  A hA C.toRelStructure S R f T U hShared
local notation "CoreWagon" => generatedActualASupportTrain_coreWagonEmbedding
  A hA C.toRelStructure S R f T U
    (fun ν j p q h => (hRel ν j p q).mp h) hShared μ
local notation "Out" => attachedSelectedPictureOrderOneData
  A hA B D C family selected e R f T U hShared μ
local notation "Wit" => sharedWitnessOrderOneData
  U μ Emb (Subtype.val : CoreEdge → Set Y)
local notation "GeomAllowed" => selectedOutputGeometricOwnerAllowed
  A hA B D C family selected e R f T U hShared μ

include hRel

/-- Under genuine WITNESS system-girth at q>=2, an actual output
BigCycle cannot have exactly two geometric owner cuts with two
distinct WAGON connectors at those cuts. Original source length is
arbitrary. This excludes a whole part of the unproved two-cut case
without assuming output girth. -/
theorem attachedSelectedPicture_two_cut_double_wagon_absurd_of_witness
    {n q : ℕ} (K : (Out).BigCycle n)
    (owner : Fin n → I ⊕ CoreEdge)
    (hAllowed : ∀ j, GeomAllowed (K.label j) (owner j))
    (hTwo : cyclicOwnerChanges owner = 2)
    (hWagons : ∀ j : Fin (cyclicOwnerChanges owner),
      ∃ w : Quotient ((Train).wagonSetoid μ),
        K.connector (cyclicOwnerCutIndex owner j) = Sum.inr w)
    (hWitness : (Wit).FullSystemGirthGT q)
    (hq : 2 ≤ q) : False := by
  let Z := attachedSelectedPicture_geometric_cutBigCycle
    A hA B D C family selected e R f T U hShared hRel μ
    K owner hAllowed (by omega : 2 ≤ cyclicOwnerChanges owner)
  have hWitnessWagons :
      ∀ j : Fin (cyclicOwnerChanges owner),
        ∃ p : Quotient (U.wagonSetoid μ), Z.connector j = Sum.inr p := by
    intro j
    obtain ⟨w, hw⟩ := hWagons j
    have hMap : Sum.map CoreEmb CoreWagon (Z.connector j) =
        K.connector (cyclicOwnerCutIndex owner j) :=
      attachedSelectedPicture_cutConnector_eq
        A hA B D C family selected e R f T U hShared hRel μ
        K owner hAllowed j
    rw [hw] at hMap
    cases hC : Z.connector j with
    | inl x =>
        rw [hC] at hMap
        cases hMap
    | inr p =>
        exact ⟨p, hC⟩
  exact Z.two_wagon_absurd_of_fullSystemGirth_of_length_eq_two
    (Wit) hWitness hq hTwo hWitnessWagons

end ActualTwoCutDoubleWagon

end StructuralRamsey.Girth
