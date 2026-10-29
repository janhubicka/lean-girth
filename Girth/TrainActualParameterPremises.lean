import Girth.TrainAllAdjacentParametersBridge

/-!
# Intrinsic parameter premises for an actual partite attachment

The generated-train parameter theorem takes the old and core sibling bounds
on their carriers *inside* the attachment.  The induction instead supplies
these bounds on the original old and core vertices.  Injectivity of each
canonical vertex embedding identifies the intersection of two image wagon
carriers with the image of their intersection.  Preservation of parts then
supplies the same allowed-part bound in the attachment.

Likewise the interior order-one witness may be checked on core vertices:
injectively embedding those vertices preserves its exact two-source bridges.
These lemmas discharge premises of the existing generated-train theorem.
They do not assert system-girth preservation or construct an inductive witness.
The train relations and all physical ambient edge labels are retained.
-/

namespace StructuralRamsey.Girth

universe u v

namespace EdgeTrainLevels

variable {V W E : Type v}

/-- Taking a wagon carrier commutes with taking vertex images.  The wagon
quotient labels and their equivalence relation are unchanged. -/
theorem wagonClassCarrier_vertexImage
    {m : ℕ} (T : EdgeTrainLevels E m)
    (edge : E → Set V) (φ : V → W)
    (μ : Fin (m + 1)) (q : Quotient (T.wagonSetoid μ)) :
    T.wagonClassCarrier (fun e => φ '' edge e) μ q =
      φ '' T.wagonClassCarrier edge μ q := by
  induction q using Quotient.inductionOn with
  | h a =>
      change T.wagonCarrier (fun e => φ '' edge e) μ a =
        φ '' T.wagonCarrier edge μ a
      ext z
      constructor
      · rintro ⟨e, hae, x, hx, rfl⟩
        exact ⟨x, ⟨e, hae, hx⟩, rfl⟩
      · rintro ⟨x, ⟨e, hae, hx⟩, rfl⟩
        exact ⟨e, hae, x, hx, rfl⟩

/-- An injective vertex map transports intrinsic sibling-intersection
bounds to any allowed sets containing the images of the original ones. -/
theorem adjacentParameters_vertexImage
    {m : ℕ} (T : EdgeTrainLevels E m)
    (edge : E → Set V) (φ : V ↪ W)
    (oldAllowed : Fin (m + 1) → Set V)
    (newAllowed : Fin (m + 1) → Set W)
    (hOld : T.AdjacentParameters edge oldAllowed)
    (hAllowed : ∀ ν, φ '' oldAllowed ν ⊆ newAllowed ν) :
    T.AdjacentParameters (fun e => φ '' edge e) newAllowed := by
  intro μ ν hμν hSucc a b hab hParent z hz
  rw [T.wagonClassCarrier_vertexImage edge φ μ a,
    T.wagonClassCarrier_vertexImage edge φ μ b] at hz
  rcases hz.1 with ⟨x, hxa, hxz⟩
  rcases hz.2 with ⟨y, hyb, hyz⟩
  have hxy : x = y := φ.injective (hxz.trans hyz.symm)
  subst y
  exact hAllowed ν ⟨x, hOld μ ν hμν hSucc hab hParent ⟨hxa, hyb⟩, hxz⟩

/-- Part preservation discharges the allowed-image premise without
enlarging the permitted set of parts at any level. -/
theorem adjacentPartParameters_vertexEmbedding
    {m : ℕ} {P : Type v} (T : EdgeTrainLevels E m)
    (edge : E → Set V) (φ : V ↪ W)
    (oldPart : V → P) (newPart : W → P)
    (hPart : ∀ x, newPart (φ x) = oldPart x)
    (allowedParts : Fin (m + 1) → Set P)
    (hOld : T.AdjacentParameters edge
      (fun ν => {x | oldPart x ∈ allowedParts ν})) :
    T.AdjacentParameters (fun e => φ '' edge e)
      (fun ν => {x | newPart x ∈ allowedParts ν}) := by
  apply T.adjacentParameters_vertexImage edge φ
    (fun ν => {x | oldPart x ∈ allowedParts ν})
    (fun ν => {x | newPart x ∈ allowedParts ν}) hOld
  intro ν z hz
  rcases hz with ⟨x, hx, rfl⟩
  change newPart (φ x) ∈ allowedParts ν
  change oldPart x ∈ allowedParts ν at hx
  rw [hPart x]
  exact hx

end EdgeTrainLevels

/-- The shared-witness order-one bound is preserved by an injective
change of vertex representation.  Edge ownership and parent labels stay
literal; no global cycle or extra top-coordinate bound is assumed. -/
theorem sharedWitnessOrderOneData_bound_vertexImage
    {V W E I S : Type v} {m : ℕ}
    (T : EdgeTrainLevels E m) (ν : Fin (m + 1))
    (inCore : I → S ↪ E) (edge : E → Set V) (φ : V ↪ W)
    (hBound : (sharedWitnessOrderOneData T ν inCore edge).Bound) :
    (sharedWitnessOrderOneData T ν inCore (fun e => φ '' edge e)).Bound := by
  let D := sharedWitnessOrderOneData T ν inCore edge
  let D' := sharedWitnessOrderOneData T ν inCore (fun e => φ '' edge e)
  have hCarrier : ∀ a : I ⊕ E, D'.carrier a = φ '' D.carrier a := by
    intro a
    cases a with
    | inl i =>
        ext z
        constructor
        · rintro ⟨s, x, hx, rfl⟩
          exact ⟨x, ⟨s, hx⟩, rfl⟩
        · rintro ⟨x, ⟨s, hx⟩, rfl⟩
          exact ⟨s, x, hx, rfl⟩
    | inr e => rfl
  apply D'.bound_iff_both_bridges.mpr
  intro a b z p hab hza hzb hma hmb
  rw [hCarrier a] at hza
  rw [hCarrier b] at hzb
  rcases hza with ⟨x, hxa, rfl⟩
  rcases hzb with ⟨y, hyb, hyx⟩
  have hxy : y = x := φ.injective hyx
  subst y
  obtain ⟨ha, hb⟩ := D.both_bridges hBound a b x p hab hxa hyb hma hmb
  constructor
  · rcases ha with ⟨e, he, hep, hxe⟩
    exact ⟨e, he, hep, ⟨x, hxe, rfl⟩⟩
  · rcases hb with ⟨e, he, hep, hxe⟩
    exact ⟨e, he, hep, ⟨x, hxe, rfl⟩⟩

open StructuralRamsey.RelStructure

variable {L : RelLanguage.{u}} {UA P Old Core I : Type v}

/-- Intrinsic parameters of the old partite picture provide the exact
old-carrier premise for every attached standard picture. -/
theorem attachedOldAEdgeCarrier_adjacentParameters_of_intrinsic
    {m : ℕ} (A : RelStructure L UA)
    (B : StructuralRamsey.Partite.System L P Old) (S : Set Old)
    (D : StructuralRamsey.Partite.System L P Core)
    (f : I → StructuralRamsey.Partite.Embedding (B.induce S) D)
    (T : EdgeTrainLevels (OldACarrierEdge A B.toRelStructure) m)
    (allowedParts : Fin (m + 1) → Set P)
    (hOld : T.AdjacentParameters (fun e => e.1)
      (fun ν => {x | B.part x ∈ allowedParts ν}))
    (i : I) :
    T.AdjacentParameters
      (attachedOldAEdgeCarrier A B.toRelStructure S D.toRelStructure
        (fun i => (f i).toEmbedding) i)
      (fun ν => {x |
        (StructuralRamsey.Partite.Attachment.attach B S D f).part x ∈
          allowedParts ν}) := by
  let e := StructuralRamsey.Partite.Attachment.copyEmbedding B S D f i
  exact T.adjacentPartParameters_vertexEmbedding (fun a => a.1)
    ⟨e, e.injective⟩ B.part
    (StructuralRamsey.Partite.Attachment.attach B S D f).part
    e.map_part allowedParts hOld

/-- Intrinsic parameters of the core witness provide the exact
core-carrier premise in the attachment, with the same allowed parts. -/
theorem attachedCoreAEdgeCarrier_adjacentParameters_of_intrinsic
    {m : ℕ} (A : RelStructure L UA)
    (B : StructuralRamsey.Partite.System L P Old) (S : Set Old)
    (D : StructuralRamsey.Partite.System L P Core)
    (f : I → StructuralRamsey.Partite.Embedding (B.induce S) D)
    (T : EdgeTrainLevels (OldACarrierEdge A D.toRelStructure) m)
    (allowedParts : Fin (m + 1) → Set P)
    (hCore : T.AdjacentParameters (fun e => e.1)
      (fun ν => {x | D.part x ∈ allowedParts ν})) :
    T.AdjacentParameters
      (attachedCoreAEdgeCarrier A B.toRelStructure S D.toRelStructure
        (fun i => (f i).toEmbedding))
      (fun ν => {x |
        (StructuralRamsey.Partite.Attachment.attach B S D f).part x ∈
          allowedParts ν}) := by
  let e := StructuralRamsey.Partite.Attachment.coreEmbedding B S D f
  exact T.adjacentPartParameters_vertexEmbedding (fun a => a.1)
    ⟨e, e.injective⟩ D.part
    (StructuralRamsey.Partite.Attachment.attach B S D f).part
    e.map_part allowedParts hCore

/-- The interior order-one hypothesis can be supplied on intrinsic core
vertices.  Its transport to the exact attached shared-witness data is
automatic from the canonical core embedding's injectivity. -/
theorem attachedSharedWitnessOrderOne_bound_of_intrinsic
    {m : ℕ} (A : RelStructure L UA)
    (B : RelStructure L Old) (S : Set Old) (D : RelStructure L Core)
    (f : I → RelStructure.Embedding (B.induce S) D)
    (T : EdgeTrainLevels (OldACarrierEdge A D) m)
    (ν : Fin (m + 1))
    (hBound : (sharedWitnessOrderOneData T ν
      (sharedOldACarrierCoreEmbedding A B S D f)
      (fun e => e.1)).Bound) :
    (sharedWitnessOrderOneData T ν
      (sharedOldACarrierCoreEmbedding A B S D f)
      (attachedCoreAEdgeCarrier A B S D f)).Bound := by
  let e := RelStructure.Attachment.coreEmbedding B S D f
  exact sharedWitnessOrderOneData_bound_vertexImage T ν
    (sharedOldACarrierCoreEmbedding A B S D f) (fun a => a.1)
    ⟨e, e.injective⟩ hBound

end StructuralRamsey.Girth
