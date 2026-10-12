import Girth.TrainActualASupportPushoutEquiv
import Girth.TrainEdgeEquivalenceTransport

/-!
# The genuine A-support edge bijection transports all train wagon levels

The checked carrier-pushout equivalence maps canonical core/private
A-support presentations bijectively onto ACTUAL physical A-copy
carriers of a free relational attachment.

Transporting a train along this precise bijection preserves and
reflects EVERY horizontal wagon equivalence, bottom equality, top
universal class and nesting, and preserves each labelled wagon's
full vertex carrier exactly. No old or new wagon labels are
identified solely because the corresponding vertex carriers
happen to be the same set.

This supplies the exact abstract interface by which a train on the
presented edge family becomes a train on the ACTUAL A-support
hypergraph. It does not construct the generated picture-wagon
relations on the presented type, nor prove the allowed-part
parameters or acceptable-cycle system-Girth A1--A3.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {UA Old Core I : Type v}

/-- The actual ambient A-support edge type, keeping just the genuine
physical carrier set (not the identity of an embedding). -/
def ActualAttachedAEdge
    (A : RelStructure L UA)
    (B : RelStructure L Old)
    (S : Set Old)
    (D : RelStructure L Core)
    (f : I → RelStructure.Embedding (B.induce S) D) :=
  {e : Set (RelStructure.Attachment.Vertex S (W := Core) (I := I)) //
    e ∈ actualACopyCarriers A (RelStructure.Attachment.attach B S D f)}

/-- Transport a train on the canonical presented A-support edges to
the genuine A-support family using its now verified carrier bijection. -/
noncomputable def actualAttachedATrain
    {m : ℕ}
    (A : RelStructure L UA)
    (hA : A.Irreducible)
    (B : RelStructure L Old)
    (S : Set Old)
    (D : RelStructure L Core)
    (f : I → RelStructure.Embedding (B.induce S) D)
    (T : EdgeTrainLevels (GenuineACarrierPresentation A B S D I) m) :
    EdgeTrainLevels (ActualAttachedAEdge A B S D f) m :=
  T.transport (actualACarrierPushoutEquiv A hA B S D f)

/-- Exact preservation/reflection of a cut equivalence on actual
physical A-support edges. -/
theorem actualAttachedATrain_rel_iff
    {m : ℕ}
    (A : RelStructure L UA)
    (hA : A.Irreducible)
    (B : RelStructure L Old)
    (S : Set Old)
    (D : RelStructure L Core)
    (f : I → RelStructure.Embedding (B.induce S) D)
    (T : EdgeTrainLevels (GenuineACarrierPresentation A B S D I) m)
    (μ : Fin (m + 1))
    (e₁ e₂ : GenuineACarrierPresentation A B S D I) :
    (actualAttachedATrain A hA B S D f T).rel μ
        (actualACarrierPushoutEquiv A hA B S D f e₁)
        (actualACarrierPushoutEquiv A hA B S D f e₂)
      ↔ T.rel μ e₁ e₂ := by
  exact EdgeTrainLevels.transport_rel_iff
    T (actualACarrierPushoutEquiv A hA B S D f) μ e₁ e₂

/-- Every labelled wagon in the transported ACTUAL A-support
hypergraph has EXACTLY the same physical vertex carrier as its
presentation-side wagon. This is stronger than equality of
unlabelled carrier SETS: it preserves distinct wagon labels. -/
theorem actualAttachedATrain_wagonCarrier_eq
    {m : ℕ}
    (A : RelStructure L UA)
    (hA : A.Irreducible)
    (B : RelStructure L Old)
    (S : Set Old)
    (D : RelStructure L Core)
    (f : I → RelStructure.Embedding (B.induce S) D)
    (T : EdgeTrainLevels (GenuineACarrierPresentation A B S D I) m)
    (μ : Fin (m + 1))
    (e : GenuineACarrierPresentation A B S D I) :
    (actualAttachedATrain A hA B S D f T).wagonCarrier
        (fun x : ActualAttachedAEdge A B S D f => x.1)
        μ (actualACarrierPushoutEquiv A hA B S D f e) =
      T.wagonCarrier (genuineACarrierEval A B S D f) μ e := by
  exact EdgeTrainLevels.transport_wagonCarrier_eq
    T (actualACarrierPushoutEquiv A hA B S D f)
    (genuineACarrierEval A B S D f)
    (fun x : ActualAttachedAEdge A B S D f => x.1)
    (by intro q; rfl) μ e

end StructuralRamsey.Girth
