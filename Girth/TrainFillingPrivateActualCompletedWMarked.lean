import Girth.TrainFillingPrivateCompletedWMarked
import Girth.TrainFillingPrivateActualSourceEdgeEquiv

set_option Elab.async false

/-!
# The marked completed-W intersection condition from the ACTUAL T

This connects the general completed-W support/degree-one lemma
to the genuine edge owner of an original train T.

For physical old A-support edges e != f with the same
first-wagon owner, the FIRST original train parameter
requires their intersection to use allowed predicates A₁.

We know from labelled first-wagon girth >g>=2 that
different wagon carriers meet in at most one vertex.
Therefore the A-support edges induced in F_p have the
CORRECT genuine original owner p, and local distinct
edges remain physically distinct in T.

The completed W includes only induced first-wagon edges
as full hyperedges, and its completion adds no new
hyperedges. The original first train parameter therefore
transfers without introducing any additional forbidden
edge intersection.

This is the source-side degree-one condition needed by
the Track 1 owner-split Ramsey theorem. It is not the
later covered/marked X output or the RR_h witness.

Lean candidate only; exact-head kernel check required.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v
variable {I : Type u} {V : Type v}
variable [LinearOrder I] [LinearOrder V] [Finite V]

/-- At any original labelled wagon cut μ, the genuine train
relation/owner together with the old allowed-intersection
parameter yields the SAME allowed-intersection restriction
on the complete support of the COMPLETED ordered W.

At cutoff two μ is the first-wagon cut 1 and allowed=A₁.
The premise hOriginalParam is an ORIGINAL T condition,
not a new Ramsey or EHN output condition. -/
theorem actualFirstWagonCompletedW_support_inter_allowed
    (k : ℕ) (hk : 2 ≤ k)
    (profile : Fin k → I)
    (oldEdges : Set (Set V)) (colour : V → I)
    {m : ℕ}
    (T : EdgeTrainLevels
      {e : Set V // e ∈ supportCopies
        (colouredOrderedEdgeSource.{u,v} k profile)
        (colouredOrderedEdgeTarget k oldEdges colour)} m)
    (μ : Fin (m + 1))
    (g : ℕ) (hg : 2 ≤ g)
    (hGirth : LabelledGirthGT
      (T.wagonClassCarrier
        (fun e : {e : Set V // e ∈ supportCopies
          (colouredOrderedEdgeSource.{u,v} k profile)
          (colouredOrderedEdgeTarget k oldEdges colour)} => e.1)
        μ) g)
    (allowed : Set I)
    (hOriginalParam :
      ∀ e f : {e : Set V // e ∈ supportCopies
          (colouredOrderedEdgeSource.{u,v} k profile)
          (colouredOrderedEdgeTarget k oldEdges colour)},
        e ≠ f → T.rel μ e f →
          e.1 ∩ f.1 ⊆ {x : V | colour x ∈ allowed}) :
    let A := colouredOrderedEdgeSource.{u,v} k profile
    let D := colouredOrderedEdgeTarget k oldEdges colour
    let P := Quotient (T.wagonSetoid μ)
    let carrier : P → Set V :=
      T.wagonClassCarrier
        (fun e : {e : Set V // e ∈ supportCopies A D} => e.1) μ
    letI : LinearOrder P := T.wagonQuotientLinearOrder μ
    ∀ e f : Set (FirstWagonUnionVertex carrier),
      e ∈ supportCopies A
        (completedFirstWagonColouredUnion k oldEdges colour carrier) →
      f ∈ supportCopies A
        (completedFirstWagonColouredUnion k oldEdges colour carrier) →
      e ≠ f →
      e ∩ f ⊆ {z | colour z.2.1 ∈ allowed} := by
  classical
  let A := colouredOrderedEdgeSource.{u,v} k profile
  let D := colouredOrderedEdgeTarget k oldEdges colour
  let E := {e : Set V // e ∈ supportCopies A D}
  let P := Quotient (T.wagonSetoid μ)
  let oldEdgesFn : E → Set V := fun e => e.1
  let carrier : P → Set V := T.wagonClassCarrier oldEdgesFn μ
  let owner : E → P := T.wagonClassOwner μ
  letI : Finite E := inferInstance
  letI : LinearOrder P := T.wagonQuotientLinearOrder μ
  have hTwo : Nontrivial (ULift.{v} (Fin k)) := by
    refine ⟨⟨ULift.up (⟨0, by omega⟩ : Fin k),
      ULift.up (⟨1, by omega⟩ : Fin k), ?_⟩⟩
    intro hEq
    have h01 : (0 : Nat) = 1 :=
      congrArg (fun z : ULift.{v} (Fin k) => z.down.val) hEq
    omega
  letI : Nontrivial (ULift.{v} (Fin k)) := hTwo
  have hCarrierLinear :
      ∀ p q : P, p ≠ q →
        (carrier p ∩ carrier q).Subsingleton :=
    (T.actualWagon_EHN_source_of_bound A D μ g hg hGirth).1
  have hOwnerCarrier : ∀ e : E, e.1 ⊆ carrier (owner e) := by
    intro e
    exact T.edge_subset_ownerWagonCarrier oldEdgesFn μ e
  have hLocal :
      ∀ p : P, ∀ e f : Set {x : V // x ∈ carrier p},
        e ∈ supportCopies A (D.induce (carrier p)) →
        f ∈ supportCopies A (D.induce (carrier p)) →
        e ≠ f → e ∩ f ⊆ {x | colour x.1 ∈ allowed} := by
    intro p e f he hf hne z hz
    let ep : OriginalFirstWagonEdges A D carrier :=
      ⟨p, ⟨e, he⟩⟩
    let fp : OriginalFirstWagonEdges A D carrier :=
      ⟨p, ⟨f, hf⟩⟩
    let eOld : E := firstWagonEdgeToOriginal A D carrier ep
    let fOld : E := firstWagonEdgeToOriginal A D carrier fp
    have hDistinct : eOld ≠ fOld := by
      intro hh
      have hPair : ep = fp :=
        firstWagonEdgeToOriginal_injective A D carrier owner
          hOwnerCarrier hCarrierLinear hh
      exact hne (congrArg
        (fun z : OriginalFirstWagonEdges A D carrier => z.2.1)
        hPair)
    have hOwnerE : owner eOld = p :=
      firstWagonEdgeToOriginal_owner A D carrier owner
        hOwnerCarrier hCarrierLinear ep
    have hOwnerF : owner fOld = p :=
      firstWagonEdgeToOriginal_owner A D carrier owner
        hOwnerCarrier hCarrierLinear fp
    have hSameWagon : T.rel μ eOld fOld :=
      Quotient.exact (hOwnerE.trans hOwnerF.symm)
    have hOriginalAllowed :
        eOld.1 ∩ fOld.1 ⊆ {x : V | colour x ∈ allowed} :=
      hOriginalParam eOld fOld hDistinct hSameWagon
    have hZe : z.1 ∈ eOld.1 := by
      change z.1 ∈ Subtype.val '' e
      exact ⟨z, hz.1, rfl⟩
    have hZf : z.1 ∈ fOld.1 := by
      change z.1 ∈ Subtype.val '' f
      exact ⟨z, hz.2, rfl⟩
    exact hOriginalAllowed ⟨hZe, hZf⟩
  exact completedFirstWagon_support_inter_allowed
    k hk profile oldEdges colour carrier allowed hLocal

end StructuralRamsey.Girth
