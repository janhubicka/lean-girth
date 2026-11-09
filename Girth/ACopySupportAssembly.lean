import Girth.ACopyFullDomain
import Girth.ACopyChartCoverage

set_option autoImplicit false

/-!
# A-copy support assembly

This module composes two *different* obligations in the decorated picture.

* Actual irreducible chart coverage and complete source-chart A-copy recording
  imply that every actual A-copy of the free realization is represented by a
  designated physical node.
* The source-local full-node-domain hypotheses of the decorated star make
  the resulting map of quotient nodes to actual point carriers injective.

The conclusion is an equivalence with **physical image copies**, not with
labelled designated B-charts or all parameterized embeddings. In particular
we do not assume output linearity, and do not infer the existence of relational
chart embeddings from abstract overlap setoids.
-/

namespace StructuralRamsey.Girth.ACopySupportAssembly

open StructuralRamsey.RelStructure
open ACopyChartCoverage
open ACopyLayeredStar ACopyDecoratedStar ACopyFullDomain

universe u v

variable {L : RelLanguage.{u}}
variable {J K W : Type v} {V : J → Type v}
variable {A : RelStructure L K} {H : RelStructure L W}
variable {C : ∀ j, RelStructure L (V j)}

/-- Genuine induced chart coverage and complete local node recording imply
surjectivity of the physical-node carrier family. This is a statement about
actual relational copies, not abstract overlap coordinates. -/
theorem support_range_of_chartwise_nodes
    {Ω : Type v}
    (chart : ∀ j, Embedding (C j) H)
    (hCover : CoversIrreducibles chart)
    (hA : A.Irreducible)
    (node : Ω → Embedding A H)
    (hLocal : ∀ j (b : Embedding A (C j)),
      ∃ e : Ω, SameCopy ((chart j).comp b) (node e)) :
    Set.range (fun e => copyCarrier (node e)) = supportCopies A H := by
  apply Set.Subset.antisymm
  · rintro S ⟨e, rfl⟩
    exact ⟨node e, rfl⟩
  · rintro S ⟨a, rfl⟩
    obtain ⟨j, b, hjb⟩ := factors_through_chart chart hCover hA a
    obtain ⟨e, he⟩ := hLocal j b
    refine ⟨e, ?_⟩
    change copyCarrier (node e) = copyCarrier a
    rw [← hjb]
    exact he.symm

/-- Exact support without output linearity. The injectivity input can be
supplied by the decorated-star full induced-domain theorem below. -/
noncomputable def supportEquiv
    {Ω : Type v}
    (chart : ∀ j, Embedding (C j) H)
    (hCover : CoversIrreducibles chart)
    (hA : A.Irreducible)
    (node : Ω → Embedding A H)
    (hLocal : ∀ j (b : Embedding A (C j)),
      ∃ e : Ω, SameCopy ((chart j).comp b) (node e))
    (hInject : Function.Injective (fun e => copyCarrier (node e))) :
    Ω ≃ supportCopies A H := by
  let f : Ω → supportCopies A H := fun e =>
    ⟨copyCarrier (node e), ⟨node e, rfl⟩⟩
  apply Equiv.ofBijective f
  constructor
  · intro e₁ e₂ h
    apply hInject
    exact congrArg Subtype.val h
  · rintro ⟨S, hS⟩
    have hr : S ∈ Set.range (fun e => copyCarrier (node e)) := by
      rw [support_range_of_chartwise_nodes chart hCover hA node hLocal]
      exact hS
    obtain ⟨e, he⟩ := hr
    refine ⟨e, ?_⟩
    apply Subtype.ext
    exact he

variable {Core Index PC : Type v}
variable {Sources Shared PS PQ : Index → Type v}
variable {N : Diagram Core Index Sources Shared}
variable (D : Data N K PC PS PQ)

/-- The carrier of an actual embedding is exactly the carrier of the node's
decorated coordinates. The latter retain no assumption about its relations. -/
theorem copyCarrier_eq_nodeCarrier
    {H' : RelStructure L D.Point} {A' : RelStructure L K}
    (node : Node N → Embedding A' H')
    (hCoord : ∀ e a, node e a = D.nodePoint e a)
    (e : Node N) :
    copyCarrier (node e) = nodeCarrier D e := by
  change Set.range (node e) = Set.range (D.nodePoint e)
  ext p
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨a, (hCoord e a).symm⟩
  · rintro ⟨a, rfl⟩
    exact ⟨a, hCoord e a⟩

/-- Full induced node domains exclude accidental duplication of *physical*
A-copies in the decorated point quotient. In particular, no output
linearity or no-new-edge claim is needed for this injection. -/
theorem physicalNodeCarrier_injective
    {H' : RelStructure L D.Point} {A' : RelStructure L K}
    (node : Node N → Embedding A' H')
    (hCoord : ∀ e a, node e a = D.nodePoint e a)
    (hCore : Function.Injective (coreNodeCarrier D))
    (hSource : ∀ i, Function.Injective (sourceNodeCarrier D i))
    (hFull : FullNodeDomains D) :
    Function.Injective (fun e => copyCarrier (node e)) := by
  intro e f h
  apply nodeCarrier_injective D hCore hSource hFull
  exact (copyCarrier_eq_nodeCarrier D node hCoord e).symm.trans
    (h.trans (copyCarrier_eq_nodeCarrier D node hCoord f))

/-- Concrete composition: if the induced relational chart embeddings cover
irreducibles and record each source A-copy, then the generated quotient-node
family is *exactly* the full actual physical A-support.

The hypotheses explicitly leave construction of the induced chart embeddings
and the chartwise recording/coverage property to the genuine picture step.
The result does not validate that still-open geometric construction. -/
noncomputable def decoratedSupportEquiv
    {H' : RelStructure L D.Point} {A' : RelStructure L K}
    {J' : Type v} {V' : J' → Type v}
    {C' : ∀ j, RelStructure L (V' j)}
    (chart : ∀ j, Embedding (C' j) H')
    (hCover : CoversIrreducibles chart)
    (hA : A'.Irreducible)
    (node : Node N → Embedding A' H')
    (hCoord : ∀ e a, node e a = D.nodePoint e a)
    (hCore : Function.Injective (coreNodeCarrier D))
    (hSource : ∀ i, Function.Injective (sourceNodeCarrier D i))
    (hFull : FullNodeDomains D)
    (hLocal : ∀ j (b : Embedding A' (C' j)),
      ∃ e : Node N, SameCopy ((chart j).comp b) (node e)) :
    Node N ≃ supportCopies A' H' :=
  supportEquiv chart hCover hA node hLocal
    (physicalNodeCarrier_injective D node hCoord hCore hSource hFull)

end StructuralRamsey.Girth.ACopySupportAssembly
