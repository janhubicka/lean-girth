import Girth.ACopyDecoratedStar

set_option autoImplicit false

/-!
# Full induced node domains give faithful node carriers

The decorated star already identifies points and basic nodes independently.
Here every source node carrier is faithful before gluing. A source node whose
whole carrier belongs to the shared point domain must be a shared node.
These source-local hypotheses imply injectivity of output node carriers,
without assuming output linearity or any statement about actual relational
copies. Retained point records and cross-source point contacts are unchanged.
-/

namespace StructuralRamsey.Girth.ACopyFullDomain

open ACopyLayeredStar ACopyDecoratedStar

universe v
variable {C I K PC : Type v} {S Q PS PQ : I → Type v}
variable {N : Diagram C I S Q} (D : Data N K PC PS PQ)

def coreNodeCarrier (e : C) : Set (Quotient D.coreEq) :=
  Set.range (fun a => Quotient.mk D.coreEq (D.coreCoord e a))

def sourceNodeCarrier (i : I) (e : S i) : Set (Quotient (D.sourceEq i)) :=
  Set.range (fun a => Quotient.mk (D.sourceEq i) (D.sourceCoord i e a))

def sharedSourcePoints (i : I) : Set (Quotient (D.sourceEq i)) :=
  Set.range (fun q => Quotient.mk (D.sourceEq i) (D.beta i q))

/-- This is fullness of the NODE domain, not coverage of shared points by
some shared nodes. The carrier and shared domain live in the original source. -/
def FullNodeDomains : Prop :=
  ∀ i e, sourceNodeCarrier D i e ⊆ sharedSourcePoints D i →
    ∃ q : Q i, N.beta i q = e

def nodeCarrier (e : Node N) : Set D.Point := Set.range (D.nodePoint e)

theorem nodeCarrier_core_subset (e : C) :
    nodeCarrier D (nodeCore N e) ⊆ D.coreImage := by
  rintro p ⟨a, rfl⟩
  exact ⟨D.coreCoord e a, rfl⟩

theorem nodeCarrier_source_subset (i : I) (e : S i) :
    nodeCarrier D (nodeSource N i e) ⊆ D.sourceImage i := by
  rintro p ⟨a, rfl⟩
  exact ⟨D.sourceCoord i e a, rfl⟩

theorem core_carrier_eq_iff (e f : C) :
    nodeCarrier D (nodeCore N e) = nodeCarrier D (nodeCore N f) ↔
      coreNodeCarrier D e = coreNodeCarrier D f := by
  change Set.range (fun a => D.coreMap (Quotient.mk D.coreEq (D.coreCoord e a))) =
      Set.range (fun a => D.coreMap (Quotient.mk D.coreEq (D.coreCoord f a))) ↔ _
  rw [Set.range_comp' D.coreMap, Set.range_comp' D.coreMap]
  exact (Set.image_injective.mpr D.coreMap_injective).eq_iff

theorem source_carrier_eq_iff (i : I) (e f : S i) :
    nodeCarrier D (nodeSource N i e) = nodeCarrier D (nodeSource N i f) ↔
      sourceNodeCarrier D i e = sourceNodeCarrier D i f := by
  change Set.range (fun a => D.sourceMap i
      (Quotient.mk (D.sourceEq i) (D.sourceCoord i e a))) =
      Set.range (fun a => D.sourceMap i
      (Quotient.mk (D.sourceEq i) (D.sourceCoord i f a))) ↔ _
  rw [Set.range_comp' (D.sourceMap i), Set.range_comp' (D.sourceMap i)]
  exact (Set.image_injective.mpr (D.sourceMap_injective i)).eq_iff

/-- Exact point intersection turns containment in the output core into
containment in the original shared point domain. -/
theorem source_node_shared_of_subset_core
    (hFull : FullNodeDomains D) (i : I) (e : S i)
    (hInside : nodeCarrier D (nodeSource N i e) ⊆ D.coreImage) :
    ∃ q : Q i, N.beta i q = e := by
  apply hFull i e
  rintro p ⟨a, rfl⟩
  obtain ⟨c, hc⟩ := hInside ⟨a, rfl⟩
  obtain ⟨q, hq, _⟩ :=
    (D.sourceRecord_eq_coreRecord_iff i (D.sourceCoord i e a) c).mp hc.symm
  exact ⟨q, Quotient.sound hq⟩

theorem source_node_eq_core_of_carrier_eq
    (hCore : Function.Injective (coreNodeCarrier D))
    (hFull : FullNodeDomains D) (i : I) (e : S i) (f : C)
    (h : nodeCarrier D (nodeSource N i e) = nodeCarrier D (nodeCore N f)) :
    nodeSource N i e = nodeCore N f := by
  obtain ⟨q, rfl⟩ := source_node_shared_of_subset_core D hFull i e
    (h ▸ nodeCarrier_core_subset D f)
  have hNode : nodeSource N i (N.beta i q) = nodeCore N (N.alpha i q) :=
    Quot.sound (ACopyExactStar.SourceStar.Step.shared i q)
  have hCoreEq := hCore ((core_carrier_eq_iff D (N.alpha i q) f).mp
    ((congrArg (nodeCarrier D) hNode).symm.trans h))
  exact hNode.trans (congrArg (nodeCore N) hCoreEq)

/-- Equal carriers force equal quotient nodes. All hypotheses concern
original source carriers and full shared node domains; output linearity is
neither assumed nor derived here. -/
theorem nodeCarrier_injective
    (hCore : Function.Injective (coreNodeCarrier D))
    (hSource : ∀ i, Function.Injective (sourceNodeCarrier D i))
    (hFull : FullNodeDomains D) : Function.Injective (nodeCarrier D) := by
  intro x y
  refine Quot.inductionOn x ?_
  intro a
  refine Quot.inductionOn y ?_
  intro b h
  cases a with
  | inl e =>
      cases b with
      | inl f =>
          exact congrArg (nodeCore N) (hCore ((core_carrier_eq_iff D e f).mp h))
      | inr t =>
          rcases t with ⟨i, f⟩
          exact (source_node_eq_core_of_carrier_eq D hCore hFull i f e h.symm).symm
  | inr t =>
      rcases t with ⟨i, e⟩
      cases b with
      | inl f => exact source_node_eq_core_of_carrier_eq D hCore hFull i e f h
      | inr t =>
          rcases t with ⟨j, f⟩
          by_cases hij : i = j
          · subst j
            exact congrArg (nodeSource N i)
              (hSource i ((source_carrier_eq_iff D i e f).mp h))
          · have hInside : nodeCarrier D (nodeSource N i e) ⊆ D.coreImage := by
              intro p hp
              have hi := nodeCarrier_source_subset D i e hp
              have hj := nodeCarrier_source_subset D j f (h ▸ hp)
              have hs : p ∈ D.sharedImage i ∩ D.sharedImage j :=
                D.distinct_sourceImage_inter i j hij ▸ ⟨hi, hj⟩
              obtain ⟨q, hq⟩ := hs.1
              exact ⟨D.alpha i q, hq⟩
            obtain ⟨q, rfl⟩ := source_node_shared_of_subset_core D hFull i e hInside
            have hNode : nodeSource N i (N.beta i q) = nodeCore N (N.alpha i q) :=
              Quot.sound (ACopyExactStar.SourceStar.Step.shared i q)
            have hOther := source_node_eq_core_of_carrier_eq D hCore hFull j f
              (N.alpha i q) (h.symm.trans (congrArg (nodeCarrier D) hNode))
            exact hNode.trans hOther.symm

theorem nodeCarrier_eq_iff
    (hCore : Function.Injective (coreNodeCarrier D))
    (hSource : ∀ i, Function.Injective (sourceNodeCarrier D i))
    (hFull : FullNodeDomains D) (e f : Node N) :
    nodeCarrier D e = nodeCarrier D f ↔ e = f :=
  (nodeCarrier_injective D hCore hSource hFull).eq_iff

end StructuralRamsey.Girth.ACopyFullDomain
