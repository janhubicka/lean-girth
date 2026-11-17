import Girth.CoveredPictureOrderReduct
import Girth.FiniteTraceOrderReduct

/-! # Uniform hypergraphs obtained from the covered ordered picture -/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe v
variable {VB P X : Type v}

/-- The physical hyperedges are the ranges of the positive tuples in the
one-symbol reduct. -/
def uniformRelationEdgeCarriers (k : ℕ) (R : RelStructure (uniformEdgeLanguage k) X) :
    Set (Set X) :=
  {e | ∃ t : Fin k → X, R.rel () t ∧ Set.range t = e}

/-- Coverage by induced copies of a uniform hypergraph makes the reduct a
uniform hypergraph itself. This uses only the original relation on the
target, even if some pairs of ambient vertices are incomparable. -/
theorem uniformPicture_orderReduct_eq
    (k : ℕ) (E : Set (Set VB)) [LinearOrder VB]
    {D : RelStructure (uniformEdgeLanguage k).withOrder P}
    {C : StructuralRamsey.Partite.System (uniformEdgeLanguage k).withOrder P X}
    {family : Set (Embedding (uniformEdgeTarget k E).ordered D)}
    (hCover : DesignatedCoversIrreducibles (uniformEdgeTarget k E).ordered D C family) :
    C.toRelStructure.orderReduct =
      uniformEdgeTarget k (uniformRelationEdgeCarriers k C.toRelStructure.orderReduct) := by
  classical
  let R := C.toRelStructure.orderReduct
  have coversTuple (t : Fin k → X) (ht : R.rel () t) :
      ∃ q : DesignatedCopy (uniformEdgeTarget k E).ordered D C family,
        ∀ x ∈ Set.range t, ∃ b : VB, q.embedding b = x := by
    have hIrr : (C.toRelStructure.induce (Set.range t)).Irreducible := by
      intro x y _
      obtain ⟨i, hi⟩ := x.property
      obtain ⟨j, hj⟩ := y.property
      let s (a : Fin k) : Set.range t := ⟨t a, ⟨a, rfl⟩⟩
      exact ⟨.inl (), s, i, j, ht, Subtype.ext hi, Subtype.ext hj⟩
    obtain ⟨q, hq⟩ := hCover (Set.range t) hIrr
    exact ⟨q, fun x hx => ⟨Classical.choose (hq ⟨x, hx⟩),
      (Classical.choose_spec (hq ⟨x, hx⟩)).symm⟩⟩
  have inducedTuple (q : DesignatedCopy (uniformEdgeTarget k E).ordered D C family)
      (t : Fin k → VB) : R.rel () (q.embedding ∘ t) ↔
        Function.Injective t ∧ Set.range t ∈ E :=
    q.embedding.map_rel_iff (.inl ()) t
  apply congrArg RelStructure.mk
  funext r t
  apply propext
  cases r
  change R.rel () t ↔ Function.Injective t ∧ Set.range t ∈ uniformRelationEdgeCarriers k R
  constructor
  · intro ht
    obtain ⟨q, hq⟩ := coversTuple t ht
    let s (i : Fin k) := Classical.choose (hq (t i) ⟨i, rfl⟩)
    have hs : q.embedding ∘ s = t := funext fun i => Classical.choose_spec (hq (t i) ⟨i, rfl⟩)
    have hInj := ((inducedTuple q s).mp (hs.symm ▸ ht)).1
    exact ⟨hs ▸ q.embedding.injective.comp hInj, ⟨t, ht, rfl⟩⟩
  · rintro ⟨ht, u, hu, hRange⟩
    obtain ⟨q, hq⟩ := coversTuple u hu
    let s (i : Fin k) := Classical.choose (hq (u i) ⟨i, rfl⟩)
    have hs : q.embedding ∘ s = u := funext fun i => Classical.choose_spec (hq (u i) ⟨i, rfl⟩)
    have htMem (i : Fin k) : t i ∈ Set.range u := hRange.symm ▸ ⟨i, rfl⟩
    let w (i : Fin k) := Classical.choose (hq (t i) (htMem i))
    have hw : q.embedding ∘ w = t := funext fun i => Classical.choose_spec (hq (t i) (htMem i))
    have hPreimage : Set.range s = Set.range w := by
      apply q.embedding.injective.image_injective
      calc
        q.embedding '' Set.range s = Set.range (q.embedding ∘ s) := (Set.range_comp _ _).symm
        _ = Set.range u := congrArg Set.range hs
        _ = Set.range t := hRange
        _ = Set.range (q.embedding ∘ w) := congrArg Set.range hw.symm
        _ = q.embedding '' Set.range w := Set.range_comp _ _
    have hwInj : Function.Injective w := by
      intro i j h
      apply ht
      rw [← hw]
      exact congrArg q.embedding h
    have hEdge := ((inducedTuple q s).mp (hs.symm ▸ hu)).2
    exact hw ▸ (inducedTuple q w).mpr ⟨hwInj, hPreimage ▸ hEdge⟩

/-- The physical hyperedges of the reduct are exactly the ordered picture's
ambient support, so the ordered girth and strong inducedness transfer. -/
theorem uniformPicture_edgeCarriers_eq_orderedSupport
    (k : ℕ) (E : Set (Set VB)) [Finite VB] [LinearOrder VB]
    (hUniform : ∀ e ∈ E, e.ncard = k)
    {D : RelStructure (uniformEdgeLanguage k).withOrder P}
    {C : StructuralRamsey.Partite.System (uniformEdgeLanguage k).withOrder P X}
    {family : Set (Embedding (uniformEdgeTarget k E).ordered D)}
    (hCover : DesignatedCoversIrreducibles (uniformEdgeTarget k E).ordered D C family) :
    uniformRelationEdgeCarriers k C.toRelStructure.orderReduct =
      supportCopies (uniformEdgeSource k).ordered C.toRelStructure := by
  have hReductSupport := uniformEdgeSupport_orderReduct_eq_of_designatedCover k E hUniform hCover
  rw [← hReductSupport]
  let R := C.toRelStructure.orderReduct
  let H := uniformRelationEdgeCarriers k R
  have hR : R = uniformEdgeTarget k H := uniformPicture_orderReduct_eq k E hCover
  have hEnumerate (e : Set X) (he : e ∈ H) :
      ∃ i : Fin k ↪ X, Set.range (i : Fin k → X) = e := by
    obtain ⟨t, ht, hEq⟩ := he
    have hInj : Function.Injective t := by
      rw [hR] at ht
      exact ht.1
    exact ⟨⟨t, hInj⟩, hEq⟩
  change H = supportCopies (uniformEdgeSource k) R
  exact (uniformEdgeSupport_exact k H hEnumerate).symm.trans
    (congrArg (supportCopies (uniformEdgeSource k)) hR.symm)

/-- Girth and strong inducedness hold for the actual unordered hyperedges
and the carriers of all designated copies. -/
theorem uniformPicture_girthStrong_orderReduct
    (k : ℕ) (E : Set (Set VB)) [Finite VB] [LinearOrder VB]
    (hUniform : ∀ e ∈ E, e.ncard = k)
    {D : RelStructure (uniformEdgeLanguage k).withOrder P}
    {C : StructuralRamsey.Partite.System (uniformEdgeLanguage k).withOrder P X}
    {family : Set (Embedding (uniformEdgeTarget k E).ordered D)}
    (hCover : DesignatedCoversIrreducibles (uniformEdgeTarget k E).ordered D C family)
    (g : ℕ)
    (hGirth : GirthGT (supportCopies (uniformEdgeSource k).ordered C.toRelStructure) g)
    (hStrong : ∀ f : DesignatedCopy (uniformEdgeTarget k E).ordered D C family,
      AStrong (uniformEdgeSource k).ordered C.toRelStructure (copyCarrier f.embedding)) :
    GirthGT (uniformRelationEdgeCarriers k C.toRelStructure.orderReduct) g ∧
      ∀ (f : DesignatedCopy (uniformEdgeTarget k E).ordered D C family) (e : Set X),
        e ∈ uniformRelationEdgeCarriers k C.toRelStructure.orderReduct →
        ¬ (e ∩ copyCarrier f.embedding).Subsingleton → e ⊆ copyCarrier f.embedding := by
  rw [uniformPicture_edgeCarriers_eq_orderedSupport k E hUniform hCover]
  exact ⟨hGirth, by
    intro f e he hNontrivial
    obtain ⟨a, rfl⟩ := he
    exact hStrong f a hNontrivial⟩

/-- The designated target copies cover all vertices and physical
hyperedges of the unordered witness. -/
theorem uniformPicture_designatedCover_orderReduct
    (k : ℕ) (E : Set (Set VB)) [Finite VB] [LinearOrder VB]
    (hUniform : ∀ e ∈ E, e.ncard = k)
    {D : RelStructure (uniformEdgeLanguage k).withOrder P}
    {C : StructuralRamsey.Partite.System (uniformEdgeLanguage k).withOrder P X}
    {family : Set (Embedding (uniformEdgeTarget k E).ordered D)}
    (hCover : DesignatedCoversIrreducibles (uniformEdgeTarget k E).ordered D C family) :
    (∀ x : X, ∃ b : DesignatedCopy (uniformEdgeTarget k E).ordered D C family,
      x ∈ copyCarrier b.embedding) ∧
    (∀ e ∈ uniformRelationEdgeCarriers k C.toRelStructure.orderReduct,
      ∃ b : DesignatedCopy (uniformEdgeTarget k E).ordered D C family,
        e ⊆ copyCarrier b.embedding) := by
  constructor
  · intro x
    have hIrr : (C.toRelStructure.induce ({x} : Set X)).Irreducible := by
      intro u w hne
      exact False.elim (hne (Subtype.ext (Set.subsingleton_singleton u.property w.property)))
    obtain ⟨b, hb⟩ := hCover {x} hIrr
    obtain ⟨v, hv⟩ := hb ⟨x, Set.mem_singleton x⟩
    exact ⟨b, ⟨v, hv.symm⟩⟩
  · rw [uniformPicture_edgeCarriers_eq_orderedSupport k E hUniform hCover]
    rintro e ⟨a, rfl⟩
    obtain ⟨b, hb⟩ := hCover (copyCarrier a)
      ((orderedUniformEdgeSource_irreducible k).range_embedding a)
    exact ⟨b, fun x hx => let ⟨v, hv⟩ := hb ⟨x, hx⟩; ⟨v, hv.symm⟩⟩

/-- A designated ordered arrow becomes an arrow on unordered edge carriers
with the very same designated choice. -/
theorem uniformPicture_selectedArrow_orderReduct
    (k : ℕ) (E : Set (Set VB)) [Finite VB] [LinearOrder VB]
    (hUniform : ∀ e ∈ E, e.ncard = k)
    {D : RelStructure (uniformEdgeLanguage k).withOrder P}
    {C : StructuralRamsey.Partite.System (uniformEdgeLanguage k).withOrder P X}
    {family : Set (Embedding (uniformEdgeTarget k E).ordered D)} (κ : Type*)
    (hArrow : ∀ χ : Embedding (uniformEdgeSource.{v} k).ordered C.toRelStructure → κ,
      ∃ b : DesignatedCopy (uniformEdgeTarget k E).ordered D C family,
        ∀ g h : Embedding (uniformEdgeSource.{v} k).ordered (uniformEdgeTarget k E).ordered,
          χ (b.embedding.comp g) = χ (b.embedding.comp h)) :
    ∀ χ : supportCopies (uniformEdgeSource.{v} k) C.toRelStructure.orderReduct → κ,
      ∃ b : DesignatedCopy (uniformEdgeTarget k E).ordered D C family,
        ∀ g h : Embedding (uniformEdgeSource.{v} k) (uniformEdgeTarget k E),
          χ ⟨copyCarrier (b.embedding.orderReduct.comp g), ⟨_, rfl⟩⟩ =
            χ ⟨copyCarrier (b.embedding.orderReduct.comp h), ⟨_, rfl⟩⟩ := by
  intro χ
  let chosen (f : Embedding (uniformEdgeTarget k E).ordered C.toRelStructure) :=
    ∃ b : DesignatedCopy (uniformEdgeTarget k E).ordered D C family, f = b.embedding
  have hSelected (χ' : Embedding (uniformEdgeSource.{v} k).ordered C.toRelStructure → κ) :
      ∃ f, chosen f ∧ ∀ g h, χ' (f.comp g) = χ' (f.comp h) := by
    obtain ⟨b, hb⟩ := hArrow χ'
    exact ⟨b.embedding, ⟨b, rfl⟩, hb⟩
  obtain ⟨_, ⟨b, rfl⟩, h⟩ := selectedArrow_orderReduct_carriers
    (A := (uniformEdgeSource.{v} k).ordered) (B := (uniformEdgeTarget k E).ordered)
    (C := C.toRelStructure) (chosen := chosen) hSelected
    (orderedUniformEdge_carrierLift k E hUniform) χ
  exact ⟨b, h⟩

/-- The actual picture gives the small induced subhypergraph conclusion
for any finite uniform target with at least one edge of size at least two. -/
theorem uniformPicture_smallInduced_orderReduct
    (k : ℕ) (hk : 2 ≤ k) (E : Set (Set VB)) [Finite VB] [LinearOrder VB]
    (hUniform : ∀ e ∈ E, e.ncard = k) (hEdge : E.Nonempty) [Finite X]
    {D : RelStructure (uniformEdgeLanguage k).withOrder P}
    {C : StructuralRamsey.Partite.System (uniformEdgeLanguage k).withOrder P X}
    {family : Set (Embedding (uniformEdgeTarget k E).ordered D)}
    (hCover : DesignatedCoversIrreducibles (uniformEdgeTarget k E).ordered D C family)
    (hShared : DesignatedSharedSupport (uniformEdgeSource k).ordered C family)
    (q : ℕ) (hq : 1 ≤ q)
    (hComplete : ForestCompletionProperty
      (testedPictureABSupport (uniformEdgeSource k).ordered (uniformEdgeTarget k E).ordered D C family)
      (designatedPictureASupport (uniformEdgeSource k).ordered (uniformEdgeTarget k E).ordered D C family) q)
    (Z : Set X) (hBudget : Z.ncard ≤ q) :
    ∃ (Y : Type v) (T : RelStructure (uniformEdgeLanguage k) Y)
      (_ : Embedding (C.toRelStructure.orderReduct.induce Z) T),
        ASupportedTreeAmalgam (uniformEdgeSource k) (uniformEdgeTarget k E) Y T := by
  obtain ⟨e, he⟩ := hEdge
  have he' : e ∈ supportCopies (uniformEdgeSource k).ordered (uniformEdgeTarget k E).ordered := by
    rwa [orderedUniformEdgeSupport_exact k E hUniform]
  obtain ⟨alpha, -⟩ := he'
  let a₀ : ULift.{v} (Fin k) := ⟨⟨0, by omega⟩⟩
  let a₁ : ULift.{v} (Fin k) := ⟨⟨1, by omega⟩⟩
  have hne : a₀ ≠ a₁ := fun h => Nat.zero_ne_one (congrArg (fun a => a.down.val) h)
  exact smallInducedStructure_orderReduct_of_assembledPicture
    (uniformEdgeSource k).ordered (uniformEdgeTarget k E).ordered D C family
    hCover hShared q hq hComplete Z hBudget alpha a₀ a₁ hne

/-- For the edgeless target one can use the target itself. The carrier
colouring is vacuous and each induced subhypergraph embeds into one copy. -/
theorem edgelessUniformPicture_consequence
    (k : ℕ) (κ : Type*) (Z : Set VB) :
    let B := uniformEdgeTarget k (∅ : Set (Set VB))
    (∀ χ : supportCopies (uniformEdgeSource k) B → κ,
      ∃ f : Embedding B B, ∀ g h : Embedding (uniformEdgeSource k) B,
        χ ⟨copyCarrier (f.comp g), ⟨f.comp g, rfl⟩⟩ =
          χ ⟨copyCarrier (f.comp h), ⟨f.comp h, rfl⟩⟩) ∧
    (∃ (Y : Type v) (T : RelStructure (uniformEdgeLanguage k) Y)
      (_ : Embedding (B.induce Z) T),
        ASupportedTreeAmalgam (uniformEdgeSource k) B Y T) := by
  dsimp only
  refine ⟨fun _ => ⟨(Iso.refl _).toEmbedding, fun g _ => ?_⟩, ?_⟩
  · exact (Set.notMem_empty _ (uniformEdgeEmbedding_carrier_mem k ∅ g)).elim
  · exact smallInducedStructure_embeds_supportedTree_in_target _ _ Z

end StructuralRamsey.Girth
