import Girth.ContactForestBoostClass
import Girth.ContactImageDedup

/-! The manuscript's one-representative-per-image convention for
the class-wide forest boost. The internal induction may retain
separate labels; deduplicating the final actual witness preserves
all required invariants and the Ramsey arrow. -/

namespace StructuralRamsey.Girth
universe v

namespace ContactBoostInput
variable {P : Type v} [LinearOrder P] [Nontrivial P]
    {m : ℕ} {allowed : Fin m → Set P} {q : Fin (m+1) → ℕ}
    {A : ContactBoostInput P m allowed q} {Color : Type v}

namespace Witness
variable (W : A.Witness Color)

theorem edge_nontrivial (e : W.out.Edge) :
    (W.out.graph.edgeCarrier e).Nontrivial := by
  obtain ⟨i,j,hij⟩ := exists_pair_ne P
  let ep := W.out.endpoints
  exact ⟨ep.endpoint e i,ep.endpoint_mem e i,ep.endpoint e j,
    ep.endpoint_mem e j,fun he => hij (ep.endpoint_inj e he)⟩

noncomputable def dedup : A.Witness Color := by
  let H := W.out.graph
  let ep := W.out.endpoints
  letI : Finite W.out.Copy := W.finiteC
  letI : Finite H.ImageLabel := Finite.of_surjective
    (fun i : W.out.Copy => (⟨H.copyCarrier i,⟨i,rfl⟩⟩ : H.ImageLabel))
    (by
      intro c
      exact ⟨Classical.choose c.property,Subtype.ext (Classical.choose_spec c.property)⟩)
  exact {
    out := {
      Vertex := W.out.Vertex
      Edge := W.out.Edge
      Copy := H.ImageLabel
      finiteV := W.out.finiteV
      finiteE := W.out.finiteE
      nonemptyE := W.out.nonemptyE
      graph := H.dedup
      train := W.out.train
      endpoints := {
        part := ep.part
        endpoint := ep.endpoint
        part_endpoint := ep.part_endpoint
        carrier_eq := ep.carrier_eq
        covered := ep.covered }
      order := W.out.order
      part_mono := W.out.part_mono
      linear := W.out.linear
      parameters := W.out.parameters
      positiveWagons := W.out.positiveWagons }
    finiteC := inferInstance
    family := W.family.dedup
    emb_part := fun c x => W.emb_part (H.imageRep c) x
    emb_order := fun c x y h => W.emb_order (H.imageRep c) x y h
    positive := H.dedup_positiveBounds W.out.train q W.positive W.edge_nontrivial
    arrow := W.family.dedup_arrow W.edge_nontrivial W.arrow }

theorem dedup_smallForests {j : ℕ}
    (h : W.out.graph.bottomCut.ZeroSmallMixedForestsThrough j) :
    W.dedup.out.graph.bottomCut.ZeroSmallMixedForestsThrough j :=
  W.out.graph.bottomCut.dedup_smallForests h

theorem dedup_injective : Function.Injective W.dedup.out.graph.copyCarrier :=
  Subtype.val_injective

end Witness

/-- The exact forest-boost statement including distinct copy
images. All the nontrivial geometry is in forestBoost; this last
step retains one actual representative of every designated image. -/
theorem forestBoost_distinctImages [Finite P]
    [Finite Color] [Nonempty Color]
    (hm : 0 < m) (hq : ∀ μ, μ.val < m → 2 ≤ q μ)
    (hG : ∀ B : ContactBoostInput P m allowed q, LabelledGirthGT B.graph.edgeCarrier (q 0))
    (base : ∀ B : ContactBoostInput P m allowed q, Nonempty (B.Witness Color))
    (n : ℕ) (hn : n+1 ≤ q 0) (B : ContactBoostInput P m allowed q) :
    ∃ W : B.Witness Color,
      W.out.graph.bottomCut.ZeroSmallMixedForestsThrough (n+1) ∧
      Function.Injective W.out.graph.copyCarrier := by
  obtain ⟨W,hW⟩ := forestBoost hm hq hG base n hn B
  exact ⟨W.dedup,W.dedup_smallForests hW,W.dedup_injective⟩

end ContactBoostInput
end StructuralRamsey.Girth
