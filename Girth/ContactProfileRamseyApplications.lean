import Girth.ContactProfileRamseyInduction
import Girth.ContactImageDedup

/-! The final train theorem in the manuscript's convention of one
designated copy per vertex image. The height-one consequence is the
ordered hypergraph forest Ramsey statement before the optional
restriction to covered designated copies and isolated-vertex padding.
-/

namespace StructuralRamsey.Girth
universe v

namespace ContactProfileTrain
variable {P : Type v} [LinearOrder P] {m a : ℕ}
    {allowed : Fin m → Set P} {word : Fin a → P}
    {A : ContactProfileTrain P m a allowed word}
    {Color : Type v}

namespace Witness
variable (W : A.Witness Color)

/-- Forget duplicate designated images, without changing the output
vertex order, edge labels, edge profile, train or parameter sets. -/
noncomputable def dedup (ha : 2 ≤ a) : A.Witness Color := by
  let H := W.out.graph
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
      order := W.out.order
      part := W.out.part
      enumeration := W.out.enumeration
      carrier_eq := W.out.carrier_eq
      part_eq := W.out.part_eq
      part_mono := W.out.part_mono
      covered := W.out.covered
      parameters := W.out.parameters }
    finiteC := inferInstance
    family := W.family.dedup
    emb_part := fun c x => W.emb_part (H.imageRep c) x
    emb_order := fun c x y h => W.emb_order (H.imageRep c) x y h
    arrow := W.family.dedup_arrow (W.out.edge_nontrivial ha) W.arrow }

theorem dedup_systemBounds (ha : 2 ≤ a) (q : Fin (m+1) → ℕ)
    (h : W.out.graph.SystemBounds W.out.train q) :
    (W.dedup ha).out.graph.SystemBounds (W.dedup ha).out.train q :=
  W.out.graph.dedup_systemBounds W.out.train q h (W.out.edge_nontrivial ha)

theorem dedup_injective (ha : 2 ≤ a) :
    Function.Injective (W.dedup ha).out.graph.copyCarrier := Subtype.val_injective

end Witness
end ContactProfileTrain

/-- The actual ordered train Ramsey property with the manuscript's
one-designated-copy-per-image convention. The finite upper bound on
cutoffs is supplied by the finite proper vector, not an extra
restriction on the Ramsey theorem. -/
theorem contactProfileRamsey_distinctImages
    {P : Type v} [LinearOrder P] [Finite P]
    {m a : ℕ} (hm : 0 < m) (ha : 2 ≤ a)
    (allowed : Fin m → Set P) (word : Fin a → P)
    (q : Fin (m+1) → ℕ) (M : ℕ) (hOK : ContactRankOK M q)
    (A : ContactProfileTrain P m a allowed word)
    (hG : A.graph.WagonBounds A.train q)
    (Color : Type v) [Finite Color] [Nonempty Color] :
    ∃ W : A.Witness Color,
      W.out.graph.SystemBounds W.out.train q ∧
        Function.Injective W.out.graph.copyCarrier := by
  obtain ⟨W,hW⟩ := contactProfileRamsey_wellFounded M m q hm hOK
    P a ha allowed word A hG Color
  exact ⟨W.dedup ha,W.dedup_systemBounds ha q hW,W.dedup_injective ha⟩

/-- The height-one forest-Ramsey consequence on the actual ordered
hypergraph. It includes the Ramsey arrow, labelled edge girth,
and all mixed copy/edge forests through g, with distinct images.
The remaining relational application uses this result, not the old
recursive train construction. -/
theorem contactProfileForestRamsey
    {P : Type v} [LinearOrder P] [Finite P] {a : ℕ} (ha : 2 ≤ a)
    {allowed : Fin 1 → Set P} {word : Fin a → P}
    (A : ContactProfileTrain P 1 a allowed word)
    (g : ℕ) (hg : 2 ≤ g)
    (hG : LabelledGirthGT A.graph.edgeCarrier g)
    (Color : Type v) [Finite Color] [Nonempty Color] :
    ∃ W : A.Witness Color,
      LabelledGirthGT W.out.graph.edgeCarrier g ∧
      W.out.graph.bottomCut.ZeroSmallMixedForestsThrough g ∧
      Function.Injective W.out.graph.copyCarrier := by
  let q : Fin 2 → ℕ := fun _ => g
  have hOK : ContactRankOK g q := ⟨fun _ _ => ⟨hg,le_rfl⟩,fun _ _ _ _ => le_rfl⟩
  have hBounds : A.graph.WagonBounds A.train q := by
    intro μ hμ
    have he : μ = 0 := Fin.ext (by change μ.val = 0; omega)
    rw [he]
    exact A.graph.bottom_wagon_girth A.train hG
  obtain ⟨W,hW,hI⟩ := contactProfileRamsey_distinctImages
    (by omega : 0 < 1) ha allowed word q g hOK A hBounds Color
  have h0 : W.out.graph.bottomCut.ContactSystemGirthGT g :=
    (W.out.train.bottom_systemGirth_iff W.out.graph g).mp
      (hW 0 (by change (0 : ℕ) < 1; omega))
  letI : Finite W.out.Vertex := W.out.finiteV
  letI : Fintype W.out.Vertex := Fintype.ofFinite _
  have hforest := W.out.graph.bottomCut.zero_mixedForests_of_systemGirth (fun _ => rfl) h0
  refine ⟨W,?_,⟨fun _ => hforest.1,hforest.2⟩,hI⟩
  have he : W.out.graph.bottomCut.contactWagonCarrier = W.out.graph.edgeCarrier :=
    funext (W.out.graph.bottomCut.zero_wagonCarrier_eq (fun _ => rfl))
  rw [← he]
  exact h0.g3

end StructuralRamsey.Girth
