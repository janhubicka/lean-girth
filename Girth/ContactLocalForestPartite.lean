import Girth.ContactIsolatedPadding
import Girth.ContactCoveredProfile

/-! Complete the application to arbitrary finite ordered uniform
profiles, including targets with isolated vertices. The input
train theorem applies only to the covered restriction, and the
omitted vertices are then restored in genuinely private copies.
-/

namespace StructuralRamsey.Girth
universe v
variable {V E I U F J P : Type v}

namespace ContactDesignatedEmbeddings
variable {D : ContactHypergraphData V E I}
    {H : ContactHypergraphData U F J}
    {T : ContactTrainData E 1} {S : ContactTrainData F 1}
    (M : ContactDesignatedEmbeddings D.trimIsolated T H S)

def paddedPart (part : V → P) (label : U → P) (x : M.PaddedVertex) : P :=
  match x.val with
  | .inl u => label u
  | .inr z => part z.2

theorem paddedPart_core (part : V → P) (label : U → P) (x : U) :
    M.paddedPart part label (M.paddedCore x) = label x := rfl

theorem paddedPart_copy (part : V → P) (label : U → P)
    (hpart : ∀ j (x : D.EdgeVertex), label ((M.emb j).vertex x) = part x.val)
    (j : J) (x : V) :
    M.paddedPart part label (M.paddedCopy j x) = part x := by
  cases he : M.isolatedGlue j x with
  | none =>
    change (match gluedStandardNode M.isolatedGlue j x with
      | .inl u => label u
      | .inr z => part z.2) = part x
    simp only [gluedStandardNode,he]
  | some u =>
    obtain ⟨hx,hxu⟩ := (M.isolatedGlue_iff j x u).mp he
    rw [(contactStandardEmb_eq_core M.isolatedGlue M.isolatedGlue_inj j x u).mpr he,
      M.paddedPart_core,← hxu]
    exact hpart j ⟨x,hx⟩

/-- Restore the original orders on every copy and keep a single
order concatenated by the original parts on the output. -/
theorem exists_paddedPartOrder [Fintype V] [Fintype U] [Finite J]
    [LinearOrder V] [LinearOrder U] [LinearOrder P]
    (part : V → P) (label : U → P)
    (hmono : Monotone part)
    (hpart : ∀ j (x : D.EdgeVertex), label ((M.emb j).vertex x) = part x.val)
    (hord : ∀ j (x y : D.EdgeVertex), x.val < y.val →
      (M.emb j).vertex x < (M.emb j).vertex y) :
    ∃ o : LinearOrder M.PaddedVertex,
      (∀ x y, o.le x y → M.paddedPart part label x ≤ M.paddedPart part label y) ∧
      (∀ j x y, x < y → o.lt (M.paddedCopy j x) (M.paddedCopy j y)) := by
  classical
  have hc : ContactGluedOrder.Compatible M.isolatedGlue := by
    intro j x y u w hx hy hxy
    obtain ⟨hx,hxu⟩ := (M.isolatedGlue_iff j x u).mp hx
    obtain ⟨hy,hyw⟩ := (M.isolatedGlue_iff j y w).mp hy
    exact hxu ▸ hyw ▸ hord j ⟨x,hx⟩ ⟨y,hy⟩ hxy
  obtain ⟨o,_,hstd⟩ := ContactGluedOrder.exists_order M.isolatedGlue hc M.isolatedGlue_inj
  let o' := ContactOrderedSeedStage.concatenate o (M.paddedPart part label)
  refine ⟨o',?_,?_⟩
  · intro x y h
    by_contra hn
    have ht := ContactOrderedSeedStage.concatenate_part o
      (M.paddedPart part label) y x (lt_of_not_ge hn)
    letI : LinearOrder M.PaddedVertex := o'
    exact (not_lt_of_ge h) ht
  · intro j x y h
    rcases lt_or_eq_of_le (hmono h.le) with hl | he
    · apply ContactOrderedSeedStage.concatenate_part
      rw [M.paddedPart_copy part label hpart,M.paddedPart_copy part label hpart]
      exact hl
    · apply ContactOrderedSeedStage.concatenate_within
      · rw [M.paddedPart_copy part label hpart,M.paddedPart_copy part label hpart]
        exact he
      · exact hstd j x y h

end ContactDesignatedEmbeddings

/-- The finite local-forest witness, without requiring the target
or the output to be covered by hyperedges. Every output vertex
and edge is, however, covered by a designated copy. -/
structure ContactLocalForestWitness (D : ContactHypergraphData V E I)
    [LinearOrder V] (P : Type v) [LinearOrder P] (part : V → P)
    (q : ℕ) (Color : Type v) where
  Vertex : Type v
  Edge : Type v
  Copy : Type v
  finiteV : Finite Vertex
  finiteE : Finite Edge
  finiteC : Finite Copy
  graph : ContactHypergraphData Vertex Edge Copy
  train : ContactTrainData Edge 1
  family : ContactDesignatedEmbeddings D (contactHeightOne E) graph train
  order : LinearOrder Vertex
  label : Vertex → P
  emb_part : ∀ i x, label ((family.emb i).vertex x) = part x
  emb_order : ∀ i x y, x < y → order.lt ((family.emb i).vertex x) ((family.emb i).vertex y)
  part_mono : ∀ x y, order.le x y → label x ≤ label y
  vertexCoverage : ∀ x, ∃ i, x ∈ graph.copyCarrier i
  edgeCoverage : ∀ e, ∃ i, e ∈ graph.copyEdges i
  distinctImages : Function.Injective graph.copyCarrier
  girth : LabelledGirthGT graph.edgeCarrier q
  forests : graph.bottomCut.ZeroSmallMixedForestsThrough q
  arrow : family.Arrow Color

/-- Full local-forest partite lemma, expressed for any common
ordered uniform profile. The usual transversal case is obtained
by taking the profile to list each of the a parts once.
The proof is also valid when there is just one edge. -/
theorem contactLocalForestPartite
    (D : ContactHypergraphData V E I) [Finite V] [Finite E] [Nonempty E]
    [LinearOrder V] {P : Type v} [LinearOrder P] [Finite P]
    (part : V → P) (hmono : Monotone part) {a : ℕ} (ha : 2 ≤ a)
    (word : Fin a → P) (enumeration : E → Fin a ↪o V)
    (he : ∀ e, D.edgeCarrier e = Set.range (enumeration e))
    (hw : ∀ e i, part (enumeration e i) = word i)
    (g : ℕ) (hg : 2 ≤ g) (hG : LabelledGirthGT D.edgeCarrier g)
    (Color : Type v) [Finite Color] [Nonempty Color] :
    Nonempty (ContactLocalForestWitness D P part g Color) := by
  classical
  letI : Fintype V := Fintype.ofFinite _
  letI : Finite D.EdgeVertex :=
    Finite.of_injective (fun x : D.EdgeVertex => x.val) Subtype.val_injective
  let f (e : E) (i : Fin a) : D.EdgeVertex :=
    ⟨enumeration e i,⟨e,by rw [he]; exact ⟨i,rfl⟩⟩⟩
  let A : ContactProfileTrain P 1 a (fun _ => Set.univ) word := {
    Vertex := D.EdgeVertex
    Edge := E
    Copy := PEmpty.{v+1}
    finiteV := inferInstance
    finiteE := inferInstance
    nonemptyE := inferInstance
    graph := D.trimIsolated
    train := contactHeightOne E
    order := inferInstance
    part := fun x => part x.val
    enumeration := fun e => OrderEmbedding.ofStrictMono (f e)
      (fun i j h => (enumeration e).strictMono h)
    carrier_eq := by
      intro e
      ext x
      change x.val ∈ D.edgeCarrier e ↔ x ∈ Set.range (f e)
      rw [he]
      constructor
      · rintro ⟨i,hi⟩
        exact ⟨i,Subtype.ext hi⟩
      · rintro ⟨i,rfl⟩
        exact ⟨i,rfl⟩
    part_eq := hw
    part_mono := fun x y h => hmono h
    covered := D.trimIsolated_covered
    parameters := by
      intro j e f x h hx hy hn
      exact (hn (Set.mem_univ _)).elim }
  obtain ⟨W,hW,hF,hI,hV,hE⟩ := contactProfileForestRamsey_covered ha A g hg
    (D.trimIsolated_girth hG) Color
  let M := W.family
  letI : Finite W.out.Vertex := W.out.finiteV
  letI : Fintype W.out.Vertex := Fintype.ofFinite _
  letI : Finite W.out.Copy := W.finiteC
  letI : LinearOrder W.out.Vertex := W.out.order
  obtain ⟨o,hom,ho⟩ := M.exists_paddedPartOrder part W.out.part hmono W.emb_part W.emb_order
  exact ⟨{
    Vertex := M.PaddedVertex
    Edge := W.out.Edge
    Copy := W.out.Copy
    finiteV := M.padded_finite
    finiteE := W.out.finiteE
    finiteC := W.finiteC
    graph := M.paddedGraph
    train := W.out.train
    family := M.paddedFamily
    order := o
    label := M.paddedPart part W.out.part
    emb_part := M.paddedPart_copy part W.out.part W.emb_part
    emb_order := ho
    part_mono := hom
    vertexCoverage := M.padded_vertexCoverage hV
    edgeCoverage := hE
    distinctImages := M.padded_copy_injective hI
    girth := M.padded_girth hW
    forests := M.padded_smallForests hF
    arrow := M.padded_arrow W.arrow }⟩

end StructuralRamsey.Girth
