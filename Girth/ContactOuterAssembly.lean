import Girth.ContactOuterIteration
import Girth.ContactMixedCompletionCost
import Girth.ContactSeedAssembly
import Girth.ContactPartPreservation

/-! Connect the initial linear Ramsey seed to the actual outer iteration.
The qualitative bound m may exceed the girth g of the target. At picture
zero only the copy carriers need arbitrary-size join trees; the stronger
mixed-forest condition is used at cutoff two, never at cutoff m. -/

namespace StructuralRamsey.Girth
universe v
variable {V E I J : Type v}

/-- Pairwise disjoint bags admit a join tree. The proof uses the
already established finite chordal/conformal characterization. -/
theorem contact_joinTree_of_unique_owner [Fintype V] [Fintype J] [Nonempty J]
    (F : J → Set V)
    (hunique : ∀ i j x, x ∈ F i → x ∈ F j → i = j) :
    Nonempty (ContactJoinTree F) := by
  classical
  apply contact_joinTree_of_chordal_conformal
  · intro n z hn hinj hside
    let i : Fin n := ⟨0, by omega⟩
    let j := cyclicSucc (cyclicSucc i)
    have h0 : i.val = 0 := rfl
    have h1 : (cyclicSucc i).val = 1 := by
      rw [contactSucc_value, h0, if_pos (by omega : 0+1 < n)]
    have h2 : j.val = 2 := by
      change (cyclicSucc (cyclicSucc i)).val = 2
      rw [contactSucc_value, h1, if_pos (by omega : 1+1 < n)]
    have h3 : (cyclicSucc j).val = 3 := by
      rw [contactSucc_value, h2, if_pos (by omega : 2+1 < n)]
    have hij : i ≠ j := by
      intro h
      have h' := congrArg Fin.val h
      omega
    have hnext : cyclicSucc i ≠ j := by
      intro h
      have h' := congrArg Fin.val h
      omega
    have hprev : cyclicSucc j ≠ i := by
      intro h
      have h' := congrArg Fin.val h
      omega
    obtain ⟨_,a,hxa,hya⟩ := hside i
    obtain ⟨_,b,hyb,hzb⟩ := hside (cyclicSucc i)
    have hab := hunique a b (z (cyclicSucc i)) hya hyb
    subst b
    exact ⟨i,j,hij,hnext,hprev,fun h => hij (hinj h),a,hxa,hzb⟩
  · intro s hs hv hp
    obtain ⟨x,hx⟩ := hs
    obtain ⟨i,hi⟩ := hv x hx
    refine ⟨i,?_⟩
    intro y hy
    by_cases hxy : x = y
    · exact hxy ▸ hi
    · obtain ⟨j,hxj,hyj⟩ := hp x hx y hy hxy
      have hij := hunique i j x hi hxj
      exact hij.symm ▸ hyj

namespace ContactHypergraphData
variable (D : ContactHypergraphData V E I)

/-- The initial disjoint picture satisfies arbitrary qualitative
completion, independently of the girth of the target. -/
theorem disjointCopies_completable [Finite J] [Finite V] (m : ℕ) :
    ContactCompletable (D.disjointCopies J).copyCarrier m := by
  classical
  letI : Fintype (J × V) := Fintype.ofFinite _
  intro s hs _
  let K := {i : J // i ∈ s}
  letI : Nonempty K := by
    obtain ⟨i,hi⟩ := hs
    exact ⟨⟨i,hi⟩⟩
  refine ⟨s,Finset.Subset.rfl,?_⟩
  apply contact_joinTree_of_unique_owner
  intro i j x hi hj
  change x.1 = i.val at hi
  change x.1 = j.val at hj
  exact Subtype.ext (hi.symm.trans hj)

end ContactHypergraphData

namespace ContactSeed
variable {X B : Type v} [LinearOrder V] [LinearOrder X]
    {D : ContactHypergraphData V E I} {base : B → Set X}
    (A : ContactSeed D base J) (T : ContactTrainData E 1)

/-- The actual initialization of the outer invariant. Arbitrary
qualitative completion is not obtained from a false large-girth
assertion about the initial target. -/
theorem initialPicture_outerInvariant [Finite V] [Finite E] [Finite J]
    (allowed : Fin 1 → Set X) (q : Fin 2 → ℕ) (hq : 2 ≤ q 0)
    (horder : ∀ j, StrictMono (A.vertex j))
    (hcovered : ∀ x, ∃ e, x ∈ D.edgeCarrier e)
    (hlin : ∀ μ, μ.val < 1 → (D.atCut (T.parent μ)).ContactLinear)
    (hg : D.WagonBounds T q)
    (hpar : ∀ i : J, D.Parameters T (fun j => A.vertex i ⁻¹' allowed j))
    (m : ℕ) :
    (A.initialPicture (by omega : 0 < 1) allowed q horder hcovered hlin hg hpar).OuterInvariant m := by
  let Q := A.initialPicture (by omega : 0 < 1) allowed q horder hcovered hlin hg hpar
  have hfull : Q.FullBounds := A.initialPicture_fullBounds
    (by omega : 0 < 1) allowed q horder hcovered hlin hg hpar
  refine ⟨?_,(Q.forests_of_fullBounds (by omega) hfull hq).1 (by omega),?_⟩
  · change (∀ x : J × V, ∃ j : J, x.1 = j) ∧
      (∀ e : J × E, ∃ j : J, e.1 = j)
    exact ⟨fun x => ⟨x.1,rfl⟩,fun e => ⟨e.1,rfl⟩⟩
  · exact D.disjointCopies_completable (J := J) m

end ContactSeed

/-- Ordered outer witnesses preserve the original one-point labels
and order, but do NOT require the labels to increase with the order.
This distinction is essential for relational support hypergraphs. -/
structure ContactOrderedOuterWitness (D : ContactHypergraphData V E I)
    [LinearOrder V] {P : Type v} (part : V → P) (Color : Type v) where
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
  emb_order : ∀ i x y, x < y → order.lt ((family.emb i).vertex x) ((family.emb i).vertex y)
  emb_label : ∀ i x, label ((family.emb i).vertex x) = part x
  arrow : family.Arrow Color

namespace ContactOrderedEdgeWord
variable {D : ContactHypergraphData V E I} [LinearOrder V]
    {P : Type v} {a : ℕ} (A : ContactOrderedEdgeWord D P a)

theorem outer_edge_nontrivial (ha : 2 ≤ a) (e : E) : (D.edgeCarrier e).Nontrivial := by
  rw [A.carrier_eq]
  refine ⟨A.enumeration e ⟨0,by omega⟩,⟨_,rfl⟩,
    A.enumeration e ⟨1,by omega⟩,⟨_,rfl⟩,?_⟩
  intro h
  have he := congrArg Fin.val ((A.enumeration e).injective h)
  change (0 : ℕ) = 1 at he
  omega

theorem outer_carrier_injective (ha : 2 ≤ a)
    (hlin : ∀ e f : E, e ≠ f → (D.edgeCarrier e ∩ D.edgeCarrier f).Subsingleton) :
    Function.Injective D.edgeCarrier := by
  intro e f he
  by_contra hn
  obtain ⟨x,hx,y,hy,hxy⟩ := A.outer_edge_nontrivial ha e
  exact hxy (hlin e f hn ⟨hx,he ▸ hx⟩ ⟨hy,he ▸ hy⟩)

end ContactOrderedEdgeWord

/-- The actual outer construction for an arbitrary ordered edge word.
Unlike a recursive profile, the target need not be ordered by its
labels; the output uses the projection order without resorting it by
one-point types. -/
theorem contactOrderedOuterRamsey_qualitative
    {D : ContactHypergraphData V E I} [Finite V] [Finite E] [Nonempty E]
    [LinearOrder V] {P : Type v} [LinearOrder P] [Finite P]
    {a : ℕ} (ha : 2 ≤ a) (A : ContactOrderedEdgeWord D P a)
    (hcovered : ∀ x, ∃ e, x ∈ D.edgeCarrier e)
    (g m : ℕ) (hg : 2 ≤ g) (hm : 2 ≤ m)
    (hG : LabelledGirthGT D.edgeCarrier g)
    (Color : Type v) [Finite Color] [Nonempty Color] :
    ∃ W : ContactOrderedOuterWitness D A.part Color, W.graph.CopyCovered ∧
      W.graph.bottomCut.ZeroPairwise ∧ ContactCompletable W.graph.copyCarrier m ∧
      (∀ e f : W.Edge, e ≠ f → (W.graph.edgeCarrier e ∩ W.graph.edgeCarrier f).Subsingleton) := by
  classical
  letI : Fintype V := Fintype.ofFinite _
  letI : Fintype Color := Fintype.ofFinite _
  let T := contactHeightOne E
  let allowed : Fin 1 → Set P := fun _ => Set.univ
  let q : Fin 2 → ℕ := fun _ => g
  have hBounds : D.WagonBounds T q := by
    intro μ hμ
    have he : μ = 0 := Fin.ext (by change μ.val = 0; omega)
    rw [he]
    exact D.bottom_wagon_girth T hG
  have hl := contact_pairwise_of_labelledGirth D.edgeCarrier hg hG
  have hlin (μ : Fin 2) (hμ : μ.val < 1) :
      (D.atCut (T.parent μ)).ContactLinear :=
    ⟨hl,contact_pairwise_of_labelledGirth _ hg (hBounds μ hμ)⟩
  have hp : D.Parameters T (fun j => A.part ⁻¹' allowed j) := by
    intro j e f x he hx hy hn
    exact (hn (Set.mem_univ _)).elim
  obtain ⟨S⟩ := A.exists_ordered_linear_seed (Color := Color)
    (A.outer_carrier_injective ha hl) hl
  letI : Finite S.Vertex := S.finiteV
  letI : Finite S.Edge := S.finiteE
  letI : Finite S.Copy := S.finiteC
  letI : Fintype S.Edge := Fintype.ofFinite _
  letI : LinearOrder S.Vertex := S.order
  let Q := S.trainPicture T allowed q (by omega) hcovered hlin hBounds hp
  have hInv : Q.OuterInvariant m :=
    S.toSeed.initialPicture_outerInvariant T (fun j => S.part ⁻¹' allowed j) q hg
      (fun i _ _ h => S.emb_order i _ _ h) hcovered hlin hBounds
      (S.seed_parameters T allowed hp) m
  have hpart : Q.PartPreserving A.part S.part :=
    S.trainPicture_partPreserving (T := T) allowed q (by omega)
      hcovered hlin hBounds hp
  have hArrow : ∀ ρ : S.Edge → Color, ∃ i : Q.Copy, ∃ c : Color,
      ∀ e : E, ρ (Q.projection.edge ((Q.family.emb i).edge e)) = c :=
    S.trainPicture_arrow T allowed q (by omega) hcovered hlin hBounds hp
  have hsize (b : S.Edge) : (S.graph.edgeCarrier b).Nontrivial := by
    rw [S.carrier_eq]
    refine ⟨S.enumeration b ⟨0,by omega⟩,⟨_,rfl⟩,
      S.enumeration b ⟨1,by omega⟩,⟨_,rfl⟩,?_⟩
    intro h
    have he := congrArg Fin.val ((S.enumeration b).injective h)
    change (0 : ℕ) = 1 at he
    omega
  obtain ⟨R,hR,hpartR,hA⟩ := Q.outer_of_seed m hm S.linear hsize hInv hpart hArrow
  let W : ContactOrderedOuterWitness D A.part Color := {
    Vertex := R.Vertex
    Edge := R.Edge
    Copy := R.Copy
    finiteV := R.finiteV
    finiteE := R.finiteE
    finiteC := R.finiteC
    graph := R.graph
    train := R.train
    family := R.family
    order := R.order
    label := S.part ∘ R.projection.vertex
    emb_order := R.copy_order
    emb_label := hpartR
    arrow := hA }
  exact ⟨W,hR.1,hR.2.1,hR.2.2,R.linear⟩

namespace ContactDesignatedEmbeddings
variable {U F K : Type v} {m : ℕ}
    {D : ContactHypergraphData V E I} {T : ContactTrainData E m}
    {H : ContactHypergraphData U F K} {S : ContactTrainData F m}
    (M : ContactDesignatedEmbeddings D T H S)

/-- Local girth is transported along the actual designated embeddings;
this is independent of any ambient girth conclusion. -/
theorem copy_girth_of_source {g : ℕ} (hg : LabelledGirthGT D.edgeCarrier g)
    (j : K) : LabelledGirthGT (fun e : H.copyEdges j => H.edgeCarrier e.val) g := by
  classical
  rintro ⟨C,hC⟩
  let f := M.emb j
  have hex (i : Fin C.length) : ∃ e : E, f.edge e = (C.label i).val := by
    have h := (C.label i).property
    rw [M.edge_eq j] at h
    exact h
  choose e he using hex
  have hvx (i : Fin C.length) : ∃ x : V, f.vertex x = C.vertex i :=
    f.vertex_range_of_edge (e i) (by rw [he i]; exact C.left_mem i)
  choose x hx using hvx
  let C' : LabelledBergeCycle D.edgeCarrier := {
    length := C.length
    hlength := C.hlength
    label := e
    vertex := x
    label_injective := by
      intro i j hij
      exact C.label_injective (Subtype.ext ((he i).symm.trans ((congrArg f.edge hij).trans (he j))))
    vertex_injective := by
      intro i j hij
      exact C.vertex_injective ((hx i).symm.trans ((congrArg f.vertex hij).trans (hx j)))
    left_mem := by
      intro i
      apply (f.mem_edge_image (e i) (x i)).mp
      rw [he i,hx i]
      exact C.left_mem i
    right_mem := by
      intro i
      apply (f.mem_edge_image (e (cyclicSucc i)) (x i)).mp
      rw [he (cyclicSucc i),hx i]
      exact C.right_mem i }
  exact hg ⟨C',hC⟩

theorem copy_edge_subset_from_embeddings (j : K) (e : F)
    (he : e ∈ H.copyEdges j) : H.edgeCarrier e ⊆ H.copyCarrier j := by
  rw [M.edge_eq j] at he
  obtain ⟨e₀,rfl⟩ := he
  rw [M.vertex_eq j]
  exact (M.emb j).vertex_range_of_edge e₀

end ContactDesignatedEmbeddings

namespace ContactHypergraphData
variable (H : ContactHypergraphData V E I)

open Classical in
/-- The quantitative completion conclusion, using actual mixed labels.
The constraint on the number of added pieces applies only to families
of size at least two. The singleton case already has a one-node tree. -/
def QuantitativeCompletion (g m : ℕ) : Prop :=
  ∀ s : Finset (I ⊕ E), 2 ≤ s.card → s.card ≤ m →
    ∃ t : Finset (I ⊕ E), s ⊆ t ∧
      (∀ a ∈ t, a ∉ s → ∃ i, a = Sum.inl i) ∧
      Nonempty (ContactJoinTree (fun a : {a // a ∈ t} => H.bottomCut.carrier a.val)) ∧
      (g-1)*(t \ s).card ≤ s.card-2

/-- For a short Berge cycle, the quantitative budget leaves no
auxiliary copy. A join tree on its own edges would contradict the
marked-edge lemma, with one marked edge per node. -/
theorem girth_of_quantitativeCompletion (g m : ℕ) (hg : 2 ≤ g) (hm : g ≤ m)
    (hlin : ∀ e f, e ≠ f → (H.edgeCarrier e ∩ H.edgeCarrier f).Subsingleton)
    (hcomp : H.QuantitativeCompletion g m) : LabelledGirthGT H.edgeCarrier g := by
  classical
  rintro ⟨C,hC⟩
  let f (i : Fin C.length) : I ⊕ E := Sum.inr (C.label i)
  have hfi : Function.Injective f := fun i j h => C.label_injective (Sum.inr.inj h)
  let s : Finset (I ⊕ E) := Finset.univ.image f
  have hs : s.card = C.length := by
    rw [Finset.card_image_of_injective _ hfi,Finset.card_univ,Fintype.card_fin]
  obtain ⟨t,hst,_,⟨J⟩,hcost⟩ := hcomp s
    (by rw [hs]; exact C.hlength) (by rw [hs]; exact hC.trans hm)
  rw [hs] at hcost
  have hz : (t \ s).card = 0 := by
    by_contra hne
    have hpos : 1 ≤ (t \ s).card := by omega
    have hmul := Nat.mul_le_mul_left (g-1) hpos
    rw [Nat.mul_one] at hmul
    omega
  have hts : t ⊆ s := by
    intro a ha
    by_contra hn
    have hx := Finset.mem_sdiff.mpr ⟨ha,hn⟩
    rw [Finset.card_eq_zero.mp hz] at hx
    simp at hx
  have hEq : t = s := Finset.Subset.antisymm hts hst
  subst t
  let p (i : Fin C.length) : {a : I ⊕ E // a ∈ s} :=
    ⟨f i,Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩⟩
  have hpi : Function.Injective p := fun i j h => hfi (congrArg Subtype.val h)
  have hps : Function.Surjective p := by
    intro a
    obtain ⟨i,_,hi⟩ := Finset.mem_image.mp a.property
    exact ⟨i,Subtype.ext hi⟩
  let r := Equiv.ofBijective p ⟨hpi,hps⟩
  let J' : ContactJoinTree (fun i : Fin C.length => H.edgeCarrier (C.label i)) :=
    J.reindex r
  let C' : LabelledBergeCycle (fun e : {e : E // True} => H.edgeCarrier e.val) := {
    length := C.length
    hlength := C.hlength
    label := fun i => ⟨C.label i,True.intro⟩
    vertex := C.vertex
    label_injective := fun i j h => C.label_injective (congrArg Subtype.val h)
    vertex_injective := C.vertex_injective
    left_mem := C.left_mem
    right_mem := C.right_mem }
  refine contact_marked_cycle_impossible (fun i : Fin C.length => H.edgeCarrier (C.label i))
    H.edgeCarrier (fun i => {C.label i}) (fun _ => True) J' ?_ ?_ hlin ?_ C' ?_
  · intro i e he
    have he' : e = C.label i := Set.mem_singleton_iff.mp he
    subst e
    exact Set.Subset.rfl
  · intro i e f he hf _ _
    exact (Set.mem_singleton_iff.mp he).trans (Set.mem_singleton_iff.mp hf).symm
  · intro i j hne
    exact Or.inl (hlin _ _ (fun h => hne (C.label_injective h)))
  · intro i
    exact ⟨i,rfl⟩

end ContactHypergraphData

/-- Ordered edge-word outer girth Ramsey theorem for covered input.
The quantitative conclusion is on the same actual designated family
as the arrow. The larger completion cutoff need not bound target girth. -/
theorem contactOrderedOuterRamsey_quantitative
    {D : ContactHypergraphData V E I} [Finite V] [Finite E] [Nonempty E]
    [LinearOrder V] {P : Type v} [LinearOrder P] [Finite P]
    {a : ℕ} (ha : 2 ≤ a) (A : ContactOrderedEdgeWord D P a)
    (hcovered : ∀ x, ∃ e, x ∈ D.edgeCarrier e)
    (g m : ℕ) (hg : 2 ≤ g) (hm : g ≤ m)
    (hG : LabelledGirthGT D.edgeCarrier g)
    (Color : Type v) [Finite Color] [Nonempty Color] :
    ∃ W : ContactOrderedOuterWitness D A.part Color, W.graph.CopyCovered ∧
      W.graph.bottomCut.ZeroPairwise ∧ LabelledGirthGT W.graph.edgeCarrier g ∧
      W.graph.QuantitativeCompletion g m := by
  classical
  obtain ⟨W,hcov,hpair,hcomp,hlin⟩ :=
    contactOrderedOuterRamsey_qualitative ha A hcovered g m hg (hg.trans hm) hG Color
  letI : Finite W.Vertex := W.finiteV
  letI : Fintype W.Vertex := Fintype.ofFinite _
  have hQ : W.graph.QuantitativeCompletion g m := by
    intro s hs hsm
    exact W.graph.bottomCut.mixedCompletion_cost g m hg hlin hpair hcov.2
      W.family.copy_edge_subset_from_embeddings (W.family.copy_girth_of_source hG)
      hcomp s hs hsm
  exact ⟨W,hcov,hpair,W.graph.girth_of_quantitativeCompletion g m hg hm hlin hQ,hQ⟩

end StructuralRamsey.Girth
