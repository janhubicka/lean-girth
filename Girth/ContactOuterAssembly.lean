import Girth.ContactOuterIteration
import Girth.ContactMixedCompletionCost
import Girth.ContactSeedAssembly
import Girth.ContactProfileRamseyInduction

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

/-- The outer Ramsey witness on a covered ordered uniform profile.
The initial seed is constructed, not supplied. The output has the
actual designated Ramsey family, pairwise allowed intersections,
and qualitative completion at the independently specified cutoff m. -/
theorem contactProfileOuterRamsey_qualitative
    {P : Type v} [LinearOrder P] [Finite P] {a : ℕ} (ha : 2 ≤ a)
    {allowed : Fin 1 → Set P} {word : Fin a → P}
    (A : ContactProfileTrain P 1 a allowed word)
    (g m : ℕ) (hg : 2 ≤ g) (hm : 2 ≤ m)
    (hG : LabelledGirthGT A.graph.edgeCarrier g)
    (Color : Type v) [Finite Color] [Nonempty Color] :
    ∃ W : A.Witness Color, W.out.graph.CopyCovered ∧
      W.out.graph.bottomCut.ZeroPairwise ∧
      ContactCompletable W.out.graph.copyCarrier m ∧
      (∀ e f : W.out.Edge, e ≠ f →
        (W.out.graph.edgeCarrier e ∩ W.out.graph.edgeCarrier f).Subsingleton) := by
  classical
  letI : Finite A.Vertex := A.finiteV
  letI : Fintype A.Vertex := Fintype.ofFinite _
  letI : Finite A.Edge := A.finiteE
  letI : Nonempty A.Edge := A.nonemptyE
  letI : LinearOrder A.Vertex := A.order
  letI : Fintype Color := Fintype.ofFinite _
  let q : Fin 2 → ℕ := fun _ => g
  have hBounds : A.graph.WagonBounds A.train q := by
    intro μ hμ
    have he : μ = 0 := Fin.ext (by change μ.val = 0; omega)
    rw [he]
    exact A.graph.bottom_wagon_girth A.train hG
  have hl := A.linear_of_wagonBounds (by omega : 0 < 1) q hg hBounds
  have hlin (μ : Fin 2) (hμ : μ.val < 1) :
      (A.graph.atCut (A.train.parent μ)).ContactLinear :=
    ⟨hl,contact_pairwise_of_labelledGirth _ hg (hBounds μ hμ)⟩
  let U := A.edgeWord
  obtain ⟨S⟩ := U.exists_ordered_linear_seed (Color := Color)
    (A.carrier_injective_of_linear ha hl) hl
  letI : Finite S.Vertex := S.finiteV
  letI : Finite S.Edge := S.finiteE
  letI : Finite S.Copy := S.finiteC
  letI : Fintype S.Edge := Fintype.ofFinite _
  letI : LinearOrder S.Vertex := S.order
  let Q := S.trainPicture A.train allowed q (by omega) A.covered hlin hBounds A.parameters
  have hInv : Q.OuterInvariant m :=
    S.toSeed.initialPicture_outerInvariant A.train (fun j => S.part ⁻¹' allowed j) q hg
      (fun i _ _ h => S.emb_order i _ _ h) A.covered hlin hBounds
      (S.seed_parameters A.train allowed A.parameters) m
  have hpart : Q.PartPreserving A.part S.part :=
    S.trainPicture_partPreserving (T := A.train) allowed q (by omega)
      A.covered hlin hBounds A.parameters
  have hArrow : ∀ ρ : S.Edge → Color, ∃ i : Q.Copy, ∃ c : Color,
      ∀ e : A.Edge, ρ (Q.projection.edge ((Q.family.emb i).edge e)) = c :=
    S.trainPicture_arrow A.train allowed q (by omega) A.covered hlin hBounds A.parameters
  have hsize (b : S.Edge) : (S.graph.edgeCarrier b).Nontrivial := by
    rw [S.carrier_eq]
    refine ⟨S.enumeration b ⟨0,by omega⟩,⟨_,rfl⟩,
      S.enumeration b ⟨1,by omega⟩,⟨_,rfl⟩,?_⟩
    intro h
    have he := (S.enumeration b).injective h
    have hv := congrArg Fin.val he
    change (0 : ℕ) = 1 at hv
    omega
  obtain ⟨R,hR,hpartR,hA⟩ := Q.outer_of_seed m hm S.linear hsize hInv hpart hArrow
  let W := A.witnessFromPicture S.part S.enumeration S.carrier_eq S.part_eq R
    (fun _ _ => Iff.rfl) hpartR hA
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
  apply contact_marked_cycle_impossible (fun i : Fin C.length => H.edgeCarrier (C.label i))
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

/-- Ordered uniform-profile outer girth Ramsey theorem, for covered
input. The completion cutoff is independent of g, provided it is at
least g. Both large girth and the sharp quantitative bound are
conclusions about the same actual designated family and its edge labels. -/
theorem contactProfileOuterRamsey_quantitative
    {P : Type v} [LinearOrder P] [Finite P] {a : ℕ} (ha : 2 ≤ a)
    {allowed : Fin 1 → Set P} {word : Fin a → P}
    (A : ContactProfileTrain P 1 a allowed word)
    (g m : ℕ) (hg : 2 ≤ g) (hm : g ≤ m)
    (hG : LabelledGirthGT A.graph.edgeCarrier g)
    (Color : Type v) [Finite Color] [Nonempty Color] :
    ∃ W : A.Witness Color, W.out.graph.CopyCovered ∧
      W.out.graph.bottomCut.ZeroPairwise ∧ LabelledGirthGT W.out.graph.edgeCarrier g ∧
      W.out.graph.QuantitativeCompletion g m := by
  obtain ⟨W,hcov,hpair,hcomp,hlin⟩ :=
    contactProfileOuterRamsey_qualitative ha A g m hg (hg.trans hm) hG Color
  letI : Finite W.out.Vertex := W.out.finiteV
  letI : Fintype W.out.Vertex := Fintype.ofFinite _
  have hQ : W.out.graph.QuantitativeCompletion g m := by
    intro s hs hsm
    exact W.out.graph.bottomCut.mixedCompletion_cost g m hg hlin hpair hcov.2
      W.family.copy_edge_subset_from_embeddings (W.family.copy_girth_of_source hG)
      hcomp s hs hsm
  exact ⟨W,hcov,hpair,W.out.graph.girth_of_quantitativeCompletion g m hg hm hlin hQ,hQ⟩

end StructuralRamsey.Girth
