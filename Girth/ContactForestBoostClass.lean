import Girth.ContactBoostClass
import Girth.ContactLocalCoreInput

/-! The class-wide induction in the forest-boost lemma, with actual
strip witnesses and the original part-order extraction. -/

namespace StructuralRamsey.Girth
universe v
variable {V E I P : Type v}

namespace ContactTrainPicture
variable [LinearOrder P] {m : ℕ} {allowed : Fin m → Set P} {q : Fin (m+1) → ℕ}
variable (A : ContactBoostInput P m allowed q)
variable {X B J : Type v} [LinearOrder X]
variable {H : ContactHypergraphData X B J}
variable (S : ContactPartiteEndpoints H P)
variable [LinearOrder A.Vertex]
variable (Q : ContactTrainPicture A.graph A.train H.edgeCarrier
  (fun j => S.part ⁻¹' allowed j) q)

/-- Every edge of the output has exactly one vertex over each
original part. The actual projection supplies both existence and
uniqueness, including edges not in a designated target copy. -/
noncomputable def outputEndpoints : ContactPartiteEndpoints Q.graph P := by
  classical
  have hex (e : Q.Edge) (p : P) : ∃ x, x ∈ Q.graph.edgeCarrier e ∧
      Q.projection.vertex x = S.endpoint (Q.projection.edge e) p := by
    have hmem := S.endpoint_mem (Q.projection.edge e) p
    rw [← Q.projection.edge_image e] at hmem
    exact hmem
  let f (e : Q.Edge) (p : P) := Classical.choose (hex e p)
  have hf (e : Q.Edge) (p : P) : f e p ∈ Q.graph.edgeCarrier e ∧
      Q.projection.vertex (f e p) = S.endpoint (Q.projection.edge e) p :=
    Classical.choose_spec (hex e p)
  refine {
    part := S.part ∘ Q.projection.vertex
    endpoint := f
    part_endpoint := ?_
    carrier_eq := ?_
    covered := Q.covered }
  · intro e p
    change S.part (Q.projection.vertex (f e p)) = p
    rw [(hf e p).2,S.part_endpoint]
  · intro e
    ext x
    constructor
    · intro hx
      have hmem : Q.projection.vertex x ∈ H.edgeCarrier (Q.projection.edge e) := by
        rw [← Q.projection.edge_image e]
        exact ⟨x,hx,rfl⟩
      let p := S.part (Q.projection.vertex x)
      exact ⟨p,Q.projection.edge_inj e (hf e p).1 hx
        ((hf e p).2.trans (S.endpoint_of_mem _ _ hmem))⟩
    · rintro ⟨p,rfl⟩
      exact (hf e p).1

/-- Pack an actual nonempty active strip back into the fixed
class. The positive wagon bounds and parameters are inherited. -/
noncomputable def boostStripInput (b : B) (hne : Nonempty (Q.projection.StripEdge b))
    (hmono : Monotone S.part) :
    ContactBoostInput P m allowed q := by
  letI : Finite Q.Vertex := Q.finiteV
  letI : Finite Q.Edge := Q.finiteE
  letI : LinearOrder Q.Vertex := Q.order
  let r := S.edgeLabelEquiv b
  have hr : Monotone r := fun _ _ h => hmono h
  have hparam (j : Fin m) (x : H.edgeCarrier b) :
      x.val ∈ S.part ⁻¹' allowed j ↔ r x ∈ allowed j := Iff.rfl
  exact {
    Vertex := Q.projection.StripVertex b
    Edge := Q.projection.StripEdge b
    Copy := PEmpty.{v+1}
    finiteV := inferInstance
    finiteE := inferInstance
    nonemptyE := hne
    graph := Q.projection.stripHypergraph b
    train := Q.projection.stripTrain Q.train b
    endpoints := Q.projection.relabelStripEndpoints b r
    order := inferInstance
    part_mono := fun x y h => Q.strip_original_order b r hr h
    linear := Q.projection.strip_linear b Q.linear
    parameters := Q.strip_original_parameters b r allowed hparam
    positiveWagons := fun μ hp ht => Q.strip_positive_wagonBounds b μ hp ht }

/-- Turn the lower-bound witness on that exact strip into its
actual gluing core. No preservation of the next picture is assumed. -/
noncomputable def boostCore (b : B) (hne : Nonempty (Q.projection.StripEdge b))
    (hmono : Monotone S.part) {Color : Type v}
    (W : (Q.boostStripInput A S b hne hmono).Witness Color) : Q.Core b := by
  let r := S.edgeLabelEquiv b
  let L : Q.LocalWitness b r := {
    Vertex := W.out.Vertex
    Edge := W.out.Edge
    Copy := W.out.Copy
    finiteV := W.out.finiteV
    finiteE := W.out.finiteE
    finiteC := W.finiteC
    graph := W.out.graph
    train := W.out.train
    family := W.family
    endpoints := W.out.endpoints
    emb_part := W.emb_part
    order := W.out.order
    emb_order := W.emb_order
    linear := W.out.linear
    positive := W.positive }
  exact L.toCore allowed (fun _ _ => Iff.rfl) W.out.parameters

/-- Output extraction as a member of the same fixed class. The
order is concatenated by the original part labels, not the seed
vertices. The arrow witnesses nonemptiness of the output edge type. -/
noncomputable def boostWitness {Color : Type v} [Nonempty Color]
    (horder : ∀ x y, x < y ↔ A.order.lt x y)
    (hpart : Q.PartPreserving A.endpoints.part S.part)
    (hArrow : Q.family.Arrow Color) : A.Witness Color := by
  let o := Q.originalPartOrder S.part
  let ep := Q.outputEndpoints A S
  have hE : Nonempty Q.Edge := by
    obtain ⟨i,_,_⟩ := hArrow (fun _ => Classical.choice (inferInstance : Nonempty Color))
    exact ⟨(Q.family.emb i).edge (Classical.choice A.nonemptyE)⟩
  have hm : Monotone A.endpoints.part := by
    intro x y h
    rcases lt_or_eq_of_le h with hlt | rfl
    · letI : LinearOrder A.Vertex := A.order
      exact A.part_mono x y ((horder x y).mp hlt).le
    · exact le_rfl
  refine {
    out := {
      Vertex := Q.Vertex
      Edge := Q.Edge
      Copy := Q.Copy
      finiteV := Q.finiteV
      finiteE := Q.finiteE
      nonemptyE := hE
      graph := Q.graph
      train := Q.train
      endpoints := ep
      order := o
      part_mono := ?_
      linear := Q.linear
      parameters := Q.parameters
      positiveWagons := fun μ hp ht => (Q.positive μ hp ht).g3 }
    finiteC := Q.finiteC
    family := Q.family
    emb_part := hpart
    emb_order := ?_
    positive := Q.positive
    arrow := hArrow }
  · intro x y h
    by_contra hn
    have ht : o.lt y x := ContactOrderedSeedStage.concatenate_part Q.order
      (S.part ∘ Q.projection.vertex) y x (lt_of_not_ge hn)
    letI : LinearOrder Q.Vertex := o
    exact (not_lt_of_ge h) ht
  · intro i x y h
    -- The picture source order is precisely the chosen input order in
    -- the application; keep its equality explicit instead of silently
    -- allowing a different source order.
    exact Q.originalPartOrder_copy_order hpart hm i x y ((horder x y).mpr h)

end ContactTrainPicture

namespace ContactBoostInput
variable [LinearOrder P] [Finite P] {m : ℕ} {allowed : Fin m → Set P} {q : Fin (m+1) → ℕ}

/-- One forest-boost step on the whole class, starting from any
smaller-bound supply on that class. The starting picture uses the
word seed, so there is no second application of the main theorem. -/
theorem boost_step {Color : Type v} [Finite Color] [Nonempty Color]
    (hm : 0 < m) (hq : ∀ μ, μ.val < m → 2 ≤ q μ)
    {j : ℕ} (hj : 2 ≤ j) (hjQ : j ≤ q 0)
    (hG : ∀ A : ContactBoostInput P m allowed q, LabelledGirthGT A.graph.edgeCarrier (q 0))
    (prev : ∀ A : ContactBoostInput P m allowed q,
      ∃ W : A.Witness Color, W.out.graph.bottomCut.ZeroSmallMixedForestsThrough (j-1))
    (A : ContactBoostInput P m allowed q) :
    ∃ W : A.Witness Color, W.out.graph.bottomCut.ZeroSmallMixedForestsThrough j := by
  classical
  letI : Finite A.Vertex := A.finiteV
  letI : Finite A.Edge := A.finiteE
  letI : LinearOrder A.Vertex := A.order
  let U := A.endpoints
  obtain ⟨N,hN,hword⟩ := U.exists_word_arrow (Color := Color)
  letI : Fintype N := hN
  let idx := Fintype.equivFin N
  letI : LinearOrder N := LinearOrder.lift' idx idx.injective
  letI : WellFoundedLT N := by
    change WellFounded (fun a b : N => idx a < idx b)
    exact InvImage.wf idx (inferInstance : WellFoundedLT (Fin (Fintype.card N)))
  let S := U.wordEndpoints N
  let seed := U.wordSeed N A.linear
  letI : Finite (U.WordVertex N) :=
    Finite.of_injective (fun x : U.WordVertex N => (x.val : P × (N → A.Vertex))) Subtype.val_injective
  letI : Finite (Combinatorics.Line A.Edge N) :=
    Finite.of_injective (fun l => l.idxFun) (fun _ _ he => Combinatorics.Line.ext he)
  letI : Fintype (N → A.Edge) := Fintype.ofFinite _
  letI : LinearOrder (U.WordVertex N) := U.wordOrder N
  have hSmono : @Monotone (U.WordVertex N) P (U.wordOrder N).toPreorder
      (inferInstance : Preorder P) S.part :=
    fun x y h => U.wordPart_order N x y h
  have horder : ∀ i, @StrictMono A.Vertex (U.WordVertex N)
      A.order.toPreorder (U.wordOrder N).toPreorder (seed.vertex i) :=
    fun i x y h => U.wordSeed_order N (fun x y h => A.part_mono x y h) i x y h
  have hpar : ∀ i, A.graph.Parameters A.train
      (fun j => seed.vertex i ⁻¹' (S.part ⁻¹' allowed j)) := by
    intro i
    exact A.parameters
  let Q := seed.initialPicture (T := A.train) hm (fun j => S.part ⁻¹' allowed j) q
    horder U.covered (A.all_cutLinear hq (hG A)) (A.all_wagonBounds (hG A)) hpar
  have hfull : Q.FullBounds := seed.initialPicture_fullBounds (T := A.train) hm
    (fun j => S.part ⁻¹' allowed j) q horder U.covered
    (A.all_cutLinear hq (hG A)) (A.all_wagonBounds (hG A)) hpar
  have hF : Q.Forests j := Q.forests_of_fullBounds hm hfull hjQ
  have hPart : Q.PartPreserving U.part S.part := by intro i x; rfl
  have hbase := U.word_linear N A.linear
  have hSupply : ContactTrainPicture.BoostCoreSupply (D := A.graph) (T := A.train)
      (base := (U.wordHypergraph N).edgeCarrier)
      (allowed := fun j => S.part ⁻¹' allowed j) (q := q) j Color := by
    intro R _ b hne
    let B := R.boostStripInput A S b hne hSmono
    obtain ⟨W,hW⟩ := prev B
    let C := R.boostCore A S b hne hSmono W
    refine ⟨C,hW,?_,W.arrow⟩
    rintro ⟨Z,hZ⟩
    exact hG W.out ⟨Z,hZ.trans hjQ⟩
  have hSeedArrow : ∀ ρ : (N → A.Edge) → Color, ∃ i : Q.Copy, ∃ c : Color,
      ∀ e : A.Edge, ρ (Q.projection.edge ((Q.family.emb i).edge e)) = c :=
    hword
  obtain ⟨R,hR,hRP,hRA⟩ := Q.boost_preservesPart hj hbase
    (fun μ _ h => hq μ h) hSupply hF hPart hSeedArrow
  exact ⟨R.boostWitness A S (fun _ _ => Iff.rfl) hRP hRA,hR⟩

/-- The full forest-boost lemma. Induction on j is genuinely
class-wide, so each local call in the next picture uses the
previous forest bound on a freshly constructed input. -/
theorem forestBoost {Color : Type v} [Finite Color] [Nonempty Color]
    (hm : 0 < m) (hq : ∀ μ, μ.val < m → 2 ≤ q μ)
    (hG : ∀ A : ContactBoostInput P m allowed q, LabelledGirthGT A.graph.edgeCarrier (q 0))
    (base : ∀ A : ContactBoostInput P m allowed q, Nonempty (A.Witness Color)) :
    ∀ n : ℕ, n+1 ≤ q 0 → ∀ A : ContactBoostInput P m allowed q,
      ∃ W : A.Witness Color, W.out.graph.bottomCut.ZeroSmallMixedForestsThrough (n+1) := by
  intro n
  induction n with
  | zero =>
    intro _ A
    obtain ⟨W⟩ := base A
    exact ⟨W,W.out.graph.bottomCut.zeroSmallMixedForests_one⟩
  | succ n ih =>
    intro hn A
    have hn' : n+1 ≤ q 0 := by omega
    apply boost_step hm hq (j := n+2) (by omega) (by omega) hG ?_ A
    intro B
    rw [show n+2-1 = n+1 by omega]
    exact ih hn' B

end ContactBoostInput
end StructuralRamsey.Girth
