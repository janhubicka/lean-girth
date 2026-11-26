import Girth.ContactRankAssembly
import Girth.ContactRefinedCoreAssembly
import Girth.ContactCutoffTwoProfileRamsey

/-! The actual finite train Ramsey induction. The induction hypothesis
ranges over ALL ordered profiles, parameters, finite part types and
finite colour types. The only recursive requests are the positive
tails in the two local core constructions. Their strict decrease
is proved on the actual cutoff multiplicity list in ContactRankAssembly.
-/

namespace StructuralRamsey.Girth
universe v

/-- The height-one word supply or the arbitrary-profile shorter theorem
gives the base case of the class-wide forest boost. The bottom
budget of the boost is not an input to the shorter theorem. -/
theorem contactBoostBase_from_lower
    {P : Type v} [LinearOrder P] [Finite P] [Nontrivial P]
    {m : ℕ} {allowed : Fin m → Set P} {q : Fin (m+1) → ℕ}
    {Color : Type v} [Finite Color] [Nonempty Color]
    (hm : 0 < m) (hq : ∀ μ, μ.val < m → 2 ≤ q μ)
    (lower : 0 < m-1 → ContactProfileRamsey.{v} (contactTailBounds q))
    (A : ContactBoostInput P m allowed q) : Nonempty (A.Witness Color) := by
  cases m with
  | zero => omega
  | succ n =>
    cases n with
    | zero => exact ContactBoostInput.cutoffTwo_heightOne A
    | succ n =>
      have hLower := lower (by omega)
      rw [contactTailBounds_succ] at hLower
      exact ContactBoostInput.cutoffTwo_of_tailRamsey
        (by omega) (fun μ hμ => hq μ.succ (by change μ.val+1 < n+2; omega)) hLower A

namespace ContactProfileTrain
variable {P : Type v} [LinearOrder P] {m a : ℕ}
    {allowed : Fin m → Set P} {word : Fin a → P}
    (A : ContactProfileTrain P m a allowed word)

/-- Recover the actual profile witness from a final train picture.
Reordering by original parts preserves both the designated embeddings
and the common edge word, even if a part occurs repeatedly. -/
noncomputable def witnessFromPicture
    {X B : Type v} [LinearOrder X] [LinearOrder A.Vertex]
    {base : B → Set X} {q : Fin (m+1) → ℕ}
    (label : X → P) (enumeration : B → Fin a ↪o X)
    (he : ∀ b, base b = Set.range (enumeration b))
    (hw : ∀ b i, label (enumeration b i) = word i)
    (Q : ContactTrainPicture A.graph A.train base (fun j => label ⁻¹' allowed j) q)
    (hord : ∀ x y : A.Vertex, x < y ↔ A.order.lt x y)
    {Color : Type v} [Nonempty Color]
    (hpart : Q.PartPreserving A.part label)
    (hArrow : Q.family.Arrow Color) : A.Witness Color := by
  classical
  let o := Q.originalPartOrder label
  let f (e : Q.Edge) (i : Fin a) : Q.Vertex :=
    Q.liftEnumeration enumeration he e i
  have hf (e : Q.Edge) (i j : Fin a) (hij : i < j) : o.lt (f e i) (f e j) :=
    Q.originalPartOrder_edge_order label word enumeration he hw A.word_mono e i j hij
  have hmono : Monotone A.part := by
    intro x y hxy
    rcases lt_or_eq_of_le hxy with h | rfl
    · letI : LinearOrder A.Vertex := A.order
      exact A.part_mono x y ((hord x y).mp h).le
    · exact le_rfl
  have hE : Nonempty Q.Edge := by
    obtain ⟨i,_,_⟩ := hArrow (fun _ => Classical.choice (inferInstance : Nonempty Color))
    exact ⟨(Q.family.emb i).edge (Classical.choice A.nonemptyE)⟩
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
      order := o
      part := label ∘ Q.projection.vertex
      enumeration := fun e =>
        letI : LinearOrder Q.Vertex := o
        OrderEmbedding.ofStrictMono (f e) (fun i j h => hf e i j h)
      carrier_eq := Q.liftEnumeration_carrier enumeration he
      part_eq := ?_
      part_mono := ?_
      covered := Q.covered
      parameters := Q.parameters }
    finiteC := Q.finiteC
    family := Q.family
    emb_part := hpart
    emb_order := ?_
    arrow := hArrow }
  · intro e i
    change label (Q.projection.vertex (f e i)) = word i
    rw [(Q.liftEnumeration_spec enumeration he e i).2]
    exact hw _ _
  · intro x y h
    change label (Q.projection.vertex x) ≤ label (Q.projection.vertex y)
    by_contra hn
    have ht : o.lt y x := ContactOrderedSeedStage.concatenate_part Q.order
      (label ∘ Q.projection.vertex) y x (lt_of_not_ge hn)
    letI : LinearOrder Q.Vertex := o
    exact (not_lt_of_ge h) ht
  · intro i x y h
    exact Q.originalPartOrder_copy_order hpart hmono i x y ((hord x y).mpr h)

/-- Edge labels are injective once the proper bottom cut has girth
greater than two and the common profile has size at least two. -/
theorem carrier_injective_of_linear (ha : 2 ≤ a)
    (hl : ∀ e f : A.Edge, e ≠ f →
      (A.graph.edgeCarrier e ∩ A.graph.edgeCarrier f).Subsingleton) :
    Function.Injective A.graph.edgeCarrier := by
  intro e f he
  by_contra hn
  obtain ⟨x,hx,y,hy,hxy⟩ := A.edge_nontrivial ha e
  exact hxy (hl e f hn ⟨hx,he ▸ hx⟩ ⟨hy,he ▸ hy⟩)

end ContactProfileTrain

/-- The main step of the well-founded induction, with the exact
numerical lower-rank premise. It does not assume the desired
Ramsey arrow, a system witness, or a local core supply. -/
theorem contactProfileRamsey_step
    (M h : ℕ) (q : Fin (h+2) → ℕ) (hOK : ContactRankOK M q)
    (lower : ∀ (n : ℕ) (p : Fin (n+1) → ℕ), 0 < n →
      TrainCountLex M (contactCutoffs p) (contactCutoffs q) →
      ContactRankOK M p → ContactProfileRamsey.{v} p) :
    ContactProfileRamsey.{v} q := by
  classical
  intro P _ _ a ha allowed word A hG Color _ _
  letI : Finite A.Vertex := A.finiteV
  letI : Fintype A.Vertex := Fintype.ofFinite _
  letI : Finite A.Edge := A.finiteE
  letI : Nonempty A.Edge := A.nonemptyE
  letI : LinearOrder A.Vertex := A.order
  letI : Fintype Color := Fintype.ofFinite _
  have hq (μ : Fin (h+2)) (hμ : μ.val < h+1) : 2 ≤ q μ := (hOK.1 μ hμ).1
  have hq0 := hq 0 (by change (0 : ℕ) < h+1; omega)
  have hl := A.linear_of_wagonBounds (by omega) q hq0 hG
  have hlin (μ : Fin (h+2)) (hμ : μ.val < h+1) :
      (A.graph.atCut (A.train.parent μ)).ContactLinear :=
    ⟨hl,contact_pairwise_of_labelledGirth _ (hq μ hμ) (hG μ hμ)⟩
  let U := A.edgeWord
  obtain ⟨S⟩ := U.exists_ordered_linear_seed (Color := Color)
    (A.carrier_injective_of_linear ha hl) hl
  letI : Finite S.Vertex := S.finiteV
  letI : Finite S.Edge := S.finiteE
  letI : Finite S.Copy := S.finiteC
  letI : Fintype S.Edge := Fintype.ofFinite _
  letI : LinearOrder S.Vertex := S.order
  let params : Fin (h+1) → Set S.Vertex := fun j => S.part ⁻¹' allowed j
  let Q := S.trainPicture A.train allowed q (by omega) A.covered hlin hG A.parameters
  have hP : Q.FullBounds :=
    S.trainPicture_fullBounds A.train allowed q (by omega) A.covered hlin hG A.parameters
  have hpart : Q.PartPreserving A.part S.part :=
    S.trainPicture_partPreserving (T := A.train) allowed q (by omega)
      A.covered hlin hG A.parameters
  have hArrow : ∀ ρ : S.Edge → Color, ∃ i : Q.Copy, ∃ c : Color,
      ∀ e : A.Edge, ρ (Q.projection.edge ((Q.family.emb i).edge e)) = c :=
    S.trainPicture_arrow A.train allowed q (by omega) A.covered hlin hG A.parameters
  have hsize (b : S.Edge) : (S.graph.edgeCarrier b).Nontrivial := by
    rw [S.carrier_eq]
    refine ⟨S.enumeration b ⟨0,by omega⟩,⟨_,rfl⟩,
      S.enumeration b ⟨1,by omega⟩,⟨_,rfl⟩,?_⟩
    intro h
    have he := (S.enumeration b).injective h
    have hv := congrArg Fin.val he
    change (0 : ℕ) = 1 at hv
    omega
  have hnt (b : S.Edge) : Nontrivial (S.graph.edgeCarrier b) := by
    obtain ⟨x,hx,y,hy,hxy⟩ := hsize b
    exact ⟨⟨⟨x,hx⟩,⟨y,hy⟩,fun he => hxy (congrArg Subtype.val he)⟩⟩
  have hex : ∃ R : ContactTrainPicture A.graph A.train S.graph.edgeCarrier params q,
      R.FullBounds ∧ R.PartPreserving A.part S.part ∧ R.family.Arrow Color := by
    by_cases htwo : q 0 = 2
    · have hLower : 0 < h → ContactProfileRamsey.{v} (contactTailBounds q) := by
        intro hh
        exact lower h _ hh (contactTailBounds_rankDecrease_two q hOK htwo)
          (contactTailBounds_rankOK q (by omega) hOK)
      have supply : ContactTrainPicture.MainCoreSupply
          (D := A.graph) (T := A.train) (base := S.graph.edgeCarrier)
          (allowed := params) (q := q) S.linear hq (fun _ _ => True) Color := by
        intro R done b _ _ _ hn
        letI : Nontrivial (S.graph.edgeCarrier b) := hnt b
        obtain ⟨C,hC,hS,hA⟩ := R.coarseCore_of_cutoffTwo b hn hq htwo (hsize b) (by
          intro K
          exact contactBoostBase_from_lower (by omega) hq hLower K)
        exact ⟨C,hC,hS,hA,True.intro⟩
      exact Q.main_preservesPart (by omega) S.linear hq (fun _ _ => True)
        (fun _ _ _ _ => True.intro) supply hP True.intro hpart hArrow
    · have hbig : 2 < q 0 := by omega
      let g := contactRefinementCutoff (q 0)
      have hg : 2 ≤ g := (contactRefinementCutoff_bounds hbig).1
      have hg0 : g ≤ q 0 := (contactRefinementCutoff_bounds hbig).2.1.le
      have hk : q 0 ≤ 2*g+1 := (contactRefinementCutoff_bounds hbig).2.2
      have hfirst : 0 < h → q 0 ≤ q ⟨1,by omega⟩ := by
        intro hh
        exact hOK.2 0 ⟨1,by omega⟩ (by change (0 : ℕ) ≤ 1; omega)
          (by change 1 < h+1; omega)
      have hg1 : 0 < h → g ≤ q ⟨1,by omega⟩ := fun hh => hg0.trans (hfirst hh)
      have hInv : ContactTrainPicture.HasFutureRefinements g Q [] :=
        S.toSeed.initial_hasFutureRefinements A.train params q
          (fun i x y h => S.emb_order i x y h) A.covered hlin hG
          (S.seed_parameters A.train allowed A.parameters) hg0
      have supply : ContactTrainPicture.MainCoreSupply
          (D := A.graph) (T := A.train) (base := S.graph.edgeCarrier)
          (allowed := params) (q := q) S.linear hq
          (ContactTrainPicture.HasFutureRefinements g) Color := by
        intro R done b hR hI hb hn
        obtain ⟨r⟩ := hI b hb hn
        letI : Nontrivial (S.graph.edgeCarrier b) := hnt b
        have hd := r.depth_pos
        have hLower : 0 < r.depth+h-1 →
            ContactProfileRamsey.{v} (contactTailBounds (r.boostBounds q)) := by
          intro hh
          exact lower (r.depth+h-1) _ hh
            (r.shorter_refined_rankDecrease M q hOK hbig rfl)
            (r.shorter_refined_rankOK M q hOK hg hg0)
        obtain ⟨C,hC,hS,hA⟩ := R.refinedCore_of_cutoffTwo b r hn hg hq hk hfirst
          (hsize b) (by
            intro K
            exact contactBoostBase_from_lower (by omega) (r.boostBounds_two q hg hq) hLower K)
        exact ⟨C,hC,hS,hA,C.next_hasFutureRefinements hn hg hg0 hg1 S.linear hq hR hC hS hI⟩
      exact Q.main_preservesPart (by omega) S.linear hq
        (ContactTrainPicture.HasFutureRefinements g)
        (fun _ _ _ h => ContactTrainPicture.hasFutureRefinements_skip h)
        supply hP hInv hpart hArrow
  obtain ⟨R,hR,hPart,hA⟩ := hex
  let W := A.witnessFromPicture S.part S.enumeration S.carrier_eq S.part_eq R
    (fun _ _ => Iff.rfl) hPart hA
  exact ⟨W,hR⟩

/-- UNCONDITIONAL ordered train Ramsey theorem for every nonempty
nondecreasing finite proper cutoff vector bounded by M. The proof
is well-founded induction on cutoff multiplicities, not induction
on height or on a numerical sum. -/
theorem contactProfileRamsey_wellFounded (M : ℕ) :
    ∀ (m : ℕ) (q : Fin (m+1) → ℕ), 0 < m →
      ContactRankOK M q → ContactProfileRamsey.{v} q := by
  have aux : ∀ t : List ℕ, ∀ (m : ℕ) (q : Fin (m+1) → ℕ),
      contactCutoffs q = t → 0 < m → ContactRankOK M q →
        ContactProfileRamsey.{v} q := by
    intro t
    induction t using (trainCountLex_wellFounded M).induction with
    | h t ih =>
      intro m q ht hm hOK
      cases m with
      | zero => omega
      | succ h =>
        apply contactProfileRamsey_step M h q hOK
        intro n p hn hrank hp
        have hlt : TrainCountLex M (contactCutoffs p) t := by
          rw [← ht]
          exact hrank
        exact ih (contactCutoffs p) hlt n p rfl hn hp
  intro m q hm hOK
  exact aux (contactCutoffs q) m q rfl hm hOK

end StructuralRamsey.Girth
