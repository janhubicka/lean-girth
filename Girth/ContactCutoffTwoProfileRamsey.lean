import Girth.ContactBoostClass
import Girth.ContactCutoffTwoOrderedSource
import Girth.ContactCutoffTwoAssembly

/-! Ordered arbitrary-profile train inputs and the actual cutoff-two
construction from the strictly shorter train theorem. A profile may
have repeated parts; only the initial and final local core is
transversal. The recursive hypothesis is not restricted to a-partite
trains with one vertex per part. -/

namespace StructuralRamsey.Girth
universe v

/-- The common ordered edge word is part of the type of the input,
so the lower-rank witness has exactly that same profile. -/
structure ContactProfileTrain (P : Type v) [LinearOrder P] (m a : ℕ)
    (allowed : Fin m → Set P) (word : Fin a → P) where
  Vertex : Type v
  Edge : Type v
  Copy : Type v
  finiteV : Finite Vertex
  finiteE : Finite Edge
  nonemptyE : Nonempty Edge
  graph : ContactHypergraphData Vertex Edge Copy
  train : ContactTrainData Edge m
  order : LinearOrder Vertex
  part : Vertex → P
  enumeration : letI : LinearOrder Vertex := order
    Edge → Fin a ↪o Vertex
  carrier_eq : ∀ e, graph.edgeCarrier e = Set.range (enumeration e)
  part_eq : ∀ e i, part (enumeration e i) = word i
  part_mono : ∀ x y, order.le x y → part x ≤ part y
  covered : ∀ x, ∃ e, x ∈ graph.edgeCarrier e
  parameters : graph.Parameters train (fun j => part ⁻¹' allowed j)

namespace ContactProfileTrain
variable {P : Type v} [LinearOrder P] {m a : ℕ}
    {allowed : Fin m → Set P} {word : Fin a → P}
    (A : ContactProfileTrain P m a allowed word)

/-- Full witnesses preserve the actual ordered embeddings and all
proper system bounds. The output input-data record does not assume
these bounds independently of the proof. -/
structure Witness (Color : Type v) where
  out : ContactProfileTrain P m a allowed word
  finiteC : Finite out.Copy
  family : ContactDesignatedEmbeddings A.graph A.train out.graph out.train
  emb_part : ∀ i x, out.part ((family.emb i).vertex x) = A.part x
  emb_order : ∀ i x y, A.order.lt x y → out.order.lt ((family.emb i).vertex x) ((family.emb i).vertex y)
  arrow : family.Arrow Color

def edgeWord : letI : LinearOrder A.Vertex := A.order
    ContactOrderedEdgeWord A.graph P a := by
  letI : LinearOrder A.Vertex := A.order
  exact {
    part := A.part
    word := word
    enumeration := A.enumeration
    carrier_eq := A.carrier_eq
    part_eq := A.part_eq }

include A in
theorem word_mono : Monotone word := by
  letI : LinearOrder A.Vertex := A.order
  let e := Classical.choice A.nonemptyE
  intro i j h
  rw [← A.part_eq e i,← A.part_eq e j]
  exact A.part_mono _ _ ((A.enumeration e).monotone h)

theorem edge_nonempty (ha : 0 < a) (e : A.Edge) : (A.graph.edgeCarrier e).Nonempty := by
  rw [A.carrier_eq]
  exact ⟨A.enumeration e ⟨0,ha⟩,⟨_,rfl⟩⟩

theorem edge_nontrivial (ha : 2 ≤ a) (e : A.Edge) : (A.graph.edgeCarrier e).Nontrivial := by
  rw [A.carrier_eq]
  refine ⟨A.enumeration e ⟨0,by omega⟩,⟨_,rfl⟩,
    A.enumeration e ⟨1,by omega⟩,⟨_,rfl⟩,?_⟩
  intro h
  have he := (A.enumeration e).injective h
  have hval := congrArg Fin.val he
  change (0 : ℕ) = 1 at hval
  omega

theorem linear_of_wagonBounds (hm : 0 < m) (q : Fin (m+1) → ℕ)
    (hq : 2 ≤ q 0) (hG : A.graph.WagonBounds A.train q) :
    ∀ e f : A.Edge, e ≠ f → (A.graph.edgeCarrier e ∩ A.graph.edgeCarrier f).Subsingleton := by
  intro e f hne x hx y hy
  have H := contact_pairwise_of_labelledGirth _ hq (hG 0 (by change (0 : ℕ) < m; omega))
  apply H (A.train.bottomEquiv e) (A.train.bottomEquiv f)
    (fun h => hne (A.train.bottomEquiv.injective h))
  · rw [A.graph.bottom_wagon_carrier A.train,A.graph.bottom_wagon_carrier A.train]
    exact hx
  · rw [A.graph.bottom_wagon_carrier A.train,A.graph.bottom_wagon_carrier A.train]
    exact hy

end ContactProfileTrain

/-- The lower-height theorem, uniformly in part types, profiles,
parameters and finite colour types. The height and bound vector
are fixed; in particular it may be applied with vector colours. -/
def ContactProfileRamsey {m : ℕ} (q : Fin (m+1) → ℕ) : Prop :=
  ∀ (P : Type v) [LinearOrder P] [Finite P] (a : ℕ) (ha : 2 ≤ a)
    (allowed : Fin m → Set P) (word : Fin a → P)
    (A : ContactProfileTrain P m a allowed word),
    A.graph.WagonBounds A.train q →
    ∀ (Color : Type v) [Finite Color] [Nonempty Color],
      ∃ W : A.Witness Color, W.out.graph.SystemBounds W.out.train q

namespace ContactBoostInput
variable {P : Type v} [LinearOrder P] {m : ℕ}
    {allowed : Fin m → Set P} {q : Fin (m+1) → ℕ}

/-- Height one needs no lower-height hypothesis. Use the actual word
construction with the exact height-one relations of the input. -/
theorem cutoffTwo_heightOne {allowed : Fin 1 → Set P} {q : Fin 2 → ℕ}
    [Finite P] {Color : Type v} [Finite Color] [Nonempty Color]
    (A : ContactBoostInput P 1 allowed q) :
    Nonempty (A.Witness Color) := by
  classical
  letI : Finite A.Vertex := A.finiteV
  letI : Finite A.Edge := A.finiteE
  letI : Nonempty A.Edge := A.nonemptyE
  letI : LinearOrder A.Vertex := A.order
  let U := A.endpoints
  obtain ⟨N,hN,hArrow⟩ := U.exists_word_arrow (Color := Color)
  letI : Fintype N := hN
  let idx := Fintype.equivFin N
  letI : LinearOrder N := LinearOrder.lift' idx idx.injective
  letI : WellFoundedLT N := by
    change WellFounded (fun a b : N => idx a < idx b)
    exact InvImage.wf idx (inferInstance : WellFoundedLT (Fin (Fintype.card N)))
  letI : Finite (U.WordVertex N) :=
    Finite.of_injective (fun x : U.WordVertex N => (x.val : P × (N → A.Vertex))) Subtype.val_injective
  letI : Finite (Combinatorics.Line A.Edge N) :=
    Finite.of_injective (fun l => l.idxFun) (fun _ _ he => Combinatorics.Line.ext he)
  let S := contactHeightOne (N → A.Edge)
  let M : ContactDesignatedEmbeddings A.graph A.train (U.wordHypergraph N) S := {
    emb := fun l => {
      vertex := U.lineVertexEmb N l
      edge := U.lineEdgeEmb N l
      carrier_eq := U.line_carrier N l
      rel_iff := fun μ e f =>
        (ContactSeedStage.height_one_rel _ μ _ _).trans
          ((or_congr Iff.rfl ⟨fun h => (U.lineEdgeEmb N l).injective h,
              fun h => congrArg (U.lineEdgeEmb N l) h⟩).trans
            (ContactSeedStage.height_one_rel A.train μ e f).symm)
      strong := U.line_strong N A.linear l }
    vertex_eq := fun _ => rfl
    edge_eq := fun _ => rfl }
  refine ⟨{
    out := {
      Vertex := U.WordVertex N
      Edge := N → A.Edge
      Copy := Combinatorics.Line A.Edge N
      finiteV := inferInstance
      finiteE := inferInstance
      nonemptyE := ⟨fun _ => Classical.choice A.nonemptyE⟩
      graph := U.wordHypergraph N
      train := S
      endpoints := U.wordEndpoints N
      order := U.wordOrder N
      part_mono := U.wordPart_order N
      linear := U.word_linear N A.linear
      parameters := ?_
      positiveWagons := ?_ }
    finiteC := inferInstance
    family := M
    emb_part := fun _ _ => rfl
    emb_order := fun l x y h => U.wordSeed_order N (fun x y h => A.part_mono x y h) l x y h
    positive := ?_
    arrow := hArrow }⟩
  · intro j e f x he hx hy hn
    have hj : j = 0 := Fin.ext (by have := j.isLt; omega)
    subst j
    by_contra hef
    have hne : e ≠ f := fun h => hef (congrArg (S.parent 0) h)
    obtain ⟨u,w,huw,hu⟩ := U.word_intersection_part N e f hne x ⟨hx,hy⟩
    have hu' : U.endpoint u (U.wordPart N x) ∈ A.graph.edgeCarrier u :=
      U.endpoint_mem u _
    have hw' : U.endpoint u (U.wordPart N x) ∈ A.graph.edgeCarrier w :=
      hu.symm ▸ U.endpoint_mem w _
    have hnot : U.endpoint u (U.wordPart N x) ∉ U.part ⁻¹' allowed 0 := by
      intro hp
      apply hn
      change U.part (U.endpoint u (U.wordPart N x)) ∈ allowed 0 at hp
      rw [U.part_endpoint] at hp
      exact hp
    have hb := A.parameters 0 u w _ (A.train.top u w) hu' hw' hnot
    exact huw (A.train.bottom hb)
  · intro μ hp ht
    omega
  · intro μ hp ht
    omega

end ContactBoostInput

namespace ContactCutoffTwoInput
variable {P V E I X F J C : Type v} [LinearOrder P]
    [LinearOrder V] [LinearOrder X] [Fintype X]
    {m : ℕ} {D : ContactHypergraphData V E I}
    {T : ContactTrainData E (m+1)} {L : ContactHypergraphData X F J}
    (A : ContactCutoffTwoInput D T L C)
    {part : V → P} {templatePart : X → P}
    (O : A.OrderedSource part templatePart)

/-- A padded source is covered because each original vertex
is in some first wagon, and each private padding position is in
its own padded wagon. -/
theorem source_covered (hc : ∀ x : V, ∃ e, x ∈ D.edgeCarrier e) :
    ∀ x, ∃ e, x ∈ A.source.edgeCarrier e := by
  rintro ⟨c,x⟩
  cases x with
  | inl x =>
    obtain ⟨e,he⟩ := hc x
    let p := T.parent (0 : Fin (m+1)).succ e
    have hx : x ∈ (D.atCut (T.parent (0 : Fin (m+1)).succ)).contactWagonCarrier p :=
      ⟨e,rfl,he⟩
    refine ⟨(c,p),?_⟩
    rw [← A.fill.range_eq]
    exact ⟨(A.pad c).inside p ⟨x,hx⟩,by
      change (⟨c,(A.pad c).placeFun p ((A.pad c).inside p ⟨x,hx⟩)⟩ : A.Vertex) = _
      rw [(A.pad c).placeFun_old]
      rfl⟩
  | inr x =>
    rcases x with ⟨p,⟨x,hx⟩⟩
    refine ⟨(c,p),?_⟩
    rw [← A.fill.range_eq]
    exact ⟨x,by
      change (⟨c,(A.pad c).placeFun p x⟩ : A.Vertex) = _
      rw [(A.pad c).placeFun_private p x hx]⟩

/-- Build the genuine input of the shorter theorem with its full
(possibly nontransversal) part word. The inherited parameters allow
all vertices of the given part, not only the original unpadded ones. -/
noncomputable def profileSource [Finite V] [Finite E] [Finite C]
    (hne : Nonempty A.OldEdge) (hc : ∀ x : V, ∃ e, x ∈ D.edgeCarrier e)
    (allowed : Fin (m+1) → Set P)
    (hp : D.Parameters T (fun j => part ⁻¹' allowed j)) :
    ContactProfileTrain P m (Fintype.card X) (fun j => allowed j.succ)
      (fun i => templatePart (Fintype.orderIsoFinOfCardEq X rfl i)) := by
  letI : Finite T.FirstWagon := Finite.of_surjective (T.parent (0 : Fin (m+1)).succ) (T.surj _)
  letI : ∀ c : C, Finite (A.Component c) := fun c => by
    apply Finite.of_injective (fun z : A.Component c =>
      match z with
      | .inl x => (Sum.inl x : V ⊕ (T.FirstWagon × X))
      | .inr p => Sum.inr (p.1,p.2.val))
    intro x y he
    cases x with
    | inl x =>
      cases y with
      | inl y => exact congrArg Sum.inl (Sum.inl.inj he)
      | inr y => cases he
    | inr x =>
      rcases x with ⟨p,⟨u,hu⟩⟩
      cases y with
      | inl y => cases he
      | inr y =>
        rcases y with ⟨q,⟨w,hw⟩⟩
        have h := Sum.inr.inj he
        have hp : p = q := congrArg Prod.fst h
        have hu' : u = w := congrArg Prod.snd h
        subst q
        subst w
        rfl
  letI : Finite A.Vertex := inferInstanceAs (Finite (Sigma A.Component))
  letI : LinearOrder A.Vertex := O.order
  let W := O.edgeWord
  refine {
    Vertex := A.Vertex
    Edge := A.OldEdge
    Copy := PEmpty.{v+1}
    finiteV := inferInstance
    finiteE := inferInstance
    nonemptyE := hne
    graph := A.source
    train := A.sourceTrain
    order := O.order
    part := W.part
    enumeration := W.enumeration
    carrier_eq := W.carrier_eq
    part_eq := W.part_eq
    part_mono := ?_
    covered := A.source_covered hc
    parameters := ?_ }
  · intro x y h
    letI : LinearOrder A.Vertex := O.order
    have h' : x ≤ y := h
    rcases lt_or_eq_of_le h' with hlt | he
    · exact O.part_order x y hlt
    · exact le_of_eq (congrArg W.part he)
  · intro j
    apply A.source.parameter_mono A.sourceTrain j.castSucc j.succ
      (A := {x | x.2 ∈ (A.pad x.1).oldVertex '' (part ⁻¹' allowed j.succ)})
    · intro z hz
      rcases z with ⟨c,x⟩
      change x ∈ (A.pad c).oldVertex '' (part ⁻¹' allowed j.succ) at hz
      obtain ⟨u,hu,hux⟩ := hz
      change A.paddedPart part templatePart c x ∈ allowed j.succ
      rw [← hux]
      exact hu
    · exact A.source_parameters (fun j => part ⁻¹' allowed j.succ)
        (fun j => hp j.succ) j

/-- A canonical placement of the template into every output
shorter edge, using the common ordered profile rather than a new
cardinality hypothesis. -/
noncomputable def profileFilling
    {allowed : Fin m → Set P}
    (B : ContactProfileTrain P m (Fintype.card X) allowed
      (fun i => templatePart (Fintype.orderIsoFinOfCardEq X rfl i))) :
    ContactFilling B.graph L where
  place := fun e =>
    letI : LinearOrder B.Vertex := B.order
    ((Fintype.orderIsoFinOfCardEq X rfl).symm.toOrderEmbedding.trans
      (B.enumeration e)).toEmbedding
  range_eq := by
    intro e
    rw [B.carrier_eq]
    ext x
    constructor
    · rintro ⟨y,rfl⟩
      exact ⟨(Fintype.orderIsoFinOfCardEq X rfl).symm y,rfl⟩
    · rintro ⟨i,rfl⟩
      exact ⟨Fintype.orderIsoFinOfCardEq X rfl i,by
        change B.enumeration e ((Fintype.orderIsoFinOfCardEq X rfl).symm
          (Fintype.orderIsoFinOfCardEq X rfl i)) = _
        rw [OrderIso.symm_apply_apply]⟩
  template_cover := A.cover
  template_nonempty := A.nonempty

/-- The canonical increasing filling preserves the template part
at every position, including padded positions. -/
theorem profileFilling_part {allowed : Fin m → Set P}
    (B : ContactProfileTrain P m (Fintype.card X) allowed
      (fun i => templatePart (Fintype.orderIsoFinOfCardEq X rfl i)))
    (e : B.Edge) (x : X) :
    B.part ((A.profileFilling B).place e x) = templatePart x := by
  change B.part (B.enumeration e ((Fintype.orderIsoFinOfCardEq X rfl).symm x)) = _
  rw [B.part_eq,OrderIso.apply_symm_apply]

/-- Compatibility follows from uniqueness of the increasing
enumeration of a finite edge. This proof uses only the well-founded
order on Fin, not a further compatibility premise on the witness. -/
theorem profileFilling_compatible [Finite V] [Finite E] [Finite C]
    (hne : Nonempty A.OldEdge) (hc : ∀ x : V, ∃ e, x ∈ D.edgeCarrier e)
    (allowed : Fin (m+1) → Set P)
    (hp : D.Parameters T (fun j => part ⁻¹' allowed j))
    {Color : Type v}
    (W : (A.profileSource O hne hc allowed hp).Witness Color)
    (j : W.out.Copy) (e : A.OldEdge) (x : X) :
    (A.profileFilling W.out).place ((W.family.emb j).edge e) x =
      (W.family.emb j).vertex (A.fill.place e x) := by
  let R := A.profileSource O hne hc allowed hp
  letI : LinearOrder R.Vertex := R.order
  letI : LinearOrder W.out.Vertex := W.out.order
  let k := Fintype.orderIsoFinOfCardEq X rfl
  let f : Fin (Fintype.card X) → W.out.Vertex :=
    W.out.enumeration ((W.family.emb j).edge e)
  let g : Fin (Fintype.card X) → W.out.Vertex :=
    fun i => (W.family.emb j).vertex (A.fill.place e (k i))
  have hf : StrictMono f := (W.out.enumeration _).strictMono
  have hg : StrictMono g := fun i l h =>
    W.emb_order j _ _ (O.place_order e _ _ (k.strictMono h))
  have hr : Set.range f = Set.range g := by
    calc
      Set.range f = W.out.graph.edgeCarrier ((W.family.emb j).edge e) :=
        (W.out.carrier_eq ((W.family.emb j).edge e)).symm
      _ = (W.family.emb j).vertex '' A.source.edgeCarrier e :=
        (W.family.emb j).carrier_eq e
      _ = Set.range g := by
        rw [← A.fill.range_eq e]
        ext y
        constructor
        · rintro ⟨z,⟨u,rfl⟩,rfl⟩
          refine ⟨k.symm u,?_⟩
          change (W.family.emb j).vertex (A.fill.place e (k (k.symm u))) =
            (W.family.emb j).vertex (A.fill.place e u)
          rw [k.apply_symm_apply]
        · rintro ⟨i,rfl⟩
          exact ⟨A.fill.place e (k i),⟨k i,rfl⟩,rfl⟩
  have h := congrFun (hf.range_inj_of_wellFoundedLT hg |>.mp hr) (k.symm x)
  change W.out.enumeration ((W.family.emb j).edge e) (k.symm x) =
    (W.family.emb j).vertex (A.fill.place e (k (k.symm x))) at h
  rw [k.apply_symm_apply] at h
  exact h

end ContactCutoffTwoInput

namespace ContactBoostInput
variable {P : Type v} [LinearOrder P] [Finite P] [Nontrivial P]
    {m : ℕ} {allowed : Fin (m+1) → Set P} {q : Fin (m+2) → ℕ}

/-- The positive-level Ramsey supply at height m+1, derived from
the full Ramsey theorem at height m on arbitrary profiles. The
bottom budget q 0 is deliberately irrelevant to this theorem. -/
theorem cutoffTwo_of_tailRamsey {Color : Type v} [Finite Color] [Nonempty Color]
    (hm : 0 < m) (hq : ∀ μ : Fin (m+1), μ.val < m → 2 ≤ q μ.succ)
    (lower : ContactProfileRamsey.{v} (fun μ : Fin (m+1) => q μ.succ))
    (A : ContactBoostInput P (m+1) allowed q) :
    Nonempty (A.Witness Color) := by
  classical
  letI : Finite A.Vertex := A.finiteV
  letI : Fintype A.Vertex := Fintype.ofFinite _
  letI : Finite A.Edge := A.finiteE
  letI : Nonempty A.Edge := A.nonemptyE
  letI : LinearOrder A.Vertex := A.order
  let U := A.endpoints
  have hmU : Monotone U.part := fun x y h => A.part_mono x y h
  obtain ⟨N,hN,hword⟩ := U.cutoffInput_arrow A.train (Color := Color)
  letI : Fintype N := hN
  let idx := Fintype.equivFin N
  letI : LinearOrder N := LinearOrder.lift' idx idx.injective
  letI : WellFoundedLT N := by
    change WellFounded (fun a b : N => idx a < idx b)
    exact InvImage.wf idx (inferInstance : WellFoundedLT (Fin (Fintype.card N)))
  letI : Finite A.train.FirstWagon := Finite.of_surjective
    (A.train.parent (0 : Fin (m+1)).succ) (A.train.surj _)
  letI : Finite (ContactPartiteEndpoints.FirstVertex (D := A.graph) A.train) := Finite.of_injective
    (fun x : ContactPartiteEndpoints.FirstVertex (D := A.graph) A.train => (x.1,x.2.val)) (by
      rintro ⟨p,x⟩ ⟨r,y⟩ he
      have hp : p = r := congrArg Prod.fst he
      subst r
      have he' : x = y := Subtype.ext (congrArg Prod.snd he)
      subst y
      rfl)
  let EP := (U.firstEndpoints A.train).wordEndpoints N
  let X := U.CutoffWordVertex A.train N
  letI : Finite X := Finite.of_injective
    (fun x : X => (x.val : P × (N → ContactPartiteEndpoints.FirstVertex (D := A.graph) A.train))) Subtype.val_injective
  letI : Fintype X := Fintype.ofFinite _
  letI : LinearOrder X := U.cutoffWordOrder A.train N
  letI : Finite (Combinatorics.Line A.Edge N) :=
    Finite.of_injective (fun l => l.idxFun) (fun _ _ he => Combinatorics.Line.ext he)
  letI : Fintype (Combinatorics.Line A.Edge N) := Fintype.ofFinite _
  let C := U.cutoffInput A.train N hm A.linear
  let O := U.cutoffOrderedSource A.train N hm A.linear hmU
  have hline : Nonempty (Combinatorics.Line A.Edge N) := by
    obtain ⟨l,_,_⟩ := hword (fun _ => Classical.choice (inferInstance : Nonempty Color))
    exact ⟨l⟩
  have hsource : Nonempty C.OldEdge := ⟨(Classical.choice hline,
    A.train.parent (0 : Fin (m+1)).succ (Classical.choice A.nonemptyE))⟩
  let R := C.profileSource O hsource U.covered allowed A.parameters
  have hR : R.graph.WagonBounds R.train (fun μ : Fin (m+1) => q μ.succ) := by
    apply C.source_wagonBounds
    intro μ ht
    exact A.positiveWagons μ.succ (by change 0 < μ.val+1; omega)
      (by change μ.val+1 < m+1; omega)
  let f₀ : N → A.Edge := fun _ => Classical.choice A.nonemptyE
  have ha : 2 ≤ Fintype.card X := by
    letI : Nontrivial X := ⟨by
      obtain ⟨x,y,hxy⟩ := exists_pair_ne P
      exact ⟨EP.endpoint f₀ x,EP.endpoint f₀ y,
        fun he => hxy (EP.endpoint_inj f₀ he)⟩⟩
    exact Fintype.one_lt_card
  letI : Finite ((N → A.Edge) → Color) := inferInstance
  letI : Nonempty ((N → A.Edge) → Color) :=
    ⟨fun _ => Classical.choice (inferInstance : Nonempty Color)⟩
  obtain ⟨W,hW⟩ := lower P (Fintype.card X) ha
    (fun j => allowed j.succ)
    (fun i => EP.part (Fintype.orderIsoFinOfCardEq X rfl i)) R hR
    ((N → A.Edge) → Color)
  let B := C.profileFilling (templatePart := EP.part) W.out
  have hplace : ∀ j e x, B.place ((W.family.emb j).edge e) x =
      (W.family.emb j).vertex (C.fill.place e x) :=
    C.profileFilling_compatible O hsource U.covered allowed A.parameters W
  let H := C.resultHypergraph W.family B hplace
  let S := B.fillTrain W.out.train
  let M := C.resultFamily W.family B hplace
  have hBP (e : W.out.Edge) (x : X) : W.out.part (B.place e x) = EP.part x :=
    C.profileFilling_part (templatePart := EP.part) W.out e x
  have hlin : ∀ e f : N → A.Edge, e ≠ f →
      ((U.cutoffTemplate A.train N).edgeCarrier e ∩
        (U.cutoffTemplate A.train N).edgeCarrier f).Subsingleton :=
    (U.firstEndpoints A.train).word_linear N (U.firstDisjoint_linear A.train A.linear)
  have hWlin := W.out.linear_of_wagonBounds hm (fun μ => q μ.succ)
    (hq 0 (by change (0 : ℕ) < m; omega)) (W.out.graph.systemBounds_wagonBounds W.out.train hW)
  have hsize : 0 < Fintype.card X := by omega
  have hpositive' := C.result_positiveBounds W.family B hplace
    (fun μ : Fin (m+1) => q μ.succ) hW (W.out.edge_nonempty hsize) hlin
  have hpositive : H.PositiveBounds S q := by
    intro μ
    refine Fin.cases ?_ (fun ν => ?_) μ
    · intro h0
      change 0 < 0 at h0
      omega
    · intro hpos hproper
      exact hpositive' ν.succ hpos hproper
  have hpar : H.Parameters S (fun j => W.out.part ⁻¹' allowed j) := by
    intro j
    refine Fin.cases ?_ (fun k => ?_) j
    · apply C.result_first_parameter W.family B hplace
      intro e f g hfg
      rintro x ⟨y,hy,rfl⟩
      change W.out.part (B.place e y) ∈ allowed 0
      rw [hBP]
      exact U.cutoffTemplate_allowed A.train N (allowed 0) (A.parameters 0) f g hfg y hy
    · exact C.result_inherited_parameter W.family B hplace k.castSucc k.succ _
        (W.out.parameters k)
  let endp : ContactPartiteEndpoints H P := {
    part := W.out.part
    endpoint := fun e p => B.place e.1 (EP.endpoint e.2 p)
    part_endpoint := by
      intro e p
      rw [hBP,EP.part_endpoint]
    carrier_eq := by
      intro e
      change B.place e.1 '' (U.cutoffTemplate A.train N).edgeCarrier e.2 = _
      rw [EP.carrier_eq,Set.image_range]
    covered := by
      intro x
      obtain ⟨e,he⟩ := W.out.covered x
      obtain ⟨f,hf⟩ := B.output_cover e x he
      exact ⟨(e,f),hf⟩ }
  refine ⟨{
    out := {
      Vertex := W.out.Vertex
      Edge := W.out.Edge × (N → A.Edge)
      Copy := W.out.Copy × Combinatorics.Line A.Edge N
      finiteV := W.out.finiteV
      finiteE := by
        letI : Finite W.out.Edge := W.out.finiteE
        infer_instance
      nonemptyE := ⟨(Classical.choice W.out.nonemptyE,f₀)⟩
      graph := H
      train := S
      endpoints := endp
      order := W.out.order
      part_mono := W.out.part_mono
      linear := C.result_linear W.family B hplace hWlin hlin
      parameters := hpar
      positiveWagons := fun μ hp ht => (hpositive μ hp ht).g3 }
    finiteC := by
      letI : Finite W.out.Copy := W.finiteC
      infer_instance
    family := M
    emb_part := ?_
    emb_order := ?_
    positive := hpositive
    arrow := C.result_arrow W.family B hplace W.arrow hword }⟩
  · rintro ⟨j,c⟩ x
    change W.out.part ((W.family.emb j).vertex ((C.original c).vertex x)) = U.part x
    calc
      _ = C.sourcePart U.part EP.part ((C.original c).vertex x) :=
        W.emb_part j ((C.original c).vertex x)
      _ = U.part x := O.original_part c x
  · rintro ⟨j,c⟩ x y h
    exact W.emb_order j _ _ (O.original_order c x y h)

end ContactBoostInput
end StructuralRamsey.Girth
