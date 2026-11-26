import Girth.ContactOuterCompletionStep
import Girth.ContactCoveredProfile
import Girth.ContactRefinedCoreAssembly
import Girth.ContactPartPreservation

/-! The outer iteration with a genuinely supplied local-forest core.
The same height-one picture data are reused. The outer property is
qualitative, not full system girth at the large completion cutoff.
-/

namespace StructuralRamsey.Girth
universe v
variable {V E I X B J L : Type v}
variable {D : ContactHypergraphData V E I} {T : ContactTrainData E 1}
    {base : B → Set X} [LinearOrder V] [LinearOrder X]
    {allowed : Fin 1 → Set X} {q : Fin 2 → ℕ}

namespace ContactTrainPicture
variable (P : ContactTrainPicture D T base allowed q)

/-- The covered local-forest theorem applied to the actual active
strip, via the already existing coarse-core interface. No separate
local-core assumption occurs in the outer iteration. -/
theorem outerCore_of_invariant {Color : Type v} [Finite Color] [Nonempty Color]
    (b : B) (hne : Nonempty (P.projection.StripEdge b))
    (m : ℕ) (hm : 2 ≤ m) (hsize : (base b).Nontrivial)
    (hP : P.OuterInvariant m) :
    ∃ C : P.Core b, C.graph.CopyCovered ∧
      C.graph.bottomCut.ZeroSmallMixedForestsThrough m ∧ C.family.Arrow Color := by
  classical
  letI : Finite P.Vertex := P.finiteV
  let C₀ := P.coarseBoostInput b hne
  let EP := C₀.endpoints
  letI : LinearOrder C₀.Vertex := C₀.order
  letI : Finite (base b) := Finite.of_injective
    (EP.endpoint (Classical.choice C₀.nonemptyE)) (EP.endpoint_inj _)
  letI : Fintype (base b) := Fintype.ofFinite _
  letI : Nontrivial (base b) := by
    obtain ⟨x,hx,y,hy,hxy⟩ := hsize
    exact ⟨⟨⟨x,hx⟩,⟨y,hy⟩,fun he => hxy (congrArg Subtype.val he)⟩⟩
  have ha : 2 ≤ Fintype.card (base b) := Fintype.one_lt_card
  let k := Fintype.orderIsoFinOfCardEq (base b) rfl
  have hEndpoint (e : C₀.Edge) (u w : base b) (hu : u < w) :
      C₀.order.lt (EP.endpoint e u) (EP.endpoint e w) := by
    by_contra hn
    have hle : C₀.order.le (EP.endpoint e w) (EP.endpoint e u) :=
      le_of_not_gt hn
    have h := C₀.part_mono _ _ hle
    change EP.part (EP.endpoint e w) ≤ EP.part (EP.endpoint e u) at h
    rw [EP.part_endpoint,EP.part_endpoint] at h
    exact (not_le_of_gt hu) h
  let A : ContactProfileTrain (base b) 1 (Fintype.card (base b))
      (fun j => Subtype.val ⁻¹' allowed j) (fun i => k i) := {
    Vertex := C₀.Vertex
    Edge := C₀.Edge
    Copy := C₀.Copy
    finiteV := C₀.finiteV
    finiteE := C₀.finiteE
    nonemptyE := C₀.nonemptyE
    graph := C₀.graph
    train := C₀.train
    order := C₀.order
    part := EP.part
    enumeration := fun e => OrderEmbedding.ofStrictMono
      (fun i => EP.endpoint e (k i)) (fun i j h => hEndpoint e _ _ (k.strictMono h))
    carrier_eq := by
      intro e
      rw [EP.carrier_eq]
      ext x
      constructor
      · rintro ⟨p,rfl⟩
        refine ⟨k.symm p,?_⟩
        change EP.endpoint e (k (k.symm p)) = EP.endpoint e p
        rw [k.apply_symm_apply]
      · rintro ⟨i,rfl⟩
        exact ⟨k i,rfl⟩
    part_eq := fun e i => EP.part_endpoint e (k i)
    part_mono := C₀.part_mono
    covered := EP.covered
    parameters := C₀.parameters }
  have hG : LabelledGirthGT A.graph.edgeCarrier m :=
    P.projection.strip_girth_of_qualitativeCompletion b hsize P.linear hP.2.1 hP.1 m hP.2.2
  obtain ⟨W,hW,hF,hI,hV,hE⟩ := contactProfileForestRamsey_covered ha A m hm hG Color
  let ep : ContactPartiteEndpoints W.out.graph (base b) := {
    part := W.out.part
    endpoint := fun e p => W.out.enumeration e (k.symm p)
    part_endpoint := by
      intro e p
      rw [W.out.part_eq]
      exact k.apply_symm_apply p
    carrier_eq := by
      intro e
      rw [W.out.carrier_eq]
      ext x
      constructor
      · rintro ⟨i,rfl⟩
        refine ⟨k i,?_⟩
        change W.out.enumeration e (k.symm (k i)) = W.out.enumeration e i
        rw [k.symm_apply_apply]
      · rintro ⟨p,rfl⟩
        exact ⟨k.symm p,rfl⟩
    covered := W.out.covered }
  let R : C₀.Witness Color := {
    out := {
      Vertex := W.out.Vertex
      Edge := W.out.Edge
      Copy := W.out.Copy
      finiteV := W.out.finiteV
      finiteE := W.out.finiteE
      nonemptyE := W.out.nonemptyE
      graph := W.out.graph
      train := W.out.train
      endpoints := ep
      order := W.out.order
      part_mono := W.out.part_mono
      linear := contact_pairwise_of_labelledGirth _ hm hW
      parameters := W.out.parameters
      positiveWagons := by intro μ hp ht; omega }
    finiteC := W.finiteC
    family := W.family
    emb_part := W.emb_part
    emb_order := W.emb_order
    positive := by intro μ hp ht; omega
    arrow := W.arrow }
  let C := P.coarseCore b hne R
  exact ⟨C,⟨hV,hE⟩,hF,W.arrow⟩

/-- Finite outer iteration preserving the actual one-point labels
and qualitative completion. Empty strips use the identity step. -/
theorem exists_outer_chain {Color : Type v} [Finite Color] [Nonempty Color]
    (m : ℕ) (hm : 2 ≤ m)
    (hbase : ∀ a b : B, a ≠ b → (base a ∩ base b).Subsingleton)
    (hsize : ∀ b, (base b).Nontrivial)
    {part : V → L} {label : X → L}
    (hP : P.OuterInvariant m) (hpart : P.PartPreserving part label)
    (l : List B) :
    ∃ Q : ContactTrainPicture D T base allowed q, Q.OuterInvariant m ∧
      Q.PartPreserving part label ∧ ContactFocusPicture.Chain Color P.focus Q.focus l := by
  classical
  let hq : ∀ μ : Fin 2, 0 < μ.val → μ.val < 1 → 2 ≤ q μ :=
    fun μ hp ht => (by omega : False).elim
  induction l with
  | nil => exact ⟨P,hP,hpart,ContactFocusPicture.Chain.nil _⟩
  | cons b l ih =>
    obtain ⟨Q,hQ,hpartQ,hchain⟩ := ih
    by_cases hne : Nonempty (Q.projection.StripEdge b)
    · obtain ⟨C,hCover,hF,hArrow⟩ := Q.outerCore_of_invariant (Color := Color) b hne m hm (hsize b) hQ
      exact ⟨C.next hne hbase hq,C.next_outerInvariant hne hbase hq m hm hQ hCover hF,
        C.next_partPreserving hne hbase hq hpartQ,
        ContactFocusPicture.Chain.snoc hchain (C.next_focus hne hbase hq hArrow)⟩
    · have hstep : ContactFocusPicture.Step Q.focus Q.focus b Color := by
        intro χ
        refine ⟨Function.Embedding.refl _,id,fun _ => rfl,fun _ _ => rfl,
          Classical.choice (inferInstance : Nonempty Color),?_⟩
        intro e he
        exact (hne ⟨⟨e,he⟩⟩).elim
      exact ⟨Q,hQ,hpartQ,ContactFocusPicture.Chain.snoc hchain hstep⟩

theorem outer_of_seed [Fintype B] {Color : Type v} [Finite Color] [Nonempty Color]
    (m : ℕ) (hm : 2 ≤ m)
    (hbase : ∀ a b : B, a ≠ b → (base a ∩ base b).Subsingleton)
    (hsize : ∀ b, (base b).Nontrivial)
    {part : V → L} {label : X → L}
    (hP : P.OuterInvariant m) (hpart : P.PartPreserving part label)
    (hArrow : ∀ ρ : B → Color, ∃ i : P.Copy, ∃ c : Color,
      ∀ e : E, ρ (P.projection.edge ((P.family.emb i).edge e)) = c) :
    ∃ Q : ContactTrainPicture D T base allowed q, Q.OuterInvariant m ∧
      Q.PartPreserving part label ∧ Q.family.Arrow Color := by
  classical
  let l := (Finset.univ : Finset B).toList
  obtain ⟨Q,hQ,hPart,hchain⟩ := P.exists_outer_chain (Color := Color) m hm
    hbase hsize hP hpart l
  refine ⟨Q,hQ,hPart,hchain.arrow_of_base ?_ hArrow⟩
  intro b
  simp [l]

end ContactTrainPicture
end StructuralRamsey.Girth
