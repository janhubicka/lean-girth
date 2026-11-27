import Girth.ContactSeedAssembly

/-! Retain original part labels through the actual picture iterations.

The ordinary picture state has its own base projection; that alone does
not express preservation of a chosen earlier part map by every member of
the designated family. This invariant is proved for the actual gluing
and then carried through both finite iterations. -/

namespace StructuralRamsey.Girth
universe v
variable {V E I X B L : Type v} {m : ℕ}
variable {D : ContactHypergraphData V E I} {T : ContactTrainData E m}
variable {base : B → Set X} [LinearOrder V] [LinearOrder X]

namespace ContactTrainPicture
variable {allowed : Fin m → Set X} {q : Fin (m+1) → ℕ}
    (P : ContactTrainPicture D T base allowed q)

/-- Every actual designated embedding preserves the original part map,
when the current projection is followed by the fixed base labelling. -/
def PartPreserving (part : V → L) (label : X → L) : Prop :=
  ∀ i x, label (P.projection.vertex ((P.family.emb i).vertex x)) = part x

namespace Core
variable {P} {b : B} (C : P.Core b)
    (hne : Nonempty (P.projection.StripEdge b))

 theorem next_partPreserving
    (hbase : ∀ a b : B, a ≠ b → (base a ∩ base b).Subsingleton)
    (hq : ∀ μ, 0 < μ.val → μ.val < m → 2 ≤ q μ)
    {part : V → L} {label : X → L} (hP : P.PartPreserving part label) :
    (C.next hne hbase hq).PartPreserving part label := by
  rintro ⟨i,j⟩ x
  change label ((C.gluing hne).outputProjectionVertex P.projection C.part
    ((C.gluing hne).stdV i ((P.family.emb j).vertex x))) = part x
  rw [(C.gluing hne).projection_vertex_std P.projection b C.part
    (C.family.stripGluing_coreOver hne C.part C.part_emb C.edge_image C.edge_inj)]
  exact hP j x

end Core

/-- Main iteration with a concrete original-part invariant. The old
supply only has to construct the core and the other recursive invariant.
Part preservation is a consequence of the actual gluing. -/
theorem main_preservesPart [Fintype B] {Color : Type v} [Nonempty Color]
    (hm : 0 < m)
    (hbase : ∀ a b : B, a ≠ b → (base a ∩ base b).Subsingleton)
    (hq : ∀ μ, μ.val < m → 2 ≤ q μ)
    (Inv : ContactTrainPicture D T base allowed q → List B → Prop)
    (hskip : ∀ Q done b, Inv Q done → Inv Q (b :: done))
    (supply : MainCoreSupply hbase hq Inv Color)
    {part : V → L} {label : X → L}
    (hP : P.FullBounds) (hInv : Inv P []) (hpart : P.PartPreserving part label)
    (hArrow : ∀ ρ : B → Color, ∃ i : P.Copy, ∃ c : Color,
      ∀ e : E, ρ (P.projection.edge ((P.family.emb i).edge e)) = c) :
    ∃ Q : ContactTrainPicture D T base allowed q,
      Q.FullBounds ∧ Q.PartPreserving part label ∧ Q.family.Arrow Color := by
  classical
  let Inv' (Q : ContactTrainPicture D T base allowed q) (done : List B) : Prop :=
    Inv Q done ∧ Q.PartPreserving part label
  have hskip' : ∀ Q done b, Inv' Q done → Inv' Q (b :: done) :=
    fun Q done b h => ⟨hskip Q done b h.1,h.2⟩
  have hsup : MainCoreSupply hbase hq Inv' Color := by
    intro Q done b hQ hI hb hn
    obtain ⟨C,hC,hsize,hA,hNext⟩ := supply Q done b hQ hI.1 hb hn
    exact ⟨C,hC,hsize,hA,hNext,
      C.next_partPreserving hn hbase (fun μ _ hh => hq μ hh) hI.2⟩
  let l := (Finset.univ : Finset B).toList
  have hl : l.Nodup := Finset.nodup_toList _
  obtain ⟨Q,hQ,hI,hchain⟩ := P.exists_main_chain hm hbase hq Inv' hskip' hsup
    hP ⟨hInv,hpart⟩ l hl
  refine ⟨Q,hQ,hI.2,hchain.arrow_of_base ?_ hArrow⟩
  intro b
  simp [l]

/-- The finite forest-boost chain also retains every original part label.
No class-wide or recursive existence statement is assumed by this lemma
beyond the already isolated smaller-bound core supply. -/
theorem exists_boost_chain_preservesPart {Color : Type v} [Nonempty Color] {j : ℕ}
    (hj : 2 ≤ j)
    (hbase : ∀ a b : B, a ≠ b → (base a ∩ base b).Subsingleton)
    (hq : ∀ μ, 0 < μ.val → μ.val < m → 2 ≤ q μ)
    (supply : BoostCoreSupply (D := D) (T := T) (base := base)
      (allowed := allowed) (q := q) j Color)
    {part : V → L} {label : X → L}
    (hP : P.Forests j) (hpart : P.PartPreserving part label) (l : List B) :
    ∃ Q : ContactTrainPicture D T base allowed q,
      Q.Forests j ∧ Q.PartPreserving part label ∧
      ContactFocusPicture.Chain Color P.focus Q.focus l := by
  classical
  induction l with
  | nil => exact ⟨P,hP,hpart,ContactFocusPicture.Chain.nil _⟩
  | cons b l ih =>
    obtain ⟨Q,hQ,hpartQ,hchain⟩ := ih
    by_cases hne : Nonempty (Q.projection.StripEdge b)
    · obtain ⟨C,hC,hg,hArrow⟩ := supply Q hQ b hne
      exact ⟨C.next hne hbase hq,C.next_forests hne hbase hq hj hQ hC hg,
        C.next_partPreserving hne hbase hq hpartQ,
        ContactFocusPicture.Chain.snoc hchain (C.next_focus hne hbase hq hArrow)⟩
    · have hstep : ContactFocusPicture.Step Q.focus Q.focus b Color := by
        intro χ
        refine ⟨Function.Embedding.refl _,id,fun _ => rfl,fun _ _ => rfl,
          Classical.choice (inferInstance : Nonempty Color),?_⟩
        intro e he
        exact (hne ⟨⟨e,he⟩⟩).elim
      exact ⟨Q,hQ,hpartQ,ContactFocusPicture.Chain.snoc hchain hstep⟩

 theorem boost_preservesPart [Fintype B] {Color : Type v} [Nonempty Color] {j : ℕ}
    (hj : 2 ≤ j)
    (hbase : ∀ a b : B, a ≠ b → (base a ∩ base b).Subsingleton)
    (hq : ∀ μ, 0 < μ.val → μ.val < m → 2 ≤ q μ)
    (supply : BoostCoreSupply (D := D) (T := T) (base := base)
      (allowed := allowed) (q := q) j Color)
    {part : V → L} {label : X → L}
    (hP : P.Forests j) (hpart : P.PartPreserving part label)
    (hArrow : ∀ ρ : B → Color, ∃ i : P.Copy, ∃ c : Color,
      ∀ e : E, ρ (P.projection.edge ((P.family.emb i).edge e)) = c) :
    ∃ Q : ContactTrainPicture D T base allowed q,
      Q.Forests j ∧ Q.PartPreserving part label ∧ Q.family.Arrow Color := by
  classical
  let l := (Finset.univ : Finset B).toList
  obtain ⟨Q,hQ,hpartQ,hchain⟩ := P.exists_boost_chain_preservesPart hj hbase hq supply hP hpart l
  refine ⟨Q,hQ,hpartQ,hchain.arrow_of_base ?_ hArrow⟩
  intro b
  simp [l]

section FinalOrder
variable [LinearOrder L]

/-- Reorder by original part, preserving the picture order within each
part. The result need not use the same order as the seed projection. -/
noncomputable def originalPartOrder (label : X → L) : LinearOrder P.Vertex :=
  ContactOrderedSeedStage.concatenate P.order (label ∘ P.projection.vertex)

/-- If the original target order is concatenated by parts, sorting the
output by original parts preserves the order of every designated copy. -/
theorem originalPartOrder_copy_order {part : V → L} {label : X → L}
    (hpart : P.PartPreserving part label) (hmono : Monotone part)
    (i : P.Copy) (x y : V) (hxy : x < y) :
    (P.originalPartOrder label).lt ((P.family.emb i).vertex x) ((P.family.emb i).vertex y) := by
  have hp : part x ≤ part y := hmono hxy.le
  rcases lt_or_eq_of_le hp with hlt | he
  · apply ContactOrderedSeedStage.concatenate_part
    change label (P.projection.vertex ((P.family.emb i).vertex x)) <
      label (P.projection.vertex ((P.family.emb i).vertex y))
    rw [hpart i x,hpart i y]
    exact hlt
  · apply ContactOrderedSeedStage.concatenate_within
    · change label (P.projection.vertex ((P.family.emb i).vertex x)) =
        label (P.projection.vertex ((P.family.emb i).vertex y))
      rw [hpart i x,hpart i y]
      exact he
    · exact P.copy_order i x y hxy

/-- The increasing edge enumeration also survives sorting by the original
part, provided the common part word is nondecreasing. -/
theorem originalPartOrder_edge_order (label : X → L) {a : ℕ}
    (word : Fin a → L) (enumeration : B → Fin a ↪o X)
    (he : ∀ b, base b = Set.range (enumeration b))
    (hw : ∀ b i, label (enumeration b i) = word i) (hmono : Monotone word)
    (e : P.Edge) :
    letI : LinearOrder P.Vertex := P.order
    ∀ i j : Fin a, i < j → (P.originalPartOrder label).lt
      (P.liftEnumeration enumeration he e i) (P.liftEnumeration enumeration he e j) := by
  letI : LinearOrder P.Vertex := P.order
  intro i j hij
  have hpi : label (P.projection.vertex (P.liftEnumeration enumeration he e i)) = word i := by
    rw [(P.liftEnumeration_spec enumeration he e i).2]
    exact hw _ _
  have hpj : label (P.projection.vertex (P.liftEnumeration enumeration he e j)) = word j := by
    rw [(P.liftEnumeration_spec enumeration he e j).2]
    exact hw _ _
  rcases lt_or_eq_of_le (hmono hij.le) with hlt | heq
  · apply ContactOrderedSeedStage.concatenate_part
    change label (P.projection.vertex (P.liftEnumeration enumeration he e i)) <
      label (P.projection.vertex (P.liftEnumeration enumeration he e j))
    rw [hpi,hpj]
    exact hlt
  · apply ContactOrderedSeedStage.concatenate_within
    · change label (P.projection.vertex (P.liftEnumeration enumeration he e i)) =
        label (P.projection.vertex (P.liftEnumeration enumeration he e j))
      rw [hpi,hpj]
      exact heq
    · exact (P.liftEnumeration enumeration he e).strictMono hij

end FinalOrder
end ContactTrainPicture

namespace ContactOrderedEdgeWord.LinearSeedResult
variable [LinearOrder L] {a : ℕ} {A : ContactOrderedEdgeWord D L a} {Color : Type v}
    (S : A.LinearSeedResult Color)
    (allowed : Fin m → Set L) (q : Fin (m+1) → ℕ)

 theorem trainPicture_partPreserving [Finite V] [Finite E] (hm : 0 < m)
    (hcovered : ∀ x, ∃ e, x ∈ D.edgeCarrier e)
    (hlin : ∀ μ, μ.val < m → (D.atCut (T.parent μ)).ContactLinear)
    (hg : D.WagonBounds T q)
    (hp : D.Parameters T (fun j => A.part ⁻¹' allowed j)) :
    letI : LinearOrder S.Vertex := S.order
    (S.trainPicture T allowed q hm hcovered hlin hg hp).PartPreserving A.part S.part := by
  letI : LinearOrder S.Vertex := S.order
  exact S.emb_part

end ContactOrderedEdgeWord.LinearSeedResult
end StructuralRamsey.Girth
