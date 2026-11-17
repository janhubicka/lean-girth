import Mathlib.Data.Finset.Max
import Mathlib.Order.Prod.Lex.Basic
import PartiteConstruction.Partite.Attachment

set_option autoImplicit false

namespace StructuralRamsey.RelStructure.Attachment

universe u v w z
variable {L : RelLanguage.{u}} {X : Type v} {Y : Type w} {I : Type z}

/-- The orders of the core and attached copies have a common extension.
Each private vertex is put immediately before its first upper boundary vertex
in the core, or after the entire core if it has no upper boundary vertex.
Applying this to the intersection with each part gives the within-part orders. -/
theorem exists_linearOrder_attachment
    [LinearOrder X] [LinearOrder Y] [LinearOrder I] [Finite X]
    (B : RelStructure L X) (S : Set X) (D : RelStructure L Y)
    (f : I → Embedding (B.induce S) D)
    (hf : ∀ i, StrictMono (f i)) :
    ∃ o : LinearOrder (Vertex S (W := Y) (I := I)),
      @StrictMono Y _ inferInstance o.toPartialOrder.toPreorder Sum.inl ∧
        ∀ i, @StrictMono X _ inferInstance o.toPartialOrder.toPreorder
          (copyMap B S D f i) := by
  classical
  let : Fintype S := Fintype.ofFinite S
  let upper (i : I) (x : X) : Finset Y :=
    (Finset.univ.filter (fun s : S => x ≤ s.val)).image (f i)
  let rank (i : I) (x : X) : WithTop Y := (upper i x).min
  have rankMono (i : I) : Monotone (rank i) := by
    intro x y h
    apply Finset.le_min
    intro a ha
    apply Finset.min_le
    rcases Finset.mem_image.mp ha with ⟨s, hs, rfl⟩
    exact Finset.mem_image.mpr
      ⟨s, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h.trans (Finset.mem_filter.mp hs).2⟩, rfl⟩
  have rankAt (i : I) (x : X) (hx : x ∈ S) :
      rank i x = (f i ⟨x, hx⟩ : Y) := by
    apply le_antisymm
    · apply Finset.min_le
      exact Finset.mem_image.mpr
        ⟨⟨x, hx⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_rfl⟩, rfl⟩
    · apply Finset.le_min
      intro a ha
      rcases Finset.mem_image.mp ha with ⟨s, hs, rfl⟩
      exact WithTop.coe_le_coe.mpr ((hf i).monotone (Finset.mem_filter.mp hs).2)
  have ltRank (i : I) (x y : X) (hx : x ∈ S) (hxy : x < y) :
      (f i ⟨x, hx⟩ : WithTop Y) < rank i y := by
    cases h : rank i y with
    | top => exact WithTop.coe_lt_top _
    | coe a =>
      have ha : a ∈ upper i y := Finset.mem_of_min h
      rcases Finset.mem_image.mp ha with ⟨s, hs, rfl⟩
      exact WithTop.coe_lt_coe.mpr ((hf i) (hxy.trans_le (Finset.mem_filter.mp hs).2))
  let key : Vertex S (W := Y) (I := I) → WithTop Y ×ₗ WithTop (I ×ₗ X)
    | .inl a => toLex (a, ⊤)
    | .inr (i, x) => toLex (rank i x, (toLex (i, x.val) : I ×ₗ X))
  have keyInj : Function.Injective key := by
    rintro (a | ⟨i, x⟩) (b | ⟨j, y⟩) h
    · simpa [key] using congrArg (fun p => (ofLex p).1) h
    · simpa [key] using congrArg (fun p => (ofLex p).2) h
    · simpa [key] using congrArg (fun p => (ofLex p).2) h
    · have hprivate := congrArg (fun p => (ofLex p).2) h
      simp only [key, ofLex_toLex, WithTop.coe_inj, toLex_inj, Prod.mk.injEq] at hprivate
      obtain ⟨rfl, hxy⟩ := hprivate
      cases Subtype.ext hxy
      rfl
  let o : LinearOrder (Vertex S (W := Y) (I := I)) := LinearOrder.lift' key keyInj
  refine ⟨o, ?_, ?_⟩
  · intro a b hab
    change key (.inl a) < key (.inl b)
    exact Prod.Lex.toLex_lt_toLex.mpr (Or.inl (WithTop.coe_lt_coe.mpr hab))
  · intro i x y hxy
    change key (copyMap B S D f i x) < key (copyMap B S D f i y)
    by_cases hx : x ∈ S <;> by_cases hy : y ∈ S
    · rw [copyMap_mem i x hx, copyMap_mem i y hy]
      exact Prod.Lex.toLex_lt_toLex.mpr
        (Or.inl (WithTop.coe_lt_coe.mpr ((hf i) hxy)))
    · rw [copyMap_mem i x hx, copyMap_not_mem i y hy]
      exact Prod.Lex.toLex_lt_toLex.mpr (Or.inl (ltRank i x y hx hxy))
    · rw [copyMap_not_mem i x hx, copyMap_mem i y hy]
      apply Prod.Lex.toLex_lt_toLex'.mpr
      refine ⟨?_, fun _ => WithTop.coe_lt_top _⟩
      exact (rankMono i hxy.le).trans_eq (rankAt i y hy)
    · rw [copyMap_not_mem i x hx, copyMap_not_mem i y hy]
      apply Prod.Lex.toLex_lt_toLex'.mpr
      refine ⟨rankMono i hxy.le, fun _ => WithTop.coe_lt_coe.mpr ?_⟩
      exact Prod.Lex.toLex_lt_toLex.mpr (Or.inr ⟨rfl, hxy⟩)

end StructuralRamsey.RelStructure.Attachment

namespace StructuralRamsey.Partite.Attachment

universe u v w z t
variable {L : RelLanguage.{u}} {P : Type v} {X : Type w} {Y : Type z} {I : Type t}

/-- The within-part orders of a partite picture and local witness extend to
their attachment. In the extension the parts are ordered as prescribed by
`P`, independently of the chosen within-part orders. -/
theorem exists_linearOrder_partiteAttachment
    [ordP : LinearOrder P] [ordX : LinearOrder X] [ordY : LinearOrder Y]
    [LinearOrder I] [Finite X]
    (B : System L P X) (S : Set X) (D : System L P Y)
    (f : I → Embedding (B.induce S) D)
    (hf : ∀ i (x y : S), B.part x = B.part y → x.val < y.val → f i x < f i y) :
    ∃ o : LinearOrder (Vertex S (W := Y) (I := I)),
      (∀ x y : Y, D.part x = D.part y → x < y →
        @LT.lt _ o.toLT (coreEmbedding B S D f x) (coreEmbedding B S D f y)) ∧
      (∀ i (x y : X), B.part x = B.part y → x < y →
        @LT.lt _ o.toLT (copyEmbedding B S D f i x) (copyEmbedding B S D f i y)) ∧
      (∀ x y, part B S D x < part B S D y → @LT.lt _ o.toLT x y) := by
  let sourceKey (x : X) : P ×ₗ X := toLex (B.part x, x)
  let coreKey (y : Y) : P ×ₗ Y := toLex (D.part y, y)
  let sourceOrder : LinearOrder X :=
    LinearOrder.lift' sourceKey (fun _ _ h => congrArg (fun k => (ofLex k).2) h)
  let coreOrder : LinearOrder Y :=
    LinearOrder.lift' coreKey (fun _ _ h => congrArg (fun k => (ofLex k).2) h)
  have sourceLt (x y : X) :
      @LT.lt _ sourceOrder.toLT x y ↔
        B.part x < B.part y ∨ B.part x = B.part y ∧ @LT.lt _ ordX.toLT x y :=
    @Prod.Lex.toLex_lt_toLex P X ordP.toLT ordX.toLT _ _
  have coreLt (x y : Y) :
      @LT.lt _ coreOrder.toLT x y ↔
        D.part x < D.part y ∨ D.part x = D.part y ∧ @LT.lt _ ordY.toLT x y :=
    @Prod.Lex.toLex_lt_toLex P Y ordP.toLT ordY.toLT _ _
  have hf' (i : I) :
      @StrictMono S Y (sourceOrder.toPartialOrder.toPreorder.lift Subtype.val)
        coreOrder.toPartialOrder.toPreorder (f i) := by
    intro x y h
    apply (coreLt (f i x) (f i y)).mpr
    have hpart (s : S) : D.part (f i s) = B.part s := (f i).map_part s
    rcases (sourceLt x y).mp h with hlt | ⟨hp, hxy⟩
    · exact Or.inl (by simpa only [hpart] using hlt)
    · exact Or.inr ⟨by simpa only [hpart] using hp, hf i x y hp hxy⟩
  obtain ⟨o, hcore, hcopy⟩ :=
    @RelStructure.Attachment.exists_linearOrder_attachment L X Y I
      sourceOrder coreOrder _ _ B.toRelStructure S D.toRelStructure
      (fun i => (f i).toEmbedding) hf'
  let V := Vertex S (W := Y) (I := I)
  let : LinearOrder V := o
  let key (x : V) : P ×ₗ V := toLex (part B S D x, x)
  let ord : LinearOrder V :=
    LinearOrder.lift' key (fun _ _ h => congrArg (fun k => (ofLex k).2) h)
  have outputLt (x y : V) :
      @LT.lt _ ord.toLT x y ↔
        part B S D x < part B S D y ∨
          part B S D x = part B S D y ∧ @LT.lt _ o.toLT x y :=
    @Prod.Lex.toLex_lt_toLex P V ordP.toLT o.toLT _ _
  refine ⟨ord, ?_, ?_, ?_⟩
  · intro x y hp hxy
    exact (outputLt _ _).mpr (Or.inr ⟨hp, hcore ((coreLt x y).mpr (Or.inr ⟨hp, hxy⟩))⟩)
  · intro i x y hp hxy
    have hpart (a : X) : part B S D (copyEmbedding B S D f i a) = B.part a :=
      part_copyMap B S D f i a
    exact (outputLt _ _).mpr
      (Or.inr ⟨(hpart x).trans (hp.trans (hpart y).symm),
        hcopy i ((sourceLt x y).mpr (Or.inr ⟨hp, hxy⟩))⟩)
  · intro x y hxy
    exact (outputLt x y).mpr (Or.inl hxy)

end StructuralRamsey.Partite.Attachment
