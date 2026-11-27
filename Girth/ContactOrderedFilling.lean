import Girth.ContactGluedOrder
import Girth.ContactWagonPadding
import Girth.ContactTrainEmbedding
import Mathlib.Data.Finset.Sort
import Mathlib.Order.WellFounded

/-! The two order obligations of canonical substitution. Padded
wagon carriers have simultaneous compatible orders, obtained by
identifying the padding with an ordinary tagged free union.
The unique increasing placements on edges commute with ordered
embeddings because they have the same range. -/

namespace StructuralRamsey.Girth
universe v
variable {V P X : Type v}

namespace ContactWagonPadding
variable {K : P → Set V} (A : ContactWagonPadding K X)

noncomputable def orderGlue (p : P) (x : X) : Option V := by
  classical
  exact if h : x ∈ Set.range (A.inside p) then
    some (Classical.choose h).val else none

theorem orderGlue_some (p : P) (x : X) (v : V) :
    A.orderGlue p x = some v ↔ ∃ u : K p, A.inside p u = x ∧ u.val = v := by
  classical
  unfold orderGlue
  split_ifs with h
  · constructor
    · intro he
      exact ⟨Classical.choose h,Classical.choose_spec h,Option.some.inj he⟩
    · rintro ⟨u,hu,hv⟩
      exact congrArg some ((congrArg Subtype.val
        ((A.inside p).injective ((Classical.choose_spec h).trans hu.symm))).trans hv)
  · constructor
    · intro he
      cases he
    · rintro ⟨u,hu,_⟩
      exact (h ⟨u,hu⟩).elim

theorem orderGlue_inj (p : P) (x y : X) (v : V)
    (hx : A.orderGlue p x = some v) (hy : A.orderGlue p y = some v) : x = y := by
  obtain ⟨u,hu,hu'⟩ := (A.orderGlue_some p x v).mp hx
  obtain ⟨w,hw,hw'⟩ := (A.orderGlue_some p y v).mp hy
  exact hu.symm.trans ((congrArg (A.inside p) (Subtype.ext (hu'.trans hw'.symm))).trans hw)

theorem orderGlue_old (p : P) (u : K p) :
    A.orderGlue p (A.inside p u) = some u.val :=
  (A.orderGlue_some p (A.inside p u) u.val).mpr ⟨u,rfl,rfl⟩

theorem orderGlue_private (p : P) (x : X) (h : x ∉ Set.range (A.inside p)) :
    A.orderGlue p x = none := by
  classical
  unfold orderGlue
  rw [dif_neg h]

/-- The original padding type embeds into the generated tagged
free union, retaining its actual original and private vertices. -/
noncomputable def paddedTag : A.Vertex → ContactGlued A.orderGlue
  | .inl u => contactCoreEmb A.orderGlue u
  | .inr ⟨p,⟨x,h⟩⟩ =>
      ⟨Sum.inr (p,x),by
        have he := gluedStandardNode_generated A.orderGlue p x
        simpa only [gluedStandardNode,A.orderGlue_private p x h] using he⟩

theorem paddedTag_inj : Function.Injective A.paddedTag := by
  intro a b he
  cases a with
  | inl u =>
    cases b with
    | inl w => exact congrArg Sum.inl ((contactCoreEmb A.orderGlue).injective he)
    | inr w =>
      rcases w with ⟨p,⟨x,h⟩⟩
      have hh := congrArg Subtype.val he
      change (Sum.inl u : V ⊕ (P × X)) = Sum.inr (p,x) at hh
      cases hh
  | inr u =>
    rcases u with ⟨p,⟨x,hx⟩⟩
    cases b with
    | inl w =>
      have hh := congrArg Subtype.val he
      change (Sum.inr (p,x) : V ⊕ (P × X)) = Sum.inl w at hh
      cases hh
    | inr w =>
      rcases w with ⟨r,⟨y,hy⟩⟩
      have hh := congrArg Subtype.val he
      change (Sum.inr (p,x) : V ⊕ (P × X)) = Sum.inr (r,y) at hh
      have hp : p = r := congrArg Prod.fst (Sum.inr.inj hh)
      have hxy : x = y := congrArg Prod.snd (Sum.inr.inj hh)
      subst r
      subst y
      rfl

theorem paddedTag_place (p : P) (x : X) :
    A.paddedTag (A.place p x) = contactStandardEmb A.orderGlue A.orderGlue_inj p x := by
  classical
  change A.paddedTag (A.placeFun p x) = _
  by_cases h : x ∈ Set.range (A.inside p)
  · obtain ⟨u,rfl⟩ := h
    rw [A.placeFun_old]
    exact ((contactStandardEmb_eq_core A.orderGlue A.orderGlue_inj p
      (A.inside p u) u.val).mpr (A.orderGlue_old p u)).symm
  · rw [A.placeFun_private p x h]
    apply Subtype.ext
    change Sum.inr (p,x) = gluedStandardNode A.orderGlue p x
    rw [gluedStandardNode,A.orderGlue_private p x h]

/-- If the embeddings of the old first wagons into the template
preserve their induced order, all padded edges admit their
template order simultaneously. The order on original vertices
is retained. -/
theorem exists_padded_order [Fintype V] [Fintype X] [Finite P]
    [LinearOrder V] [LinearOrder X]
    (hord : ∀ p : P, StrictMono (A.inside p)) :
    ∃ o : LinearOrder A.Vertex,
      (∀ x y : V, x < y → o.lt (A.oldVertex x) (A.oldVertex y)) ∧
      (∀ p (x y : X), x < y → o.lt (A.place p x) (A.place p y)) := by
  have hc : ContactGluedOrder.Compatible A.orderGlue := by
    intro p x y u w hx hy hxy
    obtain ⟨a,ha,ha'⟩ := (A.orderGlue_some p x u).mp hx
    obtain ⟨b,hb,hb'⟩ := (A.orderGlue_some p y w).mp hy
    rw [← ha,← hb] at hxy
    have hlt : a < b := (hord p).lt_iff_lt.mp hxy
    exact ha' ▸ hb' ▸ (show a.val < b.val from hlt)
  obtain ⟨o,hcore,hstd⟩ := ContactGluedOrder.exists_order A.orderGlue hc A.orderGlue_inj
  letI : LinearOrder (ContactGlued A.orderGlue) := o
  let op : LinearOrder A.Vertex := LinearOrder.lift' A.paddedTag A.paddedTag_inj
  refine ⟨op,?_,?_⟩
  · intro x y h
    exact hcore x y h
  · intro p x y h
    change A.paddedTag (A.place p x) < A.paddedTag (A.place p y)
    rw [A.paddedTag_place,A.paddedTag_place]
    exact hstd p x y h

end ContactWagonPadding

namespace ContactFilling
variable {E I F J : Type v}
    {D : ContactHypergraphData V E I} {L : ContactHypergraphData X F J}
    [LinearOrder V] [LinearOrder X]

/-- The canonical increasing placement of a finite ordered
template on an edge of the same size. -/
noncomputable def orderedPlacement [Fintype X] [Finite V]
    (e : E) (hcard : Nat.card (D.edgeCarrier e) = Fintype.card X) : X ↪o V := by
  letI : Fintype (D.edgeCarrier e) := Fintype.ofFinite _
  let h : Fintype.card (D.edgeCarrier e) = Fintype.card X := by
    rw [← Nat.card_eq_fintype_card]
    exact hcard
  exact ((Fintype.orderIsoFinOfCardEq X rfl).symm.toOrderEmbedding.trans
    (Fintype.orderIsoFinOfCardEq (D.edgeCarrier e) h).toOrderEmbedding).trans
      (OrderEmbedding.subtype _)

theorem orderedPlacement_range [Fintype X] [Finite V]
    (e : E) (hcard : Nat.card (D.edgeCarrier e) = Fintype.card X) :
    Set.range (orderedPlacement (D := D) (X := X) e hcard) = D.edgeCarrier e := by
  classical
  letI : Fintype (D.edgeCarrier e) := Fintype.ofFinite _
  let h : Fintype.card (D.edgeCarrier e) = Fintype.card X := by
    rw [← Nat.card_eq_fintype_card]
    exact hcard
  let q := (Fintype.orderIsoFinOfCardEq X rfl).symm.trans
    (Fintype.orderIsoFinOfCardEq (D.edgeCarrier e) h)
  ext v
  constructor
  · rintro ⟨x,rfl⟩
    exact (q x).property
  · intro hv
    refine ⟨q.symm ⟨v,hv⟩,?_⟩
    exact congrArg Subtype.val (q.apply_symm_apply ⟨v,hv⟩)

noncomputable def ordered [Fintype X] [Finite V]
    (hcard : ∀ e, Nat.card (D.edgeCarrier e) = Fintype.card X)
    (hcover : ∀ x, ∃ f, x ∈ L.edgeCarrier f) (hne : Nonempty F) :
    ContactFilling D L where
  place := fun e => (orderedPlacement (D := D) (X := X) e (hcard e)).toEmbedding
  range_eq := fun e => orderedPlacement_range (D := D) (X := X) e (hcard e)
  template_cover := hcover
  template_nonempty := hne

theorem ordered_strictMono [Fintype X] [Finite V]
    (hcard : ∀ e, Nat.card (D.edgeCarrier e) = Fintype.card X)
    (hcover : ∀ x, ∃ f, x ∈ L.edgeCarrier f) (hne : Nonempty F)
    (e : E) : StrictMono ((ordered (D := D) (L := L) hcard hcover hne).place e) :=
  (orderedPlacement (D := D) (X := X) e (hcard e)).strictMono

end ContactFilling

namespace ContactTrainEmbedding
variable {E I U F J L K : Type v}
    {m : ℕ} {D : ContactHypergraphData V E I} {T : ContactTrainData E m}
    {H : ContactHypergraphData U F J} {S : ContactTrainData F m}
    {Z : ContactHypergraphData X L K}
    (M : ContactTrainEmbedding D T H S)
    [LinearOrder V] [LinearOrder U] [LinearOrder X] [WellFoundedLT X]

/-- No placement-compatibility hypothesis is required once the
two placements and the embedding preserve the finite orders. -/
theorem ordered_placement_compatible
    (A : ContactFilling D Z) (B : ContactFilling H Z)
    (hM : StrictMono M.vertex)
    (hA : ∀ e, StrictMono (A.place e))
    (hB : ∀ f, StrictMono (B.place f))
    (e : E) (x : X) :
    B.place (M.edge e) x = M.vertex (A.place e x) := by
  have hmono : StrictMono (fun x => M.vertex (A.place e x)) := hM.comp (hA e)
  have hrange : Set.range (B.place (M.edge e)) =
      Set.range (fun x => M.vertex (A.place e x)) := by
    rw [B.range_eq,M.carrier_eq,← A.range_eq]
    ext y
    constructor
    · rintro ⟨u,⟨z,rfl⟩,rfl⟩
      exact ⟨z,rfl⟩
    · rintro ⟨z,rfl⟩
      exact ⟨A.place e z,⟨z,rfl⟩,rfl⟩
  exact congrFun ((hB (M.edge e)).range_inj_of_wellFoundedLT hmono |>.mp hrange) x

end ContactTrainEmbedding
end StructuralRamsey.Girth
