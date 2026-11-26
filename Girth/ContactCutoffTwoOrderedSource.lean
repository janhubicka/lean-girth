import Girth.ContactCutoffTwoWord
import Girth.ContactOrderedFilling
import Girth.ContactRawSeed

/-! Ordered profile of the actual padded shorter input.
The local orders supplied by the padding theorem make every
template placement strictly increasing. The common disjoint
union is then ordered by original part, component rank and
local vertex rank. Its edges have the common template word,
even if a shared old vertex uses different template positions
in different padded edges. -/

namespace StructuralRamsey.Girth
universe v
variable {V E I X F J C P : Type v}

namespace ContactCutoffTwoInput
variable {m : ℕ} {D : ContactHypergraphData V E I}
    {T : ContactTrainData E (m+1)} {L : ContactHypergraphData X F J}
    (A : ContactCutoffTwoInput D T L C)

/-- The part of an original vertex in a padded component is
its original part, while a private vertex uses its template part. -/
def paddedPart (part : V → P) (templatePart : X → P)
    (c : C) : A.Component c → P
  | .inl x => part x
  | .inr z => templatePart z.2.val

def sourcePart (part : V → P) (templatePart : X → P) (x : A.Vertex) : P :=
  A.paddedPart part templatePart x.1 x.2

theorem paddedPart_place (part : V → P) (templatePart : X → P)
    (hpart : ∀ c p (u : (D.atCut (T.parent (0 : Fin (m+1)).succ)).contactWagonCarrier p),
      templatePart ((A.pad c).inside p u) = part u.val)
    (c : C) (p : T.FirstWagon) (x : X) :
    A.paddedPart part templatePart c ((A.pad c).place p x) = templatePart x := by
  classical
  by_cases hx : x ∈ Set.range ((A.pad c).inside p)
  · obtain ⟨u,rfl⟩ := hx
    change A.paddedPart part templatePart c ((A.pad c).placeFun p ((A.pad c).inside p u)) = _
    rw [(A.pad c).placeFun_old]
    exact (hpart c p u).symm
  · change A.paddedPart part templatePart c ((A.pad c).placeFun p x) = _
    rw [(A.pad c).placeFun_private p x hx]
    rfl

theorem sourcePart_place (part : V → P) (templatePart : X → P)
    (hpart : ∀ c p (u : (D.atCut (T.parent (0 : Fin (m+1)).succ)).contactWagonCarrier p),
      templatePart ((A.pad c).inside p u) = part u.val)
    (e : A.OldEdge) (x : X) :
    A.sourcePart part templatePart (A.fill.place e x) = templatePart x :=
  A.paddedPart_place part templatePart hpart e.1 e.2 x

theorem sourcePart_original (part : V → P) (templatePart : X → P)
    (c : C) (x : V) :
    A.sourcePart part templatePart ((A.original c).vertex x) = part x := rfl

/-- The data needed to apply the ordered shorter-train theorem.
The profile is encoded by an increasing enumeration of each
edge with the same part word. -/
structure OrderedSource [LinearOrder V] [LinearOrder X] [LinearOrder P]
    (part : V → P) (templatePart : X → P) where
  order : LinearOrder A.Vertex
  place_order : ∀ e x y, x < y → order.lt (A.fill.place e x) (A.fill.place e y)
  original_order : ∀ c x y, x < y → order.lt ((A.original c).vertex x) ((A.original c).vertex y)
  place_part : ∀ e x, A.sourcePart part templatePart (A.fill.place e x) = templatePart x
  original_part : ∀ c x, A.sourcePart part templatePart ((A.original c).vertex x) = part x
  part_order : ∀ x y, order.lt x y →
    A.sourcePart part templatePart x ≤ A.sourcePart part templatePart y

/-- Choose the local padded orders, and concatenate the
components inside each part. This gives one order on the
actual source of the recursive shorter-train call. -/
noncomputable def orderedSource [Fintype V] [Fintype X] [Finite E] [Fintype C]
    [LinearOrder V] [LinearOrder X] [LinearOrder P]
    (part : V → P) (templatePart : X → P)
    (hmonoV : Monotone part) (hmonoX : Monotone templatePart)
    (hpart : ∀ c p (u : (D.atCut (T.parent (0 : Fin (m+1)).succ)).contactWagonCarrier p),
      templatePart ((A.pad c).inside p u) = part u.val)
    (hord : ∀ c p, StrictMono ((A.pad c).inside p)) :
    A.OrderedSource part templatePart := by
  classical
  letI : Finite T.FirstWagon := Finite.of_surjective
    (T.parent (0 : Fin (m+1)).succ) (T.surj _)
  let ho (c : C) := (A.pad c).exists_padded_order (hord c)
  let o (c : C) : LinearOrder (A.Component c) := Classical.choose (ho c)
  letI : ∀ c : C, LinearOrder (A.Component c) := o
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
  letI : ∀ c : C, Fintype (A.Component c) := fun c => Fintype.ofFinite _
  let idx := Fintype.equivFin C
  let key (x : A.Vertex) : P ×ₗ (Fin (Fintype.card C) ×ₗ ℕ) :=
    toLex (A.sourcePart part templatePart x,
      toLex (idx x.1,contactOrderRank x.2))
  have hi : Function.Injective key := by
    intro x y he
    rcases x with ⟨i,x⟩
    rcases y with ⟨j,y⟩
    have he' : idx i = idx j := congrArg
      (fun z : P ×ₗ (Fin (Fintype.card C) ×ₗ ℕ) => (ofLex (ofLex z).2).1) he
    have hij := idx.injective he'
    subst j
    have hr : contactOrderRank x = contactOrderRank y := congrArg
      (fun z : P ×ₗ (Fin (Fintype.card C) ×ₗ ℕ) => (ofLex (ofLex z).2).2) he
    have hxy := (contactOrderRank_strict : StrictMono (contactOrderRank : A.Component i → ℕ)).injective hr
    subst y
    rfl
  let order : LinearOrder A.Vertex := LinearOrder.lift' key hi
  have hplace := A.sourcePart_place part templatePart hpart
  have hchoose := A.sourcePart_original part templatePart
  have hkey {i : C} {x y : A.Component i}
      (h₁ : A.paddedPart part templatePart i x ≤ A.paddedPart part templatePart i y)
      (h₂ : x < y) :
      key (⟨i,x⟩ : A.Vertex) < key (⟨i,y⟩ : A.Vertex) := by
    change (toLex (A.paddedPart part templatePart i x,
      toLex (idx i,contactOrderRank x)) : P ×ₗ (Fin (Fintype.card C) ×ₗ ℕ)) < _
    apply Prod.Lex.toLex_lt_toLex'.mpr
    refine ⟨h₁,fun _ => ?_⟩
    exact Prod.Lex.toLex_lt_toLex.mpr
      (Or.inr ⟨rfl,contactOrderRank_strict h₂⟩)
  refine {
    order := order
    place_order := ?_
    original_order := ?_
    place_part := hplace
    original_part := hchoose
    part_order := ?_ }
  · rintro ⟨c,p⟩ x y hxy
    change key ⟨c,(A.pad c).place p x⟩ < key ⟨c,(A.pad c).place p y⟩
    apply hkey
    · rw [A.paddedPart_place part templatePart hpart,A.paddedPart_place part templatePart hpart]
      exact hmonoX hxy.le
    · exact (Classical.choose_spec (ho c)).2 p x y hxy
  · intro c x y hxy
    change key ⟨c,(A.pad c).oldVertex x⟩ < key ⟨c,(A.pad c).oldVertex y⟩
    apply hkey
    · exact hmonoV hxy.le
    · exact (Classical.choose_spec (ho c)).1 x y hxy
  · intro x y hxy
    change key x < key y at hxy
    exact (Prod.Lex.toLex_lt_toLex'.mp hxy).1

/-- The ordered shorter input has a single edge word, namely the
template's part word. Its increasing enumeration is the actual
template placement composed with the finite enumeration of X. -/
noncomputable def OrderedSource.edgeWord [Fintype X]
    [LinearOrder V] [LinearOrder X] [LinearOrder P]
    {part : V → P} {templatePart : X → P}
    (O : A.OrderedSource part templatePart) :
    letI : LinearOrder A.Vertex := O.order
    ContactOrderedEdgeWord A.source P (Fintype.card X) := by
  letI : LinearOrder A.Vertex := O.order
  let q := Fintype.orderIsoFinOfCardEq X rfl
  exact {
    part := A.sourcePart part templatePart
    word := fun i => templatePart (q i)
    enumeration := fun e => OrderEmbedding.ofStrictMono
      (fun i => A.fill.place e (q i))
      (fun i j h => O.place_order e _ _ (q.strictMono h))
    carrier_eq := by
      intro e
      rw [← A.fill.range_eq e]
      ext x
      constructor
      · rintro ⟨y,rfl⟩
        exact ⟨q.symm y,congrArg (A.fill.place e) (q.apply_symm_apply y)⟩
      · rintro ⟨i,rfl⟩
        exact ⟨q i,rfl⟩
    part_eq := fun e i => O.place_part e (q i) }

end ContactCutoffTwoInput
end StructuralRamsey.Girth
