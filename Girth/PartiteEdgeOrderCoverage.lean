import Girth.HypergraphClique
import Girth.PartiteEdgeOrder
import PartiteConstruction.Partite.Induced

set_option autoImplicit false

namespace StructuralRamsey.Partite

open StructuralRamsey.Girth StructuralRamsey.RelStructure

universe u v

variable {L : RelLanguage.{u}} {U P X : Type v}
variable [LinearOrder U] [LinearOrder P]

/-- All pairs in a copy of a linearly ordered source are compared in the
ambient relational language, even when the ambient order is only partial. -/
theorem irreducible_of_pairCovered_orderedCopies
    (A : RelStructure L U) (R : RelStructure L.withOrder X) (S : Set X)
    (hS : PairCoveredBy (supportCopies A.ordered R) S) :
    (R.induce S).Irreducible := by
  intro x y hxy
  have hNe : x.1 ≠ y.1 := fun h => hxy (Subtype.ext h)
  obtain ⟨_, ⟨a, rfl⟩, ⟨i, hi⟩, ⟨j, hj⟩⟩ := hS x.2 y.2 hNe
  have hij : i ≠ j := fun h => hNe (hi.symm.trans ((congrArg a h).trans hj))
  have transfer {b c : U} {p q : S} (hb : a b = p.1) (hc : a c = q.1) (hl : b < c) :
      (R.induce S).rel (.inr ()) ![p, q] := by
    have hz : R.rel (.inr ()) (a ∘ ![b, c]) := (a.map_rel_iff (.inr ()) ![b, c]).mpr hl
    have hEq : a ∘ ![b, c] = (Subtype.val : S → X) ∘ ![p, q] := by
      funext k
      fin_cases k
      · exact hb
      · exact hc
    change R.rel (.inr ()) ((Subtype.val : S → X) ∘ ![p, q])
    exact hEq ▸ hz
  rcases lt_or_gt_of_ne hij with h | h
  · exact ⟨.inr (), ![x, y], (0 : Fin 2), (1 : Fin 2), transfer hi hj h, rfl, rfl⟩
  · exact ⟨.inr (), ![y, x], (1 : Fin 2), (0 : Fin 2), transfer hj hi h, rfl, rfl⟩

/-- A reduct copy whose vertex order agrees with the order of its parts is
also an ordered copy. Both copies have the same vertex map. -/
def System.edgeOrderCopy (H : System L P X) (A : RelStructure L U)
    (a : RelStructure.Embedding A H.toRelStructure)
    (hMono : StrictMono (H.part ∘ a)) :
    RelStructure.Embedding A.ordered (H.edgeOrder A).toRelStructure where
  toFun := a
  injective := a.injective
  map_rel_iff := by
    intro R z
    cases R with
    | inl r => exact a.map_rel_iff r z
    | inr r =>
        change Fin 2 → U at z
        change (H.part (a (z 0)) < H.part (a (z 1)) ∧
          (∃ b : RelStructure.Embedding A H.toRelStructure,
            a (z 0) ∈ copyCarrier b ∧ a (z 1) ∈ copyCarrier b)) ↔ z 0 < z 1
        exact ⟨fun h => hMono.lt_iff_lt.mp h.1,
          fun h => ⟨hMono h, a, ⟨z 0, rfl⟩, ⟨z 1, rfl⟩⟩⟩

private def System.edgeOrderReductCopy (H : System L P X) (A : RelStructure L U)
    (a : RelStructure.Embedding A.ordered (H.edgeOrder A).toRelStructure) :
    RelStructure.Embedding A H.toRelStructure where
  toFun := a
  injective := a.injective
  map_rel_iff r z := a.map_rel_iff (.inl r) z

/-- Adding supported order comparisons preserves the complete edge support
when every reduct edge already agrees with the order of its parts. -/
theorem System.edgeOrder_support_eq (H : System L P X) (A : RelStructure L U)
    (hMono : ∀ a : RelStructure.Embedding A H.toRelStructure,
      StrictMono (H.part ∘ a)) :
    supportCopies A.ordered (H.edgeOrder A).toRelStructure = supportCopies A H.toRelStructure := by
  apply Set.Subset.antisymm
  · rintro _ ⟨a, rfl⟩
    exact ⟨H.edgeOrderReductCopy A a, rfl⟩
  · rintro _ ⟨a, rfl⟩
    exact ⟨H.edgeOrderCopy A a (hMono a), rfl⟩

omit [LinearOrder U] in
/-- Order comparisons in an edge-ordered system are supported by its reduct
edges, so adding them preserves the assertion that tuples are edge-supported. -/
theorem System.edgeOrder_relationsCoveredBy (H : System L P X) (A : RelStructure L U)
    (hRel : RelationsCoveredBy (supportCopies A H.toRelStructure) H.toRelStructure) :
    RelationsCoveredBy (supportCopies A H.toRelStructure) (H.edgeOrder A).toRelStructure := by
  intro R z hz
  cases R with
  | inl r => exact hRel r z hz
  | inr r =>
      change Fin 2 → X at z
      change H.part (z 0) < H.part (z 1) ∧
        (∃ a : RelStructure.Embedding A H.toRelStructure,
          z 0 ∈ copyCarrier a ∧ z 1 ∈ copyCarrier a) at hz
      obtain ⟨a, h₀, h₁⟩ := hz.2
      exact ⟨copyCarrier a, ⟨a, rfl⟩, fun i => by fin_cases i <;> assumption⟩

/-- The induced irreducible sets in the edge-ordered language are exactly
the cliques of the pair shadow, assuming the reduct tuples are supported
and every edge meets each part at most once. -/
theorem System.edgeOrder_irreducible_iff_pairCovered
    (H : System L P X) (A : RelStructure L U)
    (hRel : RelationsCoveredBy (supportCopies A H.toRelStructure) H.toRelStructure)
    (hFine : ∀ a : RelStructure.Embedding A H.toRelStructure,
      Function.Injective (H.part ∘ a)) (S : Set X) :
    ((H.edgeOrder A).toRelStructure.induce S).Irreducible ↔
      PairCoveredBy (supportCopies A H.toRelStructure) S := by
  constructor
  · intro hS x y hx hy hxy
    let x' : S := ⟨x, hx⟩
    let y' : S := ⟨y, hy⟩
    obtain ⟨R, z, i, j, hz, hi, hj⟩ := hS (fun h : x' = y' => hxy (congrArg Subtype.val h))
    obtain ⟨e, he, hCover⟩ := H.edgeOrder_relationsCoveredBy A hRel R (Subtype.val ∘ z) hz
    refine ⟨e, he, ?_, ?_⟩
    · simpa only [Function.comp_apply, hi] using hCover i
    · simpa only [Function.comp_apply, hj] using hCover j
  · intro hS x y hxy
    have hNe : x.1 ≠ y.1 := fun h => hxy (Subtype.ext h)
    obtain ⟨e, ⟨a, rfl⟩, hx, hy⟩ := hS x.2 y.2 hNe
    obtain ⟨i, hi⟩ := hx
    obtain ⟨j, hj⟩ := hy
    have hParts : H.part x.1 ≠ H.part y.1 := by
      intro h
      have hij := hFine a (show H.part (a i) = H.part (a j) by rw [hi, hj]; exact h)
      exact hNe (hi.symm.trans ((congrArg a hij).trans hj))
    rcases lt_or_gt_of_ne hParts with h | h
    · refine ⟨.inr (), ![x, y], (0 : Fin 2), (1 : Fin 2), ?_, rfl, rfl⟩
      exact ⟨h, a, ⟨i, hi⟩, ⟨j, hj⟩⟩
    · refine ⟨.inr (), ![y, x], (1 : Fin 2), (0 : Fin 2), ?_, rfl, rfl⟩
      exact ⟨h, a, ⟨j, hj⟩, ⟨i, hi⟩⟩

/-- Ordered irreducible coverage is precisely coverage of the physical
pair-shadow cliques. The condition includes empty and singleton sets. -/
theorem System.edgeOrder_coverage_iff (H : System L P X) (A : RelStructure L U)
    (hRel : RelationsCoveredBy (supportCopies A H.toRelStructure) H.toRelStructure)
    (hMono : ∀ a : RelStructure.Embedding A H.toRelStructure,
      StrictMono (H.part ∘ a)) :
    IrreduciblesExtendTo A.ordered (H.edgeOrder A).toRelStructure ↔
      ∀ S, PairCoveredBy (supportCopies A H.toRelStructure) S →
        ∃ e ∈ supportCopies A H.toRelStructure, S ⊆ e := by
  have hIff := H.edgeOrder_irreducible_iff_pairCovered A hRel
    (fun a => (hMono a).injective)
  constructor
  · intro h S hS
    obtain ⟨a, ha⟩ := h S ((hIff S).mpr hS)
    let b := H.edgeOrderReductCopy A a
    refine ⟨copyCarrier b, ⟨b, rfl⟩, ?_⟩
    intro x hx
    obtain ⟨u, hu⟩ := ha ⟨x, hx⟩
    exact ⟨u, hu.symm⟩
  · intro h S hS
    obtain ⟨_, ⟨a, rfl⟩, ha⟩ := h S ((hIff S).mp hS)
    refine ⟨H.edgeOrderCopy A a (hMono a), ?_⟩
    intro z
    obtain ⟨u, hu⟩ := ha z.2
    exact ⟨u, hu.symm⟩

/-- An edge-supported partite projection is an embedding on every covered
irreducible set. The projection agrees with the A-coordinates on each edge. -/
theorem System.edgeOrder_isPartiteOver (H : System L U X) (A : RelStructure L U)
    (hRel : RelationsCoveredBy (supportCopies A H.toRelStructure) H.toRelStructure)
    (hCoord : ∀ (a : RelStructure.Embedding A H.toRelStructure) (u : U), H.part (a u) = u)
    (hCover : ∀ S, PairCoveredBy (supportCopies A H.toRelStructure) S →
      ∃ e ∈ supportCopies A H.toRelStructure, S ⊆ e) :
    (H.edgeOrder A).IsPartiteOver A.ordered := by
  have hMono (a : RelStructure.Embedding A H.toRelStructure) : StrictMono (H.part ∘ a) := by
    intro x y hxy
    change H.part (a x) < H.part (a y)
    rwa [hCoord a, hCoord a]
  have hCoverage := (H.edgeOrder_coverage_iff A hRel hMono).mpr hCover
  constructor
  · intro R z hz
    cases R with
    | inl r =>
        obtain ⟨_, ⟨a, rfl⟩, ha⟩ := hRel r z hz
        have hEq (i : Fin (L.arity r)) : a (H.part (z i)) = z i := by
          obtain ⟨u, hu⟩ := ha i
          rw [← hu, hCoord a u]
        have hTuple : a ∘ (H.part ∘ z) = z := funext hEq
        exact (a.map_rel_iff r (H.part ∘ z)).mp (hTuple.symm ▸ hz)
    | inr r => exact hz.1
  · intro S hS
    let E := (H.edgeOrder A).toRelStructure
    obtain ⟨a, ha⟩ := hCoverage S hS
    let f := (RelStructure.inclusion E S).factorThroughRange a ha
    refine ⟨f, fun x => ?_⟩
    have hSpec : x.1 = a (f x) := Classical.choose_spec (ha x)
    change f x = H.part x.1
    rw [hSpec]
    exact (hCoord (H.edgeOrderReductCopy A a) (f x)).symm

/-- For edge-generated systems above cutoff two, the one-edge covering
condition follows from support girth and vertex coverage. -/
theorem System.edgeOrder_isPartiteOver_of_girthGT_three
    (H : System L U X) (A : RelStructure L U)
    (hRel : RelationsCoveredBy (supportCopies A H.toRelStructure) H.toRelStructure)
    (hCoord : ∀ (a : RelStructure.Embedding A H.toRelStructure) (u : U), H.part (a u) = u)
    (hGirth : GirthGT (supportCopies A H.toRelStructure) 3)
    (hEdges : (supportCopies A H.toRelStructure).Nonempty)
    (hVertices : ∀ x : X, ∃ e ∈ supportCopies A H.toRelStructure, x ∈ e) :
    (H.edgeOrder A).IsPartiteOver A.ordered := by
  apply H.edgeOrder_isPartiteOver A hRel hCoord
  intro S hS
  by_cases hSub : S.Subsingleton
  · by_cases hNonempty : S.Nonempty
    · obtain ⟨x, hx⟩ := hNonempty
      obtain ⟨e, he, hxe⟩ := hVertices x
      refine ⟨e, he, ?_⟩
      intro y hy
      rwa [hSub hy hx]
    · obtain ⟨e, he⟩ := hEdges
      exact ⟨e, he, fun x hx => (hNonempty ⟨x, hx⟩).elim⟩
  · exact pairCovered_subset_edge_of_girthGT_three hGirth
      (Set.not_subsingleton_iff.mp hSub) hS

end StructuralRamsey.Partite
