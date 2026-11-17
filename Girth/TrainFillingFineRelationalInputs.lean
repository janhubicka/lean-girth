import Girth.TrainFillingFineRelationalCore
import Girth.TrainFillingSelectedBottomOverlap
import Girth.TrainFillingSelectedRelationalOverlap

set_option autoImplicit false

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure
open StructuralRamsey.Partite (System)

universe u u' v

namespace UniformFillingData

variable {L : RelLanguage.{u}} {A X Y : Type v}

/-- Each complete filled edge traverses every fine part once, by the
original template edge and part preservation of canonical placement. -/
theorem generatedEdge_fineParts
    (small : RelStructure L A) (R : RelStructure L X) (H : UniformFillingData Y X)
    (partX : X → A) (partY : Y → A)
    (hTemplate : H.templateEdges = supportCopies small R)
    (hFine : ∀ (a : Embedding small R) u, partX (a u) = u)
    (hPlace : ∀ (f : H.OldEdge) x, partY (H.place f x) = partX x)
    (e : Set Y) (he : e ∈ H.generatedEdges) :
    Set.InjOn partY e ∧ (∀ u : A, ∃ y ∈ e, partY y = u) := by
  obtain ⟨⟨f, s⟩, rfl⟩ := he
  have hs : s.1 ∈ supportCopies small R := hTemplate ▸ s.2
  obtain ⟨a, ha⟩ := hs
  have hRep : H.imageCarrier (f, s) = Set.range (fun u : A => H.place f (a u)) := by
    change H.place f '' s.1 = _
    rw [ha]
    ext y
    constructor
    · rintro ⟨_, ⟨u, rfl⟩, rfl⟩
      exact ⟨u, rfl⟩
    · rintro ⟨u, rfl⟩
      exact ⟨a u, ⟨u, rfl⟩, rfl⟩
  rw [hRep]
  have hu (u : A) : partY (H.place f (a u)) = u := (hPlace f (a u)).trans (hFine a u)
  constructor
  · rintro _ ⟨u, rfl⟩ _ ⟨w, rfl⟩ heq
    exact congrArg (fun z : A => H.place f (a z)) ((hu u).symm.trans (heq.trans (hu w)))
  · intro u
    exact ⟨H.place f (a u), ⟨u, rfl⟩, hu u⟩

end UniformFillingData

namespace IndexedPrivateChoice

variable {L : RelLanguage.{u}} {K : RelLanguage.{u'}}
variable {U A C P V X Y Base : Type v} [LinearOrder U] [Finite U] [Nontrivial X] [Preorder A]
variable {old : RelStructure L U}

/-- The actual lift of an original target vertex preserves its fine part.
One old first wagon through that vertex supplies its canonical placement. -/
theorem selectedOrdered_originalVertex_part
    (W : C → PrivateWagonInput V P X) {N : RelStructure L.withOrder Y}
    (small : RelStructure K A) [Nontrivial A] (R : RelStructure K X)
    (enumerate : X ≃ U)
    (hLinear : ∀ e f : {s : Set Y // s ∈ supportCopies old.ordered N},
      e ≠ f → (e.1 ∩ f.1).Subsingleton)
    (hCover : ∀ x : X, ∃ a : Embedding small R, x ∈ copyCarrier a)
    (hFirstLinear : ∀ c : C, ∀ p q : P, p ≠ q →
      ((W c).oldCarrier p ∩ (W c).oldCarrier q).Subsingleton)
    (M : RelStructure L.withOrder (Vertex W))
    (source : (C × P) → Embedding old.ordered M)
    (hSource : ∀ c : C, ∀ p : P, ∀ x : X,
      source (c, p) (enumerate x) = tagVertex W c ((W c).place p x))
    (partV : V → A) (partX : X → A) (partY : Y → A)
    (hPlace : ∀ (f : {s : Set Y // s ∈ supportCopies old.ordered N}) x,
      partY (orderedFillingPlacement enumerate f x) = partX x)
    (hLocal : ∀ c p (x : {v : V // v ∈ (W c).oldCarrier p}),
      partX ((W c).coordinate p x) = partV x.1)
    (hOld : ∀ (c : C) (x : V), ∃ p, x ∈ (W c).oldCarrier p)
    (b : Embedding M N) (c : C) (v : V) :
    partY (b (tagVertex W c (Sum.inl v))) = partV v := by
  obtain ⟨p, hp⟩ := hOld c v
  let x : {v : V // v ∈ (W c).oldCarrier p} := ⟨v, hp⟩
  let β := selectedOrderedOldEdgeEmbedding W small R enumerate hLinear hCover hFirstLinear
    M source hSource b
  have hCarrier : (β (c, p)).1 = copyCarrier (b.comp (source (c, p))) := rfl
  have hApply : orderedFillingPlacement enumerate (β (c, p)) ((W c).coordinate p x) =
      b (tagVertex W c (Sum.inl v)) := by
    rw [orderedFillingPlacement_comp enumerate (source (c, p)) b (β (c, p)) hCarrier,
      hSource c p, (W c).place_old p x]
  exact (congrArg partY hApply).symm.trans
    ((hPlace (β (c, p)) ((W c).coordinate p x)).trans (hLocal c p x))

/-- Two scattered targets agree on overlapping original order tuples.
Different siblings are disjoint. Separate old parents have a common
physical old edge for any shared distinct pair at the equality cut. -/
theorem selectedOrdered_agree_targetOrder
    (W : C → PrivateWagonInput V P X)
    (small : RelStructure K.withOrder A) [Nontrivial A]
    (R : RelStructure K.withOrder X) (Target : System K.withOrder A V)
    (hForward : PartiteOrderCompatible Target) (enumerate : X ≃ U)
    (D : RelStructure L.withOrder Base) (S : System L.withOrder Base Y)
    (M : RelStructure L.withOrder (Vertex W))
    (family : Set (Embedding M D)) (selected : Set (DesignatedCopy M D S family))
    (hLinear : ∀ e f : {s : Set Y // s ∈ supportCopies old.ordered S.toRelStructure},
      e ≠ f → (e.1 ∩ f.1).Subsingleton)
    (hCover : ∀ x : X, ∃ a : Embedding small R, x ∈ copyCarrier a)
    (hFirstLinear : ∀ c : C, ∀ p q : P, p ≠ q →
      ((W c).oldCarrier p ∩ (W c).oldCarrier q).Subsingleton)
    (source : (C × P) → Embedding old.ordered M)
    (hSource : ∀ c : C, ∀ p : P, ∀ x : X,
      source (c, p) (enumerate x) = tagVertex W c ((W c).place p x))
    (hSupport : supportCopies old.ordered M = Set.range (contractedCarrier W))
    (localCopy : ∀ c : C, ∀ p : P,
      Embedding (Target.toRelStructure.induce ((W c).oldCarrier p)) R)
    (hCoordinate : ∀ c p x, localCopy c p x = (W c).coordinate p x)
    {m q : ℕ} (train : EdgeTrainLevels (OldACarrierEdge old.ordered S.toRelStructure) m)
    (hq : 2 ≤ q)
    (hFull : (selectedPictureOrderOneData old.ordered M D S family selected train 0).FullSystemGirthGT q)
    (i j : {b : DesignatedCopy M D S family // b ∈ selected}) (c d : C)
    (u v : Fin 2 → V)
    (hEq : ∀ k, i.1.embedding (tagVertex W c (Sum.inl (u k))) =
      j.1.embedding (tagVertex W d (Sum.inl (v k))))
    (hv : Target.rel (.inr ()) v) : Target.rel (.inr ()) u := by
  classical
  by_cases hij : i = j
  · subst j
    have hTagged (k : Fin 2) : tagVertex W c (Sum.inl (u k)) =
        tagVertex W d (Sum.inl (v k)) := i.1.embedding.injective (hEq k)
    have hcd : c = d := congrArg Sigma.fst (hTagged 0)
    subst d
    have huv : u = v := funext (fun k => Sum.inl.inj (tagVertex_injective W c (hTagged k)))
    exact huv.symm ▸ hv
  · let image (k : Fin 2) : Y := i.1.embedding (tagVertex W c (Sum.inl (u k)))
    have hNe : image 0 ≠ image 1 := by
      intro hEqImage
      have hImageJ := (hEq 0).symm.trans (hEqImage.trans (hEq 1))
      have hvEq : v 0 = v 1 := Sum.inl.inj
        (tagVertex_injective W d (j.1.embedding.injective hImageJ))
      exact ne_of_lt (hForward v hv) (congrArg Target.part hvEq)
    obtain ⟨f, hx, hy, hi, hj⟩ := selectedPictureBottom_commonEdge_of_sharedPair
      old.ordered M D S family selected train hq hFull i j hij (image 0) (image 1) hNe
      ⟨_, rfl⟩ ⟨_, rfl⟩ ⟨_, (hEq 0).symm⟩ ⟨_, (hEq 1).symm⟩
    have hInside : ∀ k : Fin 2, image k ∈ f.1 := by
      intro k
      fin_cases k
      · exact hx
      · exact hy
    exact (selectedOrdered_rel_iff_of_commonOldCover W small R Target.toRelStructure
      enumerate hLinear hCover hFirstLinear M source hSource hSupport localCopy hCoordinate
      i.1.embedding j.1.embedding c d f hi hj (.inr ())
      (by change 0 < 2; decide) u v hEq hInside).mpr hv

end IndexedPrivateChoice
end StructuralRamsey.Girth
