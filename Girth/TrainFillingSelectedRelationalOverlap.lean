import Girth.TrainFillingOrderedSelectedCarriers

set_option autoImplicit false

namespace StructuralRamsey.Girth.IndexedPrivateChoice

open StructuralRamsey.RelStructure

universe u u' v

variable {L : RelLanguage.{u}} {K : RelLanguage.{u'}}
variable {U A C P V X Y : Type v}
variable [LinearOrder U] [Finite U] [Nontrivial X]
variable {old : RelStructure L U} {N : RelStructure L.withOrder Y}

/-- Two selected original target tuples in one common old cover agree
on every positive-arity relation. Each tuple pulls back to an actual
induced first wagon, then to the same tuple in the common template. -/
theorem selectedOrdered_rel_iff_of_commonOldCover
    (W : C → PrivateWagonInput V P X)
    (small : RelStructure K A) [Nontrivial A] (R : RelStructure K X) (B : RelStructure K V)
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
    (hSupport : supportCopies old.ordered M = Set.range (contractedCarrier W))
    (localCopy : ∀ c : C, ∀ p : P, Embedding (B.induce ((W c).oldCarrier p)) R)
    (hCoordinate : ∀ c p x, localCopy c p x = (W c).coordinate p x)
    (b d : Embedding M N) (c c' : C)
    (f : {s : Set Y // s ∈ supportCopies old.ordered N})
    (hb : f.1 ⊆ copyCarrier b) (hd : f.1 ⊆ copyCarrier d)
    (r : K.Symbol) (hr : 0 < K.arity r) (u v : Fin (K.arity r) → V)
    (hEq : ∀ j, b (tagVertex W c (Sum.inl (u j))) =
      d (tagVertex W c' (Sum.inl (v j))))
    (hInside : ∀ j, b (tagVertex W c (Sum.inl (u j))) ∈ f.1) :
    B.rel r u ↔ B.rel r v := by
  classical
  have pull (selected : Embedding M N) (choice : C) (w : Fin (K.arity r) → V)
      (hOld : f.1 ⊆ copyCarrier selected)
      (hw : ∀ j, selected (tagVertex W choice (Sum.inl (w j))) ∈ f.1) :
      ∃ (p : P) (z : Fin (K.arity r) → {a : V // a ∈ (W choice).oldCarrier p}),
        (∀ j, (z j).1 = w j) ∧
        (∀ j, orderedFillingPlacement enumerate f (localCopy choice p (z j)) =
          selected (tagVertex W choice (Sum.inl (w j)))) := by
    let H := UniformFillingData.ofOrderedSupportCopies small R enumerate hLinear hCover
    let β := selectedOrderedOldEdgeEmbedding W small R enumerate hLinear hCover
      hFirstLinear M source hSource selected
    have hf : (⟨f.1, f.2⟩ : H.OldEdge) ∈ Set.range β := by
      rw [selectedOrderedOldEdgeEmbedding_range W small R enumerate hLinear hCover
        hFirstLinear M source hSource hSupport selected]
      exact hOld
    obtain ⟨⟨owner, p⟩, hOwner⟩ := hf
    have hCarrier : f.1 = copyCarrier (selected.comp (source (owner, p))) :=
      (congrArg (fun e : H.OldEdge => e.1) hOwner).symm
    have hPlace (x : X) :
        orderedFillingPlacement enumerate f x =
          selected (tagVertex W owner ((W owner).place p x)) := by
      rw [orderedFillingPlacement_comp enumerate (source (owner, p)) selected f hCarrier,
        hSource owner p x]
    have hPoint (j : Fin (K.arity r)) :
        ∃ x : X, orderedFillingPlacement enumerate f x =
          selected (tagVertex W choice (Sum.inl (w j))) := by
      rw [← orderedFillingPlacement_range enumerate f] at hw
      exact hw j
    choose x hx using hPoint
    have hTag (j : Fin (K.arity r)) :
        tagVertex W owner ((W owner).place p (x j)) =
          tagVertex W choice (Sum.inl (w j)) :=
      selected.injective ((hPlace (x j)).symm.trans (hx j))
    have hChoice : owner = choice := congrArg Sigma.fst (hTag ⟨0, hr⟩)
    subst owner
    have hOldPoint (j : Fin (K.arity r)) :
        ∃ z : {a : V // a ∈ (W choice).oldCarrier p},
          z.1 = w j ∧ (W choice).coordinate p z = x j :=
      ((W choice).place_eq_old_iff p (x j) (w j)).mp
        (tagVertex_injective W choice (hTag j))
    choose z hz hcoord using hOldPoint
    refine ⟨p, z, hz, fun j => ?_⟩
    rw [hCoordinate, hcoord]
    exact hx j
  obtain ⟨p, z, hz, hLeft⟩ := pull b c u hb hInside
  obtain ⟨q, w, hw, hRight⟩ := pull d c' v hd
    (fun j => hEq j ▸ hInside j)
  have hLocal :
      (localCopy c p ∘ z) = (localCopy c' q ∘ w) := by
    funext j
    exact (orderedFillingPlacement enumerate f).injective
      ((hLeft j).trans ((hEq j).trans (hRight j).symm))
  have hz' : (fun j => (z j).1) = u := funext hz
  have hw' : (fun j => (w j).1) = v := funext hw
  have hLeftRel := (localCopy c p).map_rel_iff r z
  have hRightRel := (localCopy c' q).map_rel_iff r w
  change R.rel r (localCopy c p ∘ z) ↔ B.rel r (fun j => (z j).1) at hLeftRel
  change R.rel r (localCopy c' q ∘ w) ↔ B.rel r (fun j => (w j).1) at hRightRel
  rw [hz', hLocal] at hLeftRel
  rw [hw'] at hRightRel
  exact hLeftRel.symm.trans hRightRel

end StructuralRamsey.Girth.IndexedPrivateChoice
