import Girth.TrainFillingSelectedBottomOverlap
import Girth.TrainFillingSelectedRelationalOverlap
import Girth.TrainBigCycleTwoWagonObstruction

set_option autoImplicit false
set_option Elab.async false

namespace StructuralRamsey.Girth.IndexedPrivateChoice

open StructuralRamsey.RelStructure
open StructuralRamsey.Partite (System)

universe u u' v
variable {L : RelLanguage.{u}} {K : RelLanguage.{u'}}
variable {U A C P V X Y Base : Type v} [LinearOrder U] [Finite U] [Nontrivial X]
variable {old : RelStructure L U}

/-- Any tuple supported in a genuine copy has exactly the relation value
at its fine coordinates. -/
private theorem rel_iff_of_fineCopy
    (small : RelStructure K A) (Target : System K A V)
    (hFine : ∀ (a : Embedding small Target.toRelStructure) x, Target.part (a x) = x)
    (r : K.Symbol) (w : Fin (K.arity r) → V)
    (a : Embedding small Target.toRelStructure) (hInside : ∀ k, w k ∈ copyCarrier a) :
    Target.rel r w ↔ small.rel r (Target.part ∘ w) := by
  have hTuple : a ∘ (Target.part ∘ w) = w := by
    funext k
    obtain ⟨x, hx⟩ := hInside k
    change a (Target.part (w k)) = w k
    rw [← hx, hFine]
  have hRel := a.map_rel_iff r (Target.part ∘ w)
  rw [hTuple] at hRel
  exact hRel

/-- A constant or empty tuple fits in one edge as soon as the target has
an edge and every vertex belongs to an edge. -/
private theorem constantTuple_in_copy
    (small : RelStructure K A) (Target : System K A V)
    (hTargetCover : ∀ x : V, ∃ a : Embedding small Target.toRelStructure, x ∈ copyCarrier a)
    (hTargetEdge : Nonempty (Embedding small Target.toRelStructure))
    (r : K.Symbol) (w : Fin (K.arity r) → V) (hSame : ∀ k l, w k = w l) :
    ∃ a : Embedding small Target.toRelStructure, ∀ k, w k ∈ copyCarrier a := by
  by_cases hr : 0 < K.arity r
  · let k₀ : Fin (K.arity r) := ⟨0, hr⟩
    obtain ⟨a, ha⟩ := hTargetCover (w k₀)
    exact ⟨a, fun k => (hSame k₀ k) ▸ ha⟩
  · obtain ⟨a⟩ := hTargetEdge
    refine ⟨a, fun k => ?_⟩
    exact (hr (Nat.zero_lt_of_lt k.isLt)).elim

/-- The original relational tuples agree wherever two selected lifts
coincide. Two distinct shared images force every image into the same old
edge. Constant and empty tuples are read in the original fine parts. -/
theorem selectedOrdered_agree_targetRel
    (W : C → PrivateWagonInput V P X)
    (small : RelStructure K A) [Nontrivial A] (R : RelStructure K X)
    (Target : System K A V) (enumerate : X ≃ U)
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
    (hTargetFine : ∀ (a : Embedding small Target.toRelStructure) x, Target.part (a x) = x)
    (hTargetCover : ∀ x : V, ∃ a : Embedding small Target.toRelStructure, x ∈ copyCarrier a)
    (hTargetEdge : Nonempty (Embedding small Target.toRelStructure))
    (partY : Y → A)
    (hPart : ∀ (i : {b : DesignatedCopy M D S family // b ∈ selected}) (c : C) (x : V),
      partY (i.1.embedding (tagVertex W c (Sum.inl x))) = Target.part x)
    {m q : ℕ} (train : EdgeTrainLevels (OldACarrierEdge old.ordered S.toRelStructure) m)
    (hq : 2 ≤ q)
    (hFull : (selectedPictureOrderOneData old.ordered M D S family selected train 0).FullSystemGirthGT q)
    (i j : {b : DesignatedCopy M D S family // b ∈ selected}) (c d : C)
    (r : K.Symbol) (u v : Fin (K.arity r) → V)
    (hEq : ∀ k, i.1.embedding (tagVertex W c (Sum.inl (u k))) =
      j.1.embedding (tagVertex W d (Sum.inl (v k)))) :
    Target.rel r u ↔ Target.rel r v := by
  classical
  let image (k : Fin (K.arity r)) : Y := i.1.embedding (tagVertex W c (Sum.inl (u k)))
  by_cases hSame : ∀ k l, image k = image l
  · have hu (k l : Fin (K.arity r)) : u k = u l :=
      Sum.inl.inj (tagVertex_injective W c (i.1.embedding.injective (hSame k l)))
    have hv (k l : Fin (K.arity r)) : v k = v l :=
      Sum.inl.inj (tagVertex_injective W d
        (j.1.embedding.injective ((hEq k).symm.trans ((hSame k l).trans (hEq l)))))
    obtain ⟨a, ha⟩ := constantTuple_in_copy small Target hTargetCover hTargetEdge r u hu
    obtain ⟨b, hb⟩ := constantTuple_in_copy small Target hTargetCover hTargetEdge r v hv
    have hParts : Target.part ∘ u = Target.part ∘ v := by
      funext k
      exact (hPart i c (u k)).symm.trans
        ((congrArg partY (hEq k)).trans (hPart j d (v k)))
    have hV := rel_iff_of_fineCopy small Target hTargetFine r v b hb
    rw [← hParts] at hV
    exact (rel_iff_of_fineCopy small Target hTargetFine r u a ha).trans hV.symm
  · push Not at hSame
    obtain ⟨k, l, hNe⟩ := hSame
    by_cases hij : i = j
    · subst j
      have hTagged (s : Fin (K.arity r)) : tagVertex W c (Sum.inl (u s)) =
          tagVertex W d (Sum.inl (v s)) := i.1.embedding.injective (hEq s)
      have hcd : c = d := congrArg Sigma.fst (hTagged k)
      subst d
      have huv : u = v := funext (fun s => Sum.inl.inj (tagVertex_injective W c (hTagged s)))
      rw [huv]
    · have hLeft (s : Fin (K.arity r)) : image s ∈ copyCarrier i.1.embedding := ⟨_, rfl⟩
      have hRight (s : Fin (K.arity r)) : image s ∈ copyCarrier j.1.embedding := ⟨_, (hEq s).symm⟩
      obtain ⟨f, hf, _, hi, hj⟩ := selectedPictureBottom_commonEdge_of_sharedPair
        old.ordered M D S family selected train hq hFull i j hij (image k) (image l) hNe
        (hLeft k) (hLeft l) (hRight k) (hRight l)
      let O := selectedPictureOrderOneData old.ordered M D S family selected train 0
      have hBound : O.LocalPieceSystemBound 2 := by
        intro n cycle hAccept hOrder
        exact O.localPieceSystemBound_of_supremeCycleBound q hFull.2 n cycle hAccept
          (hOrder.trans (Nat.mul_le_mul_left 2 hq))
      have hInside (s : Fin (K.arity r)) : image s ∈ f.1 := by
        by_contra hOutside
        have hPair : image k ≠ image s := fun h => hOutside (h ▸ hf)
        obtain ⟨g, _, hg, hgi, hgj⟩ := selectedPictureBottom_commonEdge_of_sharedPair
          old.ordered M D S family selected train hq hFull i j hij (image k) (image s) hPair
          (hLeft k) (hLeft s) (hRight k) (hRight s)
        have hParents : O.parent f ≠ O.parent g := by
          intro h
          change Quotient.mk (train.wagonSetoid 0) f = Quotient.mk (train.wagonSetoid 0) g at h
          have hfg : f = g := (train.bottom f g).mp (Quotient.exact h)
          exact hOutside (hfg.symm ▸ hg)
        exact O.no_two_designated_meet_two_wagons hBound i j (O.parent f) (O.parent g)
          hij hParents ⟨f, hi, rfl⟩ ⟨g, hgi, rfl⟩ ⟨f, hj, rfl⟩ ⟨g, hgj, rfl⟩
      exact selectedOrdered_rel_iff_of_commonOldCover W small R Target.toRelStructure
        enumerate hLinear hCover hFirstLinear M source hSource hSupport localCopy hCoordinate
        i.1.embedding j.1.embedding c d f hi hj r (Nat.zero_lt_of_lt k.isLt) u v hEq hInside

end StructuralRamsey.Girth.IndexedPrivateChoice
