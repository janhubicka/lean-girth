import Girth.TrainDesignatedSubcopyRefinement

set_option Elab.async false

/-!
# Restrict full system girth to one exact designated parent

The ambient physical edge set, edge carriers and wagon partition are left
unchanged. Only the designated sort is replaced by one PUnit label whose
carrier and source-edge family are literally those of one old designated
copy.

This is deliberately not an induced restriction of the ambient edge set:
A2--A3 continue to see every old physical edge. Hence acceptability of the
one-parent cycle enlarges exactly to acceptability in the old system.

An old supreme plan at the enlarged cycle uses edges of that same parent.
Its local validity therefore reflects literally, while the already checked
planProducesBigCycle_of_enlargeCycle reflects the complete global
replacement word. No component geometry or scattering hypothesis is used.
-/

namespace StructuralRamsey.Girth.OrderOneData

universe v
variable {V E I P : Type v}

def exactSingleCopyFamily (D : OrderOneData V E I P) (i : I) :
    DesignatedSubcopyFamily D PUnit where
  containingCopy := fun _ => i
  copyCarrier := fun _ => D.copyCarrier i
  copyEdges := fun _ => D.copyEdges i
  carrier_subset := fun _ => fun _ hx => hx
  edges_subset := fun _ => fun _ hx => hx
  siblings_vertex_disjoint := by
    intro a b hab _hParent
    exact False.elim (hab (Subsingleton.elim _ _))
  siblings_wagon_disjoint := by
    intro a b hab _hParent
    exact False.elim (hab (Subsingleton.elim _ _))

namespace DesignatedSubcopyFamily

variable {D : OrderOneData V E I P}

theorem exactSingleCopy_enlargeLabel_injective (i : I) :
    Function.Injective (exactSingleCopyFamily D i).enlargeLabel := by
  intro a b h
  cases a with
  | inl u =>
      cases b with
      | inl v =>
          exact congrArg Sum.inl (Subsingleton.elim u v)
      | inr e => cases h
  | inr e =>
      cases b with
      | inl u => cases h
      | inr f => exact congrArg Sum.inr (Sum.inr.inj h)

theorem exactSingleCopy_planValid_of_enlarge
    (i : I) {n : ℕ}
    (C : (exactSingleCopyFamily D i).target.BigCycle n)
    (k : Fin n) (hk : C.label k = Sum.inl PUnit.unit)
    (pieces : Fin n → TrainSupremePiece E P)
    (hPlan :
      ((exactSingleCopyFamily D i).enlargeCycle C).PlanValid D k pieces) :
    C.PlanValid (exactSingleCopyFamily D i).target k pieces := by
  intro j
  constructor
  · intro hSame
    exact (hPlan j).1 (congrArg
      (exactSingleCopyFamily D i).enlargeLabel hSame)
  · intro hOther
    have hOldOther :
        (exactSingleCopyFamily D i).enlargeLabel (C.label j) ≠
          (exactSingleCopyFamily D i).enlargeLabel (C.label k) := by
      intro h
      exact hOther ((exactSingleCopy_enlargeLabel_injective (D := D) i) h)
    have hj := (hPlan j).2 hOldOther
    cases hp : pieces j with
    | keep =>
        simp only [hp] at hj
    | short e =>
        have hs :
            ((exactSingleCopyFamily D i).enlargeCycle C).ShortValid D k j e := by
          simpa only [hp] using hj
        obtain ⟨he, hPrev, hCurr⟩ := hs
        change e ∈ D.edges
          ((exactSingleCopyFamily D i).enlargeLabel (C.label k)) at he
        rw [hk] at he
        change e ∈ D.copyEdges i at he
        change e ∈ (exactSingleCopyFamily D i).target.edges (C.label k) ∧
          (exactSingleCopyFamily D i).target.Incident (.inr e)
            (C.connector (trainCyclicPred j)) ∧
          (exactSingleCopyFamily D i).target.Incident (.inr e)
            (C.connector j)
        rw [hk]
        exact ⟨he, hPrev, hCurr⟩
    | long e w f =>
        have hl :
            ((exactSingleCopyFamily D i).enlargeCycle C).LongValid D k j e w f := by
          simpa only [hp] using hj
        obtain ⟨x, y, hPrev, hCurr, he, hf, hne, hpe, hpf, hxe, hyf, hPair⟩ := hl
        change e ∈ D.edges
          ((exactSingleCopyFamily D i).enlargeLabel (C.label k)) at he
        change f ∈ D.edges
          ((exactSingleCopyFamily D i).enlargeLabel (C.label k)) at hf
        rw [hk] at he hf
        change e ∈ D.copyEdges i at he
        change f ∈ D.copyEdges i at hf
        change ∃ x y : V,
          C.connector (trainCyclicPred j) = Sum.inl x ∧
          C.connector j = Sum.inl y ∧
          e ∈ (exactSingleCopyFamily D i).target.edges (C.label k) ∧
          f ∈ (exactSingleCopyFamily D i).target.edges (C.label k) ∧
          e ≠ f ∧ D.parent e = w ∧ D.parent f = w ∧
          x ∈ D.edgeCarrier e ∧ y ∈ D.edgeCarrier f ∧ ¬ D.PairEdge x y
        refine ⟨x, y, ?_, ?_, ?_, ?_, hne, hpe, hpf, hxe, hyf, hPair⟩
        · simpa only [DesignatedSubcopyFamily.enlargeCycle_connector] using hPrev
        · simpa only [DesignatedSubcopyFamily.enlargeCycle_connector] using hCurr
        · rw [hk]
          exact he
        · rw [hk]
          exact hf

theorem exactSingleCopy_fullSystemGirthGT
    (D : OrderOneData V E I P) (i : I) {g : ℕ}
    (hGirth : D.FullSystemGirthGT g) :
    (exactSingleCopyFamily D i).target.FullSystemGirthGT g := by
  let S := exactSingleCopyFamily D i
  refine ⟨hGirth.1, ?_⟩
  intro n C hAccept hOrder
  obtain ⟨k, target, hk, hSupreme⟩ :=
    S.enlargeCycle_supreme_parent_of_fullSystemGirth hGirth C hAccept hOrder
  have hTarget : target = PUnit.unit := Subsingleton.elim _ _
  subst target
  obtain ⟨_hDesignated, pieces, hPlan, hGlobal⟩ := hSupreme
  refine ⟨k, ?_, pieces, ?_, ?_⟩
  · rw [hk]
    trivial
  · exact exactSingleCopy_planValid_of_enlarge
      (D := D) i C k hk pieces hPlan
  · exact S.planProducesBigCycle_of_enlargeCycle C pieces hGlobal

end DesignatedSubcopyFamily
end StructuralRamsey.Girth.OrderOneData
