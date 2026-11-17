import Girth.TrainFillingFineRelationalCore

set_option autoImplicit false

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure
open StructuralRamsey.Partite (System)

universe u v
variable {K : RelLanguage.{u}} {A X Y I : Type v} [LinearOrder A]

section Relations

variable (A₀ : RelStructure K A) (Target : System K.withOrder A X)
variable (edges : Set (Set Y)) (part : Y → A) (lift : I → X ↪ Y)
variable (hInj : ∀ e ∈ edges, Set.InjOn part e)
variable (hPart : ∀ i x, part (lift i x) = Target.part x)

/-- Restore the relations of the selected targets on the physical filling.
Every restored tuple and every edge tuple is evaluated at its fine parts. -/
def restoreSelectedFillingRelations : System K.withOrder A Y where
  toRelStructure := {
    rel := fun r z => A₀.ordered.rel r (part ∘ z) ∧
      ((∃ e ∈ edges, ∀ k, z k ∈ e) ∨
        ∃ (i : I) (w : Fin (K.withOrder.arity r) → X),
          Target.rel r w ∧ lift i ∘ w = z) }
  part := part
  transversal := by
    intro r z hz j k hEqual
    rcases hz.2 with ⟨e, he, hIn⟩ | ⟨i, w, hw, rfl⟩
    · exact hInj e he (hIn j) (hIn k) hEqual
    · have hTarget : Target.part (w j) = Target.part (w k) :=
        (hPart i (w j)).symm.trans (hEqual.trans (hPart i (w k)))
      exact congrArg (lift i) (Target.transversal r w hw j k hTarget)

local notation "Core" => restoreSelectedFillingRelations A₀ Target edges part lift hInj hPart
local notation "Small" => A₀.ordered

theorem restoreSelectedFillingRelations_projects :
    (Core).toRelStructure.IsHomomorphism Small part := fun _ _ h => h.1

variable [Finite A]
theorem restoredFillingCore_fine (a : Embedding Small (Core).toRelStructure) (x : A) :
    part (a x) = x := by
  have hm : StrictMono (part ∘ a) := by
    intro a₁ a₂ hlt
    let pair : Fin 2 → A := ![a₁, a₂]
    exact ((a.map_rel_iff (.inr ()) pair).mpr hlt).1
  exact congrFun hm.eq_id x

variable (hOnto : ∀ e ∈ edges, ∀ a : A, ∃ y ∈ e, part y = a)

/-- Reuse the established ordered edge coordinates on each literal
physical edge. Added relations cannot change any tuple on that edge. -/
noncomputable def restoredFillingEdge (e : {s : Set Y // s ∈ edges}) :
    Embedding Small (Core).toRelStructure := by
  let a := fineFillingCore_edge A₀ Target edges part lift hInj hOnto e
  have hFine (x : A) : part (a x) = x :=
    fineFillingCore_fine A₀ Target edges part lift hInj a x
  have hRange : copyCarrier a = e.1 :=
    copyCarrier_fineFillingCore_edge A₀ Target edges part lift hInj hOnto e
  refine ⟨a, a.injective, ?_⟩
  intro r z
  have hProj : part ∘ a ∘ z = z := funext (fun k => hFine (z k))
  constructor
  · intro hz
    exact hProj ▸ hz.1
  · intro hz
    refine ⟨hProj.symm ▸ hz, Or.inl ⟨e.1, e.2, ?_⟩⟩
    intro k
    exact hRange ▸ (show a (z k) ∈ copyCarrier a from ⟨z k, rfl⟩)

theorem copyCarrier_restoredFillingEdge (e : {s : Set Y // s ∈ edges}) :
    copyCarrier (restoredFillingEdge A₀ Target edges part lift hInj hPart hOnto e) = e.1 :=
  copyCarrier_fineFillingCore_edge A₀ Target edges part lift hInj hOnto e

variable (hSource : Nonempty (Embedding A₀.ordered Target.toRelStructure))
variable (hCover : ∀ x : X, ∃ a : Embedding A₀.ordered Target.toRelStructure, x ∈ copyCarrier a)
variable (hStrong : ∀ i e, e ∈ edges → ∀ x y : X, x ≠ y → lift i x ∈ e → lift i y ∈ e →
  ∃ a : Embedding A₀.ordered Target.toRelStructure, e = lift i '' copyCarrier a)

include hSource hCover hStrong in
/-- The partite pullback of an edge-supported tuple works for nullary
predicates as well. A positive constant tuple only uses vertex coverage. -/
private theorem restoredFillingEdge_pullback
    (i : I) {n : ℕ} (z : Fin n → X) (e : Set Y) (he : e ∈ edges)
    (hIn : ∀ k, lift i (z k) ∈ e) :
    ∃ a : Embedding A₀.ordered Target.toRelStructure, ∀ k, z k ∈ copyCarrier a := by
  classical
  by_cases hn : n = 0
  · subst n
    obtain ⟨a⟩ := hSource
    exact ⟨a, fun k => k.elim0⟩
  let k₀ : Fin n := ⟨0, Nat.pos_of_ne_zero hn⟩
  by_cases hPair : ∃ k, z k ≠ z k₀
  · obtain ⟨k, hk⟩ := hPair
    obtain ⟨a, ha⟩ := hStrong i e he (z k) (z k₀) hk (hIn k) (hIn k₀)
    refine ⟨a, ?_⟩
    intro j
    have hj : lift i (z j) ∈ lift i '' copyCarrier a := ha ▸ hIn j
    obtain ⟨x, hx, heq⟩ := hj
    exact (lift i).injective heq ▸ hx
  · obtain ⟨a, ha⟩ := hCover (z k₀)
    exact ⟨a, fun j => (Classical.not_not.mp (fun h => hPair ⟨j, h⟩)).symm ▸ ha⟩

variable (hFine : ∀ (a : Embedding A₀.ordered Target.toRelStructure) x, Target.part (a x) = x)
variable (hProjection : Target.toRelStructure.IsHomomorphism A₀.ordered Target.part)
variable (hAgree : ∀ (i j : I) (r : K.withOrder.Symbol) (z w : Fin (K.withOrder.arity r) → X),
  lift i ∘ z = lift j ∘ w → Target.rel r w → Target.rel r z)

/-- The literal target lifts are induced for the entire original
language, including relations whose tuple is outside its edge support. -/
noncomputable def restoredFillingTarget
    (i : I) : StructuralRamsey.Partite.Embedding Target Core where
  toEmbedding := {
    toFun := lift i
    injective := (lift i).injective
    map_rel_iff := by
      intro r z
      have hProj : part ∘ lift i ∘ z = Target.part ∘ z :=
        funext (fun k => hPart i (z k))
      constructor
      · intro hz
        rcases hz.2 with ⟨e, he, hIn⟩ | ⟨j, w, hw, hEq⟩
        · obtain ⟨a, ha⟩ := restoredFillingEdge_pullback A₀ Target edges lift
            hSource hCover hStrong i z e he hIn
          choose u hu using ha
          have hMap : a ∘ u = z := funext hu
          have hParts : Target.part ∘ z = u := by
            funext k
            change Target.part (z k) = u k
            rw [← hu k, hFine]
          have hRel : (Small).rel r u := (hProj.trans hParts) ▸ hz.1
          exact hMap ▸ ((a.map_rel_iff r u).mpr hRel)
        · exact hAgree i j r z w hEq.symm hw
      · intro hz
        exact ⟨hProj.symm ▸ hProjection r z hz, Or.inr ⟨i, z, hz, rfl⟩⟩ }
  map_part := hPart i

include hOnto hSource hCover hStrong hFine hProjection hAgree in
/-- A spanning occurrence lies on one physical edge or in one whole
induced target. In the latter case the whole candidate copy pulls back
to an actual target A-copy and has a physical edge as image. -/
theorem supportCopies_restoreSelectedFillingRelations
    (hTargetEdges : ∀ i (a : Embedding Small Target.toRelStructure),
      lift i '' copyCarrier a ∈ edges)
    (r : K.Symbol) (z : Fin (K.arity r) → A)
    (hSpan : Function.Surjective z) (hz : A₀.rel r z) :
    supportCopies Small (Core).toRelStructure = edges := by
  apply Set.Subset.antisymm
  · rintro _ ⟨a, rfl⟩
    have hTuple := (a.map_rel_iff (.inl r) z).mpr hz
    rcases hTuple.2 with ⟨e, he, hIn⟩ | ⟨i, w, _hw, hEq⟩
    · have hIn' (x : A) : a x ∈ e := by
        obtain ⟨k, rfl⟩ := hSpan x
        exact hIn k
      have hFine' := restoredFillingCore_fine A₀ Target edges part lift hInj hPart a
      have hCarrier : copyCarrier a = e := by
        ext y
        constructor
        · rintro ⟨x, rfl⟩
          exact hIn' x
        · intro hy
          exact ⟨part y, hInj e he (hIn' (part y)) hy (hFine' (part y))⟩
      exact hCarrier.symm ▸ he
    · let b := (restoredFillingTarget A₀ Target edges part lift hInj hPart
        hSource hCover hStrong hFine hProjection hAgree i).toEmbedding
      have hRange (x : A) : ∃ y : X, a x = b y := by
        obtain ⟨k, rfl⟩ := hSpan x
        exact ⟨w k, (congrFun hEq k).symm⟩
      let a' := a.factorThroughRange b hRange
      have hApply (x : A) : a x = lift i (a' x) := Classical.choose_spec (hRange x)
      have hCarrier : copyCarrier a = lift i '' copyCarrier a' := by
        ext y
        constructor
        · rintro ⟨x, rfl⟩
          exact ⟨a' x, ⟨x, rfl⟩, (hApply x).symm⟩
        · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
          exact ⟨x, hApply x⟩
      exact hCarrier.symm ▸ hTargetEdges i a'
  · intro e he
    exact ⟨restoredFillingEdge A₀ Target edges part lift hInj hPart hOnto ⟨e, he⟩,
      (copyCarrier_restoredFillingEdge A₀ Target edges part lift hInj hPart hOnto ⟨e, he⟩).symm⟩

end Relations
end StructuralRamsey.Girth
