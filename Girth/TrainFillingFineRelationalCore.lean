import Girth.PartiteOrderCompatibility
import Girth.Support
import Mathlib.Order.Preorder.Finite

set_option autoImplicit false

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure
open StructuralRamsey.Partite (System)

universe u v
variable {L : RelLanguage.{u}} {A X Y I : Type v} [LinearOrder A]

section FineCore

variable (A₀ : RelStructure L A) (Target : System L.withOrder A X)
variable (edges : Set (Set Y)) (part : Y → A) (lift : I → X ↪ Y)
variable (hInjective : ∀ e ∈ edges, Set.InjOn part e)

/-- Present the filled edge family over its actual fine parts, retaining
the original order comparisons of the selected targets. -/
def fineFillingCore : System L.withOrder A Y where
  toRelStructure := {
    rel := fun r => match r with
      | .inl r => fun z => A₀.rel r (part ∘ z) ∧
          ∃ e ∈ edges, ∀ k, z k ∈ e
      | .inr _ => fun (z : Fin 2 → Y) => part (z 0) < part (z 1) ∧
          ((∃ e ∈ edges, ∀ k, z k ∈ e) ∨
            ∃ (i : I) (w : Fin 2 → X), Target.rel (.inr ()) w ∧ lift i ∘ w = z) }
  part := part
  transversal := by
    intro r z hz i j hij
    cases r with
    | inl r =>
        obtain ⟨_, e, he, hIn⟩ := hz
        exact hInjective e he (hIn i) (hIn j) hij
    | inr r =>
        cases r
        have hlt : part (z (0 : Fin 2)) < part (z (1 : Fin 2)) := hz.1
        fin_cases i <;> fin_cases j
        · rfl
        · exact (ne_of_lt hlt hij).elim
        · exact (ne_of_lt hlt hij.symm).elim
        · rfl

local notation "Core" => fineFillingCore A₀ Target edges part lift hInjective
local notation "Small" => A₀.ordered

theorem fineFillingCore_forwardCompatible : PartiteOrderCompatible Core :=
  fun _ h => h.1

variable (hOnto : ∀ e ∈ edges, ∀ a : A, ∃ y ∈ e, part y = a)

include hOnto in
/-- Each physical edge has its induced ordered embedding on the fine
coordinates. Comparisons from other targets cannot change it. -/
noncomputable def fineFillingCore_edge (e : {s : Set Y // s ∈ edges}) :
    Embedding Small (Core).toRelStructure := by
  let f (a : A) : Y := Classical.choose (hOnto e.1 e.2 a)
  have hf (a : A) : f a ∈ e.1 ∧ part (f a) = a :=
    Classical.choose_spec (hOnto e.1 e.2 a)
  refine ⟨f, fun a b hab => ?_, ?_⟩
  · exact (hf a).2.symm.trans ((congrArg part hab).trans (hf b).2)
  · intro r z
    cases r with
    | inl r =>
        change (Fin (L.arity r) → A) at z
        change (A₀.rel r (part ∘ f ∘ z) ∧ ∃ s ∈ edges, ∀ k, f (z k) ∈ s) ↔ A₀.rel r z
        have hProj : part ∘ f ∘ z = z := funext (fun k => (hf (z k)).2)
        rw [hProj]
        exact ⟨And.left, fun h => ⟨h, e.1, e.2, fun k => (hf (z k)).1⟩⟩
    | inr r =>
        cases r
        change (Fin 2 → A) at z
        change
          (part (f (z (0 : Fin 2))) < part (f (z (1 : Fin 2))) ∧
            ((∃ s ∈ edges, ∀ k, f (z k) ∈ s) ∨ _)) ↔ z 0 < z 1
        rw [(hf (z 0)).2, (hf (z 1)).2]
        exact ⟨And.left, fun h => ⟨h, Or.inl ⟨e.1, e.2, fun k => (hf (z k)).1⟩⟩⟩

theorem copyCarrier_fineFillingCore_edge (e : {s : Set Y // s ∈ edges}) :
    copyCarrier (fineFillingCore_edge A₀ Target edges part lift hInjective hOnto e) = e.1 := by
  let f := fineFillingCore_edge A₀ Target edges part lift hInjective hOnto e
  have hf (a : A) : f a ∈ e.1 ∧ part (f a) = a :=
    Classical.choose_spec (hOnto e.1 e.2 a)
  change copyCarrier f = e.1
  ext y
  constructor
  · rintro ⟨a, rfl⟩
    exact (hf a).1
  · intro hy
    exact ⟨part y, hInjective e.1 e.2 (hf (part y)).1 hy (hf (part y)).2⟩

variable [Finite A]

/-- The forward order fixes the fine coordinates of every actual
ordered small copy, independent of which carrier witnesses it. -/
theorem fineFillingCore_fine (a : Embedding Small (Core).toRelStructure) (x : A) :
    part (a x) = x := by
  have hm : StrictMono (part ∘ a) := by
    intro x y hxy
    let z : Fin 2 → A := ![x, y]
    exact fineFillingCore_forwardCompatible A₀ Target edges part lift hInjective
      (a ∘ z) ((a.map_rel_iff (.inr ()) z).mpr hxy)
  exact congrFun hm.eq_id x

include hOnto in
/-- A spanning original relation confines every ordered copy to one
physical edge, whose full carrier it exhausts on its fine coordinates. -/
theorem supportCopies_fineFillingCore
    (r : L.Symbol) (z : Fin (L.arity r) → A)
    (hSpan : Function.Surjective z) (hz : A₀.rel r z) :
    supportCopies Small (Core).toRelStructure = edges := by
  apply Set.Subset.antisymm
  · rintro _ ⟨a, rfl⟩
    have ha := (a.map_rel_iff (.inl r) z).mpr hz
    obtain ⟨_, e, he, hIn⟩ := ha
    have haIn (x : A) : a x ∈ e := by
      obtain ⟨k, rfl⟩ := hSpan x
      exact hIn k
    have hCarrier : copyCarrier a = e := by
      ext y
      constructor
      · rintro ⟨x, rfl⟩
        exact haIn x
      · intro hy
        exact ⟨part y, hInjective e he (haIn (part y)) hy
          (fineFillingCore_fine A₀ Target edges part lift hInjective a (part y))⟩
    exact hCarrier.symm ▸ he
  · intro e he
    exact ⟨fineFillingCore_edge A₀ Target edges part lift hInjective hOnto ⟨e, he⟩,
      (copyCarrier_fineFillingCore_edge A₀ Target edges part lift hInjective hOnto
        ⟨e, he⟩).symm⟩

/-- Pull a tuple in one physical edge back to a source edge. A singleton
tuple uses ordinary support coverage, where strongness has no pair. -/
private theorem fineFillingCore_pullback
    (hCovered : ∀ x : X, ∃ a : Embedding Small Target.toRelStructure, x ∈ copyCarrier a)
    (hExact : ∀ i e, e ∈ edges → ∀ x y : X, x ≠ y → lift i x ∈ e → lift i y ∈ e →
      ∃ a : Embedding Small Target.toRelStructure, e = lift i '' copyCarrier a)
    (i : I) {n : ℕ} (hn : 0 < n)
    (z : Fin n → X) (e : Set Y) (he : e ∈ edges)
    (hIn : ∀ k, lift i (z k) ∈ e) :
    ∃ a : Embedding Small Target.toRelStructure, ∀ k, z k ∈ copyCarrier a := by
  classical
  let k₀ : Fin n := ⟨0, hn⟩
  by_cases hPair : ∃ k : Fin n, z k ≠ z k₀
  · obtain ⟨k, hk⟩ := hPair
    obtain ⟨a, ha⟩ := hExact i e he (z k) (z k₀) hk (hIn k) (hIn k₀)
    refine ⟨a, ?_⟩
    intro j
    have hImage : lift i (z j) ∈ lift i '' copyCarrier a := ha ▸ hIn j
    obtain ⟨x, hx, heq⟩ := hImage
    have heq' : x = z j := (lift i).injective heq
    exact heq' ▸ hx
  · obtain ⟨a, ha⟩ := hCovered (z k₀)
    refine ⟨a, ?_⟩
    intro j
    have hz : z j = z k₀ := Classical.not_not.mp (fun hne => hPair ⟨j, hne⟩)
    rw [hz]
    exact ha

/-- The physical target maps are actual induced fine embeddings. On an
edge the order is forced by fine parts. Away from a common physical
edge it is restored from the original targets with compatible overlaps. -/
noncomputable def fineFillingCore_lift
    (hPart : ∀ i x, part (lift i x) = Target.part x)
    (hForward : PartiteOrderCompatible Target)
    (hNormal : ∀ (r : L.Symbol) (z : Fin (L.arity r) → X),
      Target.rel (.inl r) z ↔ A₀.rel r (Target.part ∘ z) ∧
        ∃ a : Embedding Small Target.toRelStructure, ∀ k, z k ∈ copyCarrier a)
    (hPositive : ∀ r : L.Symbol, 0 < L.arity r)
    (hVertex : ∀ x : X, ∃ a : Embedding Small Target.toRelStructure, x ∈ copyCarrier a)
    (hFine : ∀ (a : Embedding Small Target.toRelStructure) u, Target.part (a u) = u)
    (hEdges : ∀ i (a : Embedding Small Target.toRelStructure),
      lift i '' copyCarrier a ∈ edges)
    (hStrong : ∀ i e, e ∈ edges → ∀ x y : X, x ≠ y → lift i x ∈ e → lift i y ∈ e →
      ∃ a : Embedding Small Target.toRelStructure, e = lift i '' copyCarrier a)
    (hAgree : ∀ (i j : I) (z w : Fin 2 → X), lift i ∘ z = lift j ∘ w →
      Target.rel (.inr ()) w → Target.rel (.inr ()) z)
    (i : I) : StructuralRamsey.Partite.Embedding Target Core where
  toEmbedding := {
    toFun := lift i
    injective := (lift i).injective
    map_rel_iff := by
      intro r z
      cases r with
      | inl r =>
          change (Fin (L.arity r) → X) at z
          change (A₀.rel r (part ∘ lift i ∘ z) ∧ ∃ e ∈ edges, ∀ k, lift i (z k) ∈ e) ↔
            Target.rel (.inl r) z
          have hProj : part ∘ lift i ∘ z = Target.part ∘ z := funext (fun k => hPart i (z k))
          constructor
          · rintro ⟨hRel, e, he, hIn⟩
            exact (hNormal r z).mpr ⟨hProj ▸ hRel,
              fineFillingCore_pullback A₀ Target edges lift hVertex hStrong
                i (hPositive r) z e he hIn⟩
          · intro hz
            obtain ⟨hRel, a, ha⟩ := (hNormal r z).mp hz
            exact ⟨hProj.symm ▸ hRel, lift i '' copyCarrier a,
              hEdges i a, fun k => ⟨z k, ha k, rfl⟩⟩
      | inr r =>
          cases r
          change (Fin 2 → X) at z
          change (part (lift i (z 0)) < part (lift i (z 1)) ∧
            ((∃ e ∈ edges, ∀ k, lift i (z k) ∈ e) ∨
              ∃ (j : I) (w : Fin 2 → X), Target.rel (.inr ()) w ∧ lift j ∘ w = lift i ∘ z)) ↔
            Target.rel (.inr ()) z
          constructor
          · rintro ⟨hlt, hInside | ⟨j, w, hw, hEq⟩⟩
            · obtain ⟨e, he, hIn⟩ := hInside
              obtain ⟨a, ha⟩ := fineFillingCore_pullback A₀ Target edges lift hVertex hStrong
                i (by decide : 0 < 2) z e he hIn
              choose u hu using ha
              have hCompose : a ∘ u = z := funext hu
              have hOrder : u 0 < u 1 := by
                have h0 := (hPart i (z 0)).trans
                  ((congrArg Target.part (hu 0)).symm.trans (hFine a (u 0)))
                have h1 := (hPart i (z 1)).trans
                  ((congrArg Target.part (hu 1)).symm.trans (hFine a (u 1)))
                exact h0 ▸ h1 ▸ hlt
              have hRel := (a.map_rel_iff (.inr ()) u).mpr hOrder
              exact hCompose ▸ hRel
            · exact hAgree i j z w hEq.symm hw
          · intro hz
            have hLt : part (lift i (z 0)) < part (lift i (z 1)) := by
              simpa only [hPart] using hForward z hz
            exact ⟨hLt, Or.inr ⟨i, z, hz, rfl⟩⟩ }
  map_part := hPart i

end FineCore

/-- The normalization of the original non-order relations follows from
tuple support and the actual fine coordinates of the original edges. No
arbitrary irreducible-cover condition is required. -/
theorem finePartite_supportedRelations
    (A₀ : RelStructure L A) (Target : System L.withOrder A X)
    (hFine : ∀ (a : Embedding A₀.ordered Target.toRelStructure) u, Target.part (a u) = u)
    (hSupported : ∀ (r : L.Symbol) (z : Fin (L.arity r) → X),
      Target.rel (.inl r) z →
        ∃ a : Embedding A₀.ordered Target.toRelStructure, ∀ k, z k ∈ copyCarrier a)
    (r : L.Symbol) (z : Fin (L.arity r) → X) :
    Target.rel (.inl r) z ↔ A₀.rel r (Target.part ∘ z) ∧
      ∃ a : Embedding A₀.ordered Target.toRelStructure, ∀ k, z k ∈ copyCarrier a := by
  have transport (a : Embedding A₀.ordered Target.toRelStructure)
      (ha : ∀ k, z k ∈ copyCarrier a) :
      Target.rel (.inl r) z ↔ A₀.rel r (Target.part ∘ z) := by
    classical
    choose u hu using ha
    have hMap : a ∘ u = z := funext hu
    have hPart : Target.part ∘ z = u := by
      funext k
      change Target.part (z k) = u k
      rw [← hu k, hFine a]
    rw [hPart, ← hMap]
    exact a.map_rel_iff (.inl r) u
  constructor
  · intro hz
    obtain ⟨a, ha⟩ := hSupported r z hz
    exact ⟨(transport a ha).mp hz, a, ha⟩
  · rintro ⟨hRel, a, ha⟩
    exact (transport a ha).mpr hRel

end StructuralRamsey.Girth
