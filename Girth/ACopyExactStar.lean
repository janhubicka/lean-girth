import Mathlib.Logic.Relation
import Mathlib.Data.Quot
import Mathlib.Tactic

/-!
# Generated equivalences in an exact star

This file proves a normal form for the *generated* equivalence, not merely
for equality in a preassigned tag model.  Its class-level input consists
of indexed source types and partial contacts with a core.  The relation
`Step` has only actual contact edges; `Generated` is its equivalence
closure.  The reverse implication in `generated_iff_normal` constructs
paths from both endpoints to the common normal form.

The later `SourceStar` construction supplies the class contacts from
source setoids and shared maps preserving and reflecting equivalence.
No geometric, support-coverage, or system-girth assertion is made here.
-/

namespace StructuralRamsey.Girth.ACopyExactStar

universe u v w z

namespace ClassStar

variable {Core : Type u} {I : Type v} {Source : I → Type w}

/-- The disjoint union before identifying contacting source classes. -/
abbrev Raw (Core : Type u) (Source : I → Type w) := Core ⊕ Sigma Source

variable (contact : (i : I) → Source i → Option Core)

/-- Only declared source-to-core contacts generate identifications. -/
inductive Step : Raw Core Source → Raw Core Source → Prop
  | contact (i : I) (a : Source i) (c : Core)
      (h : contact i a = some c) : Step (.inr ⟨i, a⟩) (.inl c)

/-- The smallest equivalence containing the contact identifications. -/
abbrev Generated := Relation.EqvGen (Step contact)

/-- Core classes stay core; noncontacting source classes stay private. -/
def normal : Raw Core Source → Raw Core Source
  | .inl c => .inl c
  | .inr ⟨i, a⟩ =>
      match contact i a with
      | none => .inr ⟨i, a⟩
      | some c => .inl c

theorem generated_normal (x : Raw Core Source) :
    Generated contact x (normal contact x) := by
  cases x with
  | inl c => exact .refl _
  | inr s =>
      rcases s with ⟨i, a⟩
      cases h : contact i a with
      | none => simpa [normal, h] using (Relation.EqvGen.refl
          (r := Step contact) (.inr ⟨i, a⟩))
      | some c => simpa [normal, h] using (Relation.EqvGen.rel _ _
          (Step.contact i a c h))

/-- Equality of tags is proved equivalent to the generated relation. -/
theorem generated_iff_normal (x y : Raw Core Source) :
    Generated contact x y ↔ normal contact x = normal contact y := by
  constructor
  · intro h
    induction h with
    | rel x y h =>
        cases h with
        | contact i a c h => simp [normal, h]
    | refl => rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  · intro h
    exact .trans _ _ _ (generated_normal contact x)
      (h ▸ Relation.EqvGen.symm _ _ (generated_normal contact y))

theorem generated_core_iff (c d : Core) :
    Generated contact (.inl c) (.inl d) ↔ c = d := by
  rw [generated_iff_normal]
  simp [normal]

theorem generated_source_core_iff (i : I) (a : Source i) (c : Core) :
    Generated contact (.inr ⟨i, a⟩) (.inl c) ↔
      contact i a = some c := by
  rw [generated_iff_normal]
  cases h : contact i a <;> simp [normal, h]

/-- Partial injectivity gives the exact restriction to each source. -/
theorem generated_source_iff
    (hInjective : ∀ i a b c, contact i a = some c →
      contact i b = some c → a = b)
    (i : I) (a b : Source i) :
    Generated contact (.inr ⟨i, a⟩) (.inr ⟨i, b⟩) ↔ a = b := by
  constructor
  · intro h
    have hn := (generated_iff_normal contact _ _).mp h
    cases ha : contact i a with
    | none =>
        cases hb : contact i b with
        | none => simpa [normal, ha, hb] using hn
        | some d => simp [normal, ha, hb] at hn
    | some c =>
        cases hb : contact i b with
        | none => simp [normal, ha, hb] at hn
        | some d =>
            have hcd : c = d := by simpa [normal, ha, hb] using hn
            exact hInjective i a b c ha (hcd ▸ hb)
  · rintro rfl
    exact .refl _

/-- Two distinct sources meet only at a common actual core contact. -/
theorem generated_distinct_sources_iff (i j : I) (hij : i ≠ j)
    (a : Source i) (b : Source j) :
    Generated contact (.inr ⟨i, a⟩) (.inr ⟨j, b⟩) ↔
      ∃ c, contact i a = some c ∧ contact j b = some c := by
  rw [generated_iff_normal]
  cases ha : contact i a with
  | none =>
      cases hb : contact j b with
      | none =>
          constructor
          · intro h
            have hs : (⟨i, a⟩ : Sigma Source) = ⟨j, b⟩ :=
              Sum.inr.inj (α := Core) (by simpa [normal, ha, hb] using h)
            exact (hij (congrArg Sigma.fst hs)).elim
          · rintro ⟨c, h, _⟩
            simp at h
      | some d => simp [normal, ha, hb, eq_comm]
  | some c =>
      cases hb : contact j b with
      | none => simp [normal, ha, hb]
      | some d => simp [normal, ha, hb, eq_comm]

/-- Exactly the active labels occur: every core label, and precisely
those private labels whose source classes have no contact. -/
theorem normal_range_iff (x : Raw Core Source) :
    x ∈ Set.range (normal contact) ↔
      match x with
      | .inl _ => True
      | .inr ⟨i, a⟩ => contact i a = none := by
  cases x with
  | inl c => exact ⟨fun _ => trivial, fun _ => ⟨.inl c, rfl⟩⟩
  | inr s =>
      rcases s with ⟨i, a⟩
      constructor
      · rintro ⟨y, hy⟩
        cases y with
        | inl c => cases hy
        | inr t =>
            rcases t with ⟨j, b⟩
            cases hb : contact j b with
            | none =>
                have hs : (⟨j, b⟩ : Sigma Source) = ⟨i, a⟩ :=
                  Sum.inr.inj (α := Core) (by simpa [normal, hb] using hy)
                cases hs
                exact hb
            | some c => simp [normal, hb] at hy
      · intro h
        exact ⟨.inr ⟨i, a⟩, by simp [normal, h]⟩

/-- The honest generated quotient maps into exactly the active labels. -/
def quotientNormal : Quot (Step contact) → Set.range (normal contact) :=
  Quot.lift (fun x => ⟨normal contact x, ⟨x, rfl⟩⟩) (by
    intro x y h
    apply Subtype.ext
    exact (generated_iff_normal contact x y).mp (.rel _ _ h))

theorem quotientNormal_bijective : Function.Bijective (quotientNormal contact) := by
  constructor
  · intro x y
    refine Quot.inductionOn x ?_
    intro a
    refine Quot.inductionOn y ?_
    intro b h
    apply Quot.eqvGen_sound
    exact (generated_iff_normal contact a b).mpr (congrArg Subtype.val h)
  · rintro ⟨x, y, rfl⟩
    exact ⟨Quot.mk _ y, rfl⟩

/-- A genuine quotient equivalence with the core/private normal form. -/
noncomputable def quotientEquiv :
    Quot (Step contact) ≃ Set.range (normal contact) :=
  Equiv.ofBijective (quotientNormal contact) (quotientNormal_bijective contact)

end ClassStar

namespace SourceStar

variable {Core : Type u} {I : Type v} {Source : I → Type w}
    {Shared : I → Type z}
variable (coreEq : Setoid Core) (sourceEq : (i : I) → Setoid (Source i))
    (alpha : (i : I) → Shared i → Core)
    (beta : (i : I) → Shared i → Source i)

/-- A source equivalence class touches a core class through a shared
representative. The shared maps need not be injective for this theorem. -/
def Touch (i : I) (a : Quotient (sourceEq i)) (c : Quotient coreEq) : Prop :=
  ∃ s : Shared i, Quotient.mk _ (beta i s) = a ∧ Quotient.mk _ (alpha i s) = c

variable (compatible : ∀ i s t,
    coreEq (alpha i s) (alpha i t) ↔ sourceEq i (beta i s) (beta i t))

include compatible in
theorem touch_unique (i : I) (a : Quotient (sourceEq i))
    (c d : Quotient coreEq)
    (hc : Touch coreEq sourceEq alpha beta i a c)
    (hd : Touch coreEq sourceEq alpha beta i a d) : c = d := by
  rcases hc with ⟨s, hsa, hsc⟩
  rcases hd with ⟨t, hta, htd⟩
  have hst := Quotient.exact (hsa.trans hta.symm)
  exact hsc.symm.trans ((Quotient.sound ((compatible i s t).mpr hst)).trans htd)

include compatible in
theorem touch_injective (i : I) (a b : Quotient (sourceEq i))
    (c : Quotient coreEq)
    (ha : Touch coreEq sourceEq alpha beta i a c)
    (hb : Touch coreEq sourceEq alpha beta i b c) : a = b := by
  rcases ha with ⟨s, hsa, hsc⟩
  rcases hb with ⟨t, htb, htc⟩
  have hst := Quotient.exact (hsc.trans htc.symm)
  exact hsa.symm.trans ((Quotient.sound ((compatible i s t).mp hst)).trans htb)

/-- The partial map on source quotient classes is constructed from
contact witnesses, rather than supplied as an extra hypothesis. -/
noncomputable def contact (i : I) (a : Quotient (sourceEq i)) :
    Option (Quotient coreEq) := by
  classical
  exact if h : ∃ c, Touch coreEq sourceEq alpha beta i a c then
    some (Classical.choose h) else none

include compatible in
theorem contact_eq_some_iff (i : I) (a : Quotient (sourceEq i))
    (c : Quotient coreEq) :
    contact coreEq sourceEq alpha beta i a = some c ↔
      Touch coreEq sourceEq alpha beta i a c := by
  classical
  by_cases h : ∃ d, Touch coreEq sourceEq alpha beta i a d
  · simp only [contact, dite_eq_left h, Option.some.injEq]
    constructor
    · intro heq
      exact heq ▸ Classical.choose_spec h
    · intro hc
      exact touch_unique coreEq sourceEq alpha beta compatible i a _ c
        (Classical.choose_spec h) hc
  · simp only [contact, dite_eq_right h]
    constructor
    · intro heq
      cases heq
    · intro hc
      exact (h ⟨c, hc⟩).elim

include compatible in
theorem contact_injective :
    ∀ i a b c, contact coreEq sourceEq alpha beta i a = some c →
      contact coreEq sourceEq alpha beta i b = some c → a = b := by
  intro i a b c ha hb
  exact touch_injective coreEq sourceEq alpha beta compatible i a b c
    ((contact_eq_some_iff coreEq sourceEq alpha beta compatible i a c).mp ha)
    ((contact_eq_some_iff coreEq sourceEq alpha beta compatible i b c).mp hb)

include compatible in
/-- A private class is exactly a class containing no shared representative. -/
theorem contact_eq_none_iff (i : I) (a : Quotient (sourceEq i)) :
    contact coreEq sourceEq alpha beta i a = none ↔
      ¬ ∃ s : Shared i, Quotient.mk (sourceEq i) (beta i s) = a := by
  constructor
  · intro hnone ⟨s, hs⟩
    have hsome := (contact_eq_some_iff coreEq sourceEq alpha beta compatible i a
      (Quotient.mk coreEq (alpha i s))).mpr ⟨s, hs, rfl⟩
    rw [hnone] at hsome
    cases hsome
  · intro hprivate
    cases h : contact coreEq sourceEq alpha beta i a with
    | none => rfl
    | some c =>
        obtain ⟨s, hs, _⟩ :=
          (contact_eq_some_iff coreEq sourceEq alpha beta compatible i a c).mp h
        exact (hprivate ⟨s, hs⟩).elim

include compatible in
/-- The active private labels have precisely the no-shared-point condition
appearing in the exact-star normal form. -/
theorem private_label_range_iff (i : I) (a : Quotient (sourceEq i)) :
    Sum.inr ⟨i, a⟩ ∈ Set.range (ClassStar.normal (contact coreEq sourceEq alpha beta)) ↔
      ¬ ∃ s : Shared i, Quotient.mk (sourceEq i) (beta i s) = a := by
  rw [ClassStar.normal_range_iff]
  exact contact_eq_none_iff coreEq sourceEq alpha beta compatible i a

/-- The generating source relations and the literal shared identifications. -/
inductive Step : ClassStar.Raw Core Source → ClassStar.Raw Core Source → Prop
  | core (c d : Core) (h : coreEq c d) : Step (.inl c) (.inl d)
  | source (i : I) (a b : Source i) (h : sourceEq i a b) :
      Step (.inr ⟨i, a⟩) (.inr ⟨i, b⟩)
  | shared (i : I) (s : Shared i) :
      Step (.inr ⟨i, beta i s⟩) (.inl (alpha i s))

abbrev Generated := Relation.EqvGen (Step coreEq sourceEq alpha beta)

/-- Pass to source classes without performing any cross-source gluing. -/
def classes : ClassStar.Raw Core Source →
    ClassStar.Raw (Quotient coreEq) (fun i => Quotient (sourceEq i))
  | .inl c => .inl (Quotient.mk _ c)
  | .inr ⟨i, a⟩ => .inr ⟨i, Quotient.mk _ a⟩

/-- A canonical map from the disjoint union of source class sets into
the quotient generated on the original source elements. -/
def classToQuotient :
    ClassStar.Raw (Quotient coreEq) (fun i => Quotient (sourceEq i)) →
      Quot (Step coreEq sourceEq alpha beta)
  | .inl c => Quotient.lift (fun x => Quot.mk _ (.inl x))
      (fun c d h => Quot.sound (Step.core c d h)) c
  | .inr ⟨i, a⟩ => Quotient.lift (fun x => Quot.mk _ (.inr ⟨i, x⟩))
      (fun a b h => Quot.sound (Step.source i a b h)) a

theorem classToQuotient_classes (x : ClassStar.Raw Core Source) :
    classToQuotient coreEq sourceEq alpha beta (classes coreEq sourceEq x) =
      Quot.mk _ x := by
  cases x with
  | inl c => rfl
  | inr a => cases a; rfl

include compatible in
theorem classToQuotient_contact (i : I) (a : Quotient (sourceEq i))
    (c : Quotient coreEq)
    (h : contact coreEq sourceEq alpha beta i a = some c) :
    classToQuotient coreEq sourceEq alpha beta (.inr ⟨i, a⟩) =
      classToQuotient coreEq sourceEq alpha beta (.inl c) := by
  rcases (contact_eq_some_iff coreEq sourceEq alpha beta compatible i a c).mp h
    with ⟨s, rfl, rfl⟩
  exact Quot.sound (Step.shared i s)

include compatible in
/-- Quotienting sources first creates exactly the same generated
equivalence as adjoining source relations and shared pairs all at once. -/
theorem generated_iff_class_generated (x y : ClassStar.Raw Core Source) :
    Generated coreEq sourceEq alpha beta x y ↔
      ClassStar.Generated (contact coreEq sourceEq alpha beta)
        (classes coreEq sourceEq x) (classes coreEq sourceEq y) := by
  constructor
  · intro h
    induction h with
    | rel x y h =>
        cases h with
        | core c d h =>
            have heq : classes coreEq sourceEq (.inl c) =
                classes coreEq sourceEq (.inl d) :=
              congrArg Sum.inl (Quotient.sound h)
            rw [heq]
            exact .refl _
        | source i a b h =>
            have heq : classes coreEq sourceEq (.inr ⟨i, a⟩) =
                classes coreEq sourceEq (.inr ⟨i, b⟩) :=
              congrArg (fun q => Sum.inr (⟨i, q⟩ : Sigma (fun j => Quotient (sourceEq j))))
                (Quotient.sound h)
            rw [heq]
            exact .refl _
        | shared i s =>
            apply Relation.EqvGen.rel
            apply ClassStar.Step.contact
            exact (contact_eq_some_iff coreEq sourceEq alpha beta compatible i _ _).mpr
              ⟨s, rfl, rfl⟩
    | refl => exact .refl _
    | symm _ _ _ ih => exact .symm _ _ ih
    | trans _ _ _ _ _ ih₁ ih₂ => exact .trans _ _ _ ih₁ ih₂
  · intro h
    have lift : ∀ a b,
        ClassStar.Generated (contact coreEq sourceEq alpha beta) a b →
        classToQuotient coreEq sourceEq alpha beta a =
        classToQuotient coreEq sourceEq alpha beta b := by
      intro a b h
      induction h with
      | rel a b h =>
          cases h with
          | contact i a c h =>
              exact classToQuotient_contact coreEq sourceEq alpha beta compatible i a c h
      | refl => rfl
      | symm _ _ _ ih => exact ih.symm
      | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂
    have hq := lift _ _ h
    rw [classToQuotient_classes, classToQuotient_classes] at hq
    exact Quot.eqvGen_exact hq

include compatible in
/-- The exact-star theorem on original source sets. No equivalence
between generated relations and tag equality is assumed. -/
theorem generated_iff_normal (x y : ClassStar.Raw Core Source) :
    Generated coreEq sourceEq alpha beta x y ↔
      ClassStar.normal (contact coreEq sourceEq alpha beta) (classes coreEq sourceEq x) =
      ClassStar.normal (contact coreEq sourceEq alpha beta) (classes coreEq sourceEq y) := by
  rw [generated_iff_class_generated coreEq sourceEq alpha beta compatible,
    ClassStar.generated_iff_normal]

include compatible in
theorem generated_core_iff (c d : Core) :
    Generated coreEq sourceEq alpha beta (.inl c) (.inl d) ↔ coreEq c d := by
  rw [generated_iff_class_generated coreEq sourceEq alpha beta compatible]
  change ClassStar.Generated _ (.inl (Quotient.mk _ c)) (.inl (Quotient.mk _ d)) ↔ _
  rw [ClassStar.generated_core_iff, Quotient.eq]

include compatible in
theorem generated_source_iff (i : I) (a b : Source i) :
    Generated coreEq sourceEq alpha beta (.inr ⟨i, a⟩) (.inr ⟨i, b⟩) ↔
      sourceEq i a b := by
  rw [generated_iff_class_generated coreEq sourceEq alpha beta compatible]
  change ClassStar.Generated (contact coreEq sourceEq alpha beta)
      (.inr ⟨i, Quotient.mk (sourceEq i) a⟩)
      (.inr ⟨i, Quotient.mk (sourceEq i) b⟩) ↔ _
  rw [ClassStar.generated_source_iff _
    (contact_injective coreEq sourceEq alpha beta compatible), Quotient.eq]

include compatible in
theorem generated_source_core_iff (i : I) (a : Source i) (c : Core) :
    Generated coreEq sourceEq alpha beta (.inr ⟨i, a⟩) (.inl c) ↔
      ∃ s : Shared i, sourceEq i (beta i s) a ∧ coreEq (alpha i s) c := by
  rw [generated_iff_class_generated coreEq sourceEq alpha beta compatible]
  change ClassStar.Generated (contact coreEq sourceEq alpha beta)
      (.inr ⟨i, Quotient.mk (sourceEq i) a⟩) (.inl (Quotient.mk coreEq c)) ↔ _
  rw [ClassStar.generated_source_core_iff,
    contact_eq_some_iff coreEq sourceEq alpha beta compatible]
  simp only [Touch, Quotient.eq]

include compatible in
/-- The map of core classes into the generated quotient is injective. -/
theorem core_classMap_injective : Function.Injective
    (fun c => classToQuotient coreEq sourceEq alpha beta (.inl c)) := by
  intro c d
  refine Quotient.inductionOn c ?_
  intro a
  refine Quotient.inductionOn d ?_
  intro b h
  apply Quotient.sound
  exact (generated_core_iff coreEq sourceEq alpha beta compatible a b).mp
    (Quot.eqvGen_exact h)

include compatible in
/-- Every individual source's map on classes is injective. -/
theorem source_classMap_injective (i : I) : Function.Injective
    (fun a => classToQuotient coreEq sourceEq alpha beta (.inr ⟨i, a⟩)) := by
  intro a b
  refine Quotient.inductionOn a ?_
  intro x
  refine Quotient.inductionOn b ?_
  intro y h
  apply Quotient.sound
  exact (generated_source_iff coreEq sourceEq alpha beta compatible i x y).mp
    (Quot.eqvGen_exact h)

theorem classes_surjective : Function.Surjective (classes coreEq sourceEq) := by
  intro x
  cases x with
  | inl c =>
      refine Quotient.inductionOn c ?_
      intro a
      exact ⟨.inl a, rfl⟩
  | inr s =>
      rcases s with ⟨i, a⟩
      refine Quotient.inductionOn a ?_
      intro b
      exact ⟨.inr ⟨i, b⟩, rfl⟩

/-- The quotient of original source elements has the same active
normal-form label set as the class-level star. -/
noncomputable def quotientNormal : Quot (Step coreEq sourceEq alpha beta) →
    Set.range (ClassStar.normal (contact coreEq sourceEq alpha beta)) :=
  Quot.lift (fun x => ⟨ClassStar.normal (contact coreEq sourceEq alpha beta)
    (classes coreEq sourceEq x), ⟨classes coreEq sourceEq x, rfl⟩⟩) (by
      intro x y h
      apply Subtype.ext
      exact (generated_iff_normal coreEq sourceEq alpha beta compatible x y).mp
        (.rel _ _ h))

include compatible in
theorem quotientNormal_bijective : Function.Bijective
    (quotientNormal coreEq sourceEq alpha beta compatible) := by
  constructor
  · intro x y
    refine Quot.inductionOn x ?_
    intro a
    refine Quot.inductionOn y ?_
    intro b h
    apply Quot.eqvGen_sound
    exact (generated_iff_normal coreEq sourceEq alpha beta compatible a b).mpr
      (congrArg Subtype.val h)
  · rintro ⟨x, y, rfl⟩
    obtain ⟨a, rfl⟩ := classes_surjective coreEq sourceEq y
    exact ⟨Quot.mk _ a, rfl⟩

/-- The complete exact-star quotient, from the original source sets
to core labels and exactly the noncontacting private class labels. -/
noncomputable def quotientEquiv : Quot (Step coreEq sourceEq alpha beta) ≃
    Set.range (ClassStar.normal (contact coreEq sourceEq alpha beta)) :=
  Equiv.ofBijective (quotientNormal coreEq sourceEq alpha beta compatible)
    (quotientNormal_bijective coreEq sourceEq alpha beta compatible)

include compatible in
/-- A generated class meeting distinct source copies has a core class,
with a representative in the original core set. -/
theorem generated_distinct_sources_iff (i j : I) (hij : i ≠ j)
    (a : Source i) (b : Source j) :
    Generated coreEq sourceEq alpha beta (.inr ⟨i, a⟩) (.inr ⟨j, b⟩) ↔
      ∃ c : Core,
        Generated coreEq sourceEq alpha beta (.inr ⟨i, a⟩) (.inl c) ∧
        Generated coreEq sourceEq alpha beta (.inr ⟨j, b⟩) (.inl c) := by
  constructor
  · intro h
    have hc := (generated_iff_class_generated coreEq sourceEq alpha beta compatible _ _).mp h
    obtain ⟨q, ha, hb⟩ :=
      (ClassStar.generated_distinct_sources_iff (contact coreEq sourceEq alpha beta)
        i j hij (Quotient.mk _ a) (Quotient.mk _ b)).mp hc
    obtain ⟨c, rfl⟩ := Quotient.exists_rep q
    refine ⟨c, ?_, ?_⟩
    · apply (generated_iff_class_generated coreEq sourceEq alpha beta compatible _ _).mpr
      exact (ClassStar.generated_source_core_iff _ _ _ _).mpr ha
    · apply (generated_iff_class_generated coreEq sourceEq alpha beta compatible _ _).mpr
      exact (ClassStar.generated_source_core_iff _ _ _ _).mpr hb
  · rintro ⟨c, ha, hb⟩
    exact .trans _ _ _ ha (.symm _ _ hb)

end SourceStar

end StructuralRamsey.Girth.ACopyExactStar
