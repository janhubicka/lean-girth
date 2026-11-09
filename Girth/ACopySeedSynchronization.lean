module

public import Mathlib.Tactic

public section

/-!
# Colour synchronization over a seed diagram

This is the colour-selection interface on physical nodes.  It makes no assertion
that a diagram with the required geometric properties or local Ramsey steps
exists.  In particular, it does not construct the recursive forest witnesses.

The admissible embeddings in `backwardFusion` retain whichever designated-chart
and geometric conditions an application needs.  Only their identity and
composition laws enter this argument.  No assumption on the geometry of the
seed is used.  Colours need only form a nonempty type; finiteness is not needed
for this transfer argument.  Empty projection fibres receive an arbitrary colour.
-/

namespace StructuralRamsey.Girth.ACopySeedSynchronization

universe u v w z t

/-- Every colouring has a monochromatic designated member. -/
def FamilyArrow {X : Type u} {B : Type v} (F : B → Set X) (κ : Type w) : Prop :=
  ∀ χ : X → κ, ∃ b k, ∀ x ∈ F b, χ x = k

/-- Each lifted member projects into the base member named by its owner. -/
def Projects {X : Type u} {Y : Type v} {B : Type w} {J : Type z}
    (F : B → Set X) (G : J → Set Y) (owner : J → B) (π : Y → X) : Prop :=
  ∀ j y, y ∈ G j → π y ∈ F (owner j)

/-- For each colouring upstairs, one base colouring is realized on a lift of
every designated base member.  The chosen lift can depend on that colouring. -/
def Synchronizes {X : Type u} {Y : Type v} {B : Type w} {J : Type z}
    (G : J → Set Y) (owner : J → B) (π : Y → X) (κ : Type t) : Prop :=
  ∀ χ : Y → κ, ∃ c : X → κ, ∀ b, ∃ j, owner j = b ∧
    ∀ y ∈ G j, χ y = c (π y)

/-- Synchronization transfers the seed's Ramsey arrow to its lifted family. -/
theorem familyArrow_of_synchronizes
    {X : Type u} {Y : Type v} {B : Type w} {J : Type z} {κ : Type t}
    {F : B → Set X} {G : J → Set Y} {owner : J → B} {π : Y → X}
    (hproject : Projects F G owner π) (hsync : Synchronizes G owner π κ)
    (hbase : FamilyArrow F κ) : FamilyArrow G κ := by
  intro χ
  obtain ⟨c, hc⟩ := hsync χ
  obtain ⟨b, k, hb⟩ := hbase c
  obtain ⟨j, hj, hχ⟩ := hc b
  refine ⟨j, k, fun y hy => (hχ y hy).trans ?_⟩
  apply hb
  simpa only [hj] using hproject j y hy

/-- Constancy on each fibre gives a colouring of the entire seed, including
empty fibres.  This does not require the projection to be surjective. -/
theorem factor_through_of_fibreConstant
    {X : Type u} {Y : Type v} {κ : Type w} [Nonempty κ]
    (π : Y → X) (χ : Y → κ)
    (h : ∀ y z, π y = π z → χ y = χ z) :
    ∃ c : X → κ, ∀ y, χ y = c (π y) := by
  classical
  let c : X → κ := fun x =>
    if hx : ∃ y, π y = x then χ (Classical.choose hx) else Classical.choice ‹Nonempty κ›
  refine ⟨c, ?_⟩
  intro y
  have hy : ∃ z, π z = π y := ⟨y, rfl⟩
  simp only [c, dite_eq_left hy]
  exact h y (Classical.choose hy) (Classical.choose_spec hy).symm

/-- Backward selection through a finite list of physical-node fibres.
Admissibility records the application's designated-chart preservation.
Repeated profiles are allowed here; geometric refinement arguments may need
a repetition-free list separately. -/
theorem backwardFusion
    {X : Type u} {V : ℕ → Type v} {κ : Type w}
    (π : ∀ i, V i → X) (α : ℕ → X)
    (Allowed : ∀ i j, (V i ↪ V j) → Prop)
    (hid : ∀ i, Allowed i i (Function.Embedding.refl (V i)))
    (hcomp : ∀ i j k (f : V i ↪ V j) (g : V j ↪ V k),
      Allowed i j f → Allowed j k g → Allowed i k (f.trans g))
    (n : ℕ)
    (step : ∀ i < n, ∀ χ : V (i + 1) → κ,
      ∃ f : V i ↪ V (i + 1), Allowed i (i + 1) f ∧
        (∀ x, π (i + 1) (f x) = π i x) ∧
        ∀ x y, π i x = α i → π i y = α i → χ (f x) = χ (f y))
    (χ : V n → κ) :
    ∃ f : V 0 ↪ V n, Allowed 0 n f ∧
      (∀ x, π n (f x) = π 0 x) ∧
      ∀ i < n, ∀ x y, π 0 x = α i → π 0 y = α i → χ (f x) = χ (f y) := by
  induction n with
  | zero =>
      exact ⟨Function.Embedding.refl _, hid 0, fun _ => rfl,
        fun i hi => (Nat.not_lt_zero i hi).elim⟩
  | succ n ih =>
      obtain ⟨g, hg, hgp, hgc⟩ := step n (Nat.lt_succ_self n) χ
      obtain ⟨f, hf, hfp, hfc⟩ := ih
        (fun i hi => step i (Nat.lt_succ_of_lt hi)) (fun x => χ (g x))
      refine ⟨f.trans g, hcomp 0 n (n + 1) f g hf hg,
        fun x => (hgp (f x)).trans (hfp x), ?_⟩
      intro i hi x y hx hy
      by_cases hin : i < n
      · exact hfc i hin x y hx hy
      · have hieq : i = n := by omega
        subst i
        exact hgc (f x) (f y) ((hfp x).trans hx) ((hfp y).trans hy)

/-- Processing every nonempty initial fibre factors the selected colouring
through the seed.  The final selected embedding remains admissible. -/
theorem factorization_of_finitePass
    {X : Type u} {V : ℕ → Type v} {κ : Type w} [Nonempty κ]
    (π : ∀ i, V i → X) (α : ℕ → X)
    (Allowed : ∀ i j, (V i ↪ V j) → Prop)
    (hid : ∀ i, Allowed i i (Function.Embedding.refl (V i)))
    (hcomp : ∀ i j k (f : V i ↪ V j) (g : V j ↪ V k),
      Allowed i j f → Allowed j k g → Allowed i k (f.trans g))
    (n : ℕ) (hcover : ∀ x : V 0, ∃ i < n, α i = π 0 x)
    (step : ∀ i < n, ∀ χ : V (i + 1) → κ,
      ∃ f : V i ↪ V (i + 1), Allowed i (i + 1) f ∧
        (∀ x, π (i + 1) (f x) = π i x) ∧
        ∀ x y, π i x = α i → π i y = α i → χ (f x) = χ (f y))
    (χ : V n → κ) :
    ∃ f : V 0 ↪ V n, Allowed 0 n f ∧
      (∀ x, π n (f x) = π 0 x) ∧
      ∃ c : X → κ, ∀ x, χ (f x) = c (π 0 x) := by
  obtain ⟨f, hf, hfp, hfc⟩ := backwardFusion π α Allowed hid hcomp n step χ
  refine ⟨f, hf, hfp, factor_through_of_fibreConstant (π 0) (fun x => χ (f x)) ?_⟩
  intro x y hxy
  obtain ⟨i, hi, hα⟩ := hcover x
  exact hfc i hi x y hα.symm (hxy.symm.trans hα.symm)

/-- A factorizing selection synchronizes every designated seed pattern when
admissible selections carry all its initial charts to designated final charts. -/
theorem synchronizes_of_factorizingSelections
    {X : Type u} {Y : Type v} {Z : Type w} {B : Type z} {J : Type t}
    {κ : Type*} (π₀ : Y → X) (π : Z → X)
    (F₀ : B → Set Y) (G : J → Set Z) (owner : J → B)
    (Allowed : (Y ↪ Z) → Prop)
    (hcharts : ∀ f, Allowed f → ∀ b, ∃ j, owner j = b ∧ G j = f '' F₀ b)
    (hselect : ∀ χ : Z → κ, ∃ f : Y ↪ Z, Allowed f ∧
      (∀ y, π (f y) = π₀ y) ∧ ∃ c : X → κ, ∀ y, χ (f y) = c (π₀ y)) :
    Synchronizes G owner π κ := by
  intro χ
  obtain ⟨f, hf, hfp, c, hc⟩ := hselect χ
  refine ⟨c, ?_⟩
  intro b
  obtain ⟨j, hj, hchart⟩ := hcharts f hf b
  refine ⟨j, hj, ?_⟩
  intro z hz
  rw [hchart] at hz
  obtain ⟨y, _, rfl⟩ := hz
  simpa only [hfp] using hc y

/-- The finite backward pass supplies exactly the synchronization interface.
All geometric content remains in the local-step and chart-transport inputs. -/
theorem synchronizes_of_finitePass
    {X : Type u} {V : ℕ → Type v} {κ : Type w} [Nonempty κ]
    {B : Type z} {J : Type t}
    (π : ∀ i, V i → X) (α : ℕ → X)
    (Allowed : ∀ i j, (V i ↪ V j) → Prop)
    (hid : ∀ i, Allowed i i (Function.Embedding.refl (V i)))
    (hcomp : ∀ i j k (f : V i ↪ V j) (g : V j ↪ V k),
      Allowed i j f → Allowed j k g → Allowed i k (f.trans g))
    (n : ℕ) (hcover : ∀ x : V 0, ∃ i < n, α i = π 0 x)
    (step : ∀ i < n, ∀ χ : V (i + 1) → κ,
      ∃ f : V i ↪ V (i + 1), Allowed i (i + 1) f ∧
        (∀ x, π (i + 1) (f x) = π i x) ∧
        ∀ x y, π i x = α i → π i y = α i → χ (f x) = χ (f y))
    (F₀ : B → Set (V 0)) (G : J → Set (V n)) (owner : J → B)
    (hcharts : ∀ f, Allowed 0 n f → ∀ b,
      ∃ j, owner j = b ∧ G j = f '' F₀ b) :
    Synchronizes G owner (π n) κ := by
  apply synchronizes_of_factorizingSelections (π 0) (π n) F₀ G owner (Allowed 0 n) hcharts
  exact factorization_of_finitePass π α Allowed hid hcomp n hcover step

end StructuralRamsey.Girth.ACopySeedSynchronization
