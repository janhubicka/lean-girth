import Girth.ACopyExactStar

/-!
# Generated wagon hierarchies over a star of node sets

Source equivalences live on fixed node sets and are nested with Nat levels.
All output relations are generated from these source relations and the
same shared node identifications.  The glued node type is the level-zero
quotient. Its higher equivalences and wagon quotients are derived, not
supplied as independent data.  This proves the hierarchy component of the
exact-star application; point occurrences and physical carriers are absent.
-/

namespace StructuralRamsey.Girth.ACopyLayeredStar

open ACopyExactStar

universe u v w z

/-- A star of actual node sets with nested source equivalences. -/
structure Diagram (Core : Type u) (I : Type v) (Source : I → Type w)
    (Shared : I → Type z) where
  coreEq : ℕ → Setoid Core
  sourceEq : ℕ → (i : I) → Setoid (Source i)
  alpha : (i : I) → Shared i → Core
  beta : (i : I) → Shared i → Source i
  core_nested : ∀ {m n}, m ≤ n → ∀ {a b}, coreEq m a b → coreEq n a b
  source_nested : ∀ {m n}, m ≤ n → ∀ i {a b}, sourceEq m i a b → sourceEq n i a b
  compatible : ∀ n i s t,
    coreEq n (alpha i s) (alpha i t) ↔ sourceEq n i (beta i s) (beta i t)
  core_zero : ∀ a b, coreEq 0 a b ↔ a = b
  source_zero : ∀ i a b, sourceEq 0 i a b ↔ a = b

variable {Core : Type u} {I : Type v} {Source : I → Type w} {Shared : I → Type z}
variable (D : Diagram Core I Source Shared)

abbrev Raw := ClassStar.Raw Core Source

/-- Literal source relations and shared node pairs at level `n`. -/
abbrev Step (n : ℕ) := SourceStar.Step (D.coreEq n) (D.sourceEq n) D.alpha D.beta

/-- The actual equivalence generated at this cut. -/
abbrev Generated (n : ℕ) := Relation.EqvGen (Step D n)

/-- The only identifications needed to form the basic node pushout. -/
inductive SharedStep : Raw (Core := Core) (Source := Source) →
    Raw (Core := Core) (Source := Source) → Prop
  | shared (i : I) (s : Shared i) :
      SharedStep (.inr ⟨i, D.beta i s⟩) (.inl (D.alpha i s))

theorem generated_zero_iff_shared (x y : Raw (Core := Core) (Source := Source)) :
    Generated D 0 x y ↔ Relation.EqvGen (SharedStep D) x y := by
  constructor
  · intro h
    induction h with
    | rel x y h =>
        cases h with
        | core a b h =>
            have hab := (D.core_zero a b).mp h
            subst b
            exact .refl _
        | source i a b h =>
            have hab := (D.source_zero i a b).mp h
            subst b
            exact .refl _
        | shared i s => exact .rel _ _ (.shared i s)
    | refl => exact .refl _
    | symm _ _ _ ih => exact .symm _ _ ih
    | trans _ _ _ _ _ ih₁ ih₂ => exact .trans _ _ _ ih₁ ih₂
  · exact Relation.EqvGen.mono (fun _ _ h => by
      cases h with
      | shared i s => exact SourceStar.Step.shared i s) x y

theorem step_nested {m n : ℕ} (hmn : m ≤ n) {x y : Raw (Core := Core) (Source := Source)}
    (h : Step D m x y) : Step D n x y := by
  cases h with
  | core a b h => exact .core a b (D.core_nested hmn h)
  | source i a b h => exact .source i a b (D.source_nested hmn i h)
  | shared i s => exact .shared i s

/-- Generated relations inherit nesting from the original node relations. -/
theorem generated_nested {m n : ℕ} (hmn : m ≤ n)
    {x y : Raw (Core := Core) (Source := Source)}
    (h : Generated D m x y) : Generated D n x y :=
  Relation.EqvGen.mono (fun _ _ hxy => step_nested D hmn hxy) _ _ h

theorem generated_core_iff (n : ℕ) (c d : Core) :
    Generated D n (.inl c) (.inl d) ↔ D.coreEq n c d :=
  SourceStar.generated_core_iff _ _ _ _ (D.compatible n) c d

theorem generated_source_iff (n : ℕ) (i : I) (a b : Source i) :
    Generated D n (.inr ⟨i, a⟩) (.inr ⟨i, b⟩) ↔ D.sourceEq n i a b :=
  SourceStar.generated_source_iff _ _ _ _ (D.compatible n) i a b

theorem generated_iff_normal (n : ℕ)
    (x y : Raw (Core := Core) (Source := Source)) :
    Generated D n x y ↔
      ClassStar.normal (SourceStar.contact (D.coreEq n) (D.sourceEq n) D.alpha D.beta)
          (SourceStar.classes (D.coreEq n) (D.sourceEq n) x) =
      ClassStar.normal (SourceStar.contact (D.coreEq n) (D.sourceEq n) D.alpha D.beta)
          (SourceStar.classes (D.coreEq n) (D.sourceEq n) y) :=
  SourceStar.generated_iff_normal _ _ _ _ (D.compatible n) x y

/-- Wagon labels are derived quotient classes of actual nodes. -/
abbrev Wagon (n : ℕ) := Quot (Step D n)

/-- The parent is induced by the identity on original nodes. -/
def parent {m n : ℕ} (hmn : m ≤ n) : Wagon D m → Wagon D n :=
  Quot.map id (fun {_ _} h => step_nested D hmn h)

@[simp] theorem parent_mk {m n : ℕ} (hmn : m ≤ n)
    (x : Raw (Core := Core) (Source := Source)) :
    parent D hmn (Quot.mk _ x) = Quot.mk _ x := rfl

theorem parent_refl (n : ℕ) (q : Wagon D n) : parent D (le_refl n) q = q := by
  refine Quot.inductionOn q ?_
  intro x
  rfl

theorem parent_comp {l m n : ℕ} (hlm : l ≤ m) (hmn : m ≤ n) (q : Wagon D l) :
    parent D hmn (parent D hlm q) = parent D (hlm.trans hmn) q := by
  refine Quot.inductionOn q ?_
  intro x
  rfl

theorem parent_surjective {m n : ℕ} (hmn : m ≤ n) :
    Function.Surjective (parent D hmn) := by
  intro q
  refine Quot.inductionOn q ?_
  intro x
  exact ⟨Quot.mk _ x, rfl⟩

def coreParent {m n : ℕ} (hmn : m ≤ n) : Quotient (D.coreEq m) → Quotient (D.coreEq n) :=
  Quotient.map id (fun {_ _} h => D.core_nested hmn h)

def sourceParent {m n : ℕ} (hmn : m ≤ n) (i : I) :
    Quotient (D.sourceEq m i) → Quotient (D.sourceEq n i) :=
  Quotient.map id (fun {_ _} h => D.source_nested hmn i h)

def coreMap (n : ℕ) (c : Quotient (D.coreEq n)) : Wagon D n :=
  SourceStar.classToQuotient (D.coreEq n) (D.sourceEq n) D.alpha D.beta (.inl c)

def sourceMap (n : ℕ) (i : I) (a : Quotient (D.sourceEq n i)) : Wagon D n :=
  SourceStar.classToQuotient (D.coreEq n) (D.sourceEq n) D.alpha D.beta (.inr ⟨i, a⟩)

theorem coreMap_injective (n : ℕ) : Function.Injective (coreMap D n) :=
  SourceStar.core_classMap_injective _ _ _ _ (D.compatible n)

theorem sourceMap_injective (n : ℕ) (i : I) : Function.Injective (sourceMap D n i) :=
  SourceStar.source_classMap_injective _ _ _ _ (D.compatible n) i

/-- All core quotient maps commute with the generated parents. -/
theorem parent_coreMap {m n : ℕ} (hmn : m ≤ n) (c : Quotient (D.coreEq m)) :
    parent D hmn (coreMap D m c) = coreMap D n (coreParent D hmn c) := by
  refine Quotient.inductionOn c ?_
  intro a
  rfl

/-- All source quotient maps commute, including private-to-core transitions. -/
theorem parent_sourceMap {m n : ℕ} (hmn : m ≤ n) (i : I)
    (a : Quotient (D.sourceEq m i)) :
    parent D hmn (sourceMap D m i a) = sourceMap D n i (sourceParent D hmn i a) := by
  refine Quotient.inductionOn a ?_
  intro b
  rfl

noncomputable abbrev contact (n : ℕ) :=
  SourceStar.contact (D.coreEq n) (D.sourceEq n) D.alpha D.beta

/-- A shared representative witnesses contact at every higher cut. -/
theorem contact_parent {m n : ℕ} (hmn : m ≤ n) (i : I)
    (a : Quotient (D.sourceEq m i)) (c : Quotient (D.coreEq m))
    (h : contact D m i a = some c) :
    contact D n i (sourceParent D hmn i a) = some (coreParent D hmn c) := by
  apply (SourceStar.contact_eq_some_iff _ _ _ _ (D.compatible n) i _ _).mpr
  obtain ⟨s, hs, hc⟩ :=
    (SourceStar.contact_eq_some_iff _ _ _ _ (D.compatible m) i a c).mp h
  exact ⟨s, congrArg (sourceParent D hmn i) hs, congrArg (coreParent D hmn) hc⟩

/-- Equality in the generated quotient means precisely class contact. -/
theorem sourceMap_eq_coreMap_iff (n : ℕ) (i : I)
    (a : Quotient (D.sourceEq n i)) (c : Quotient (D.coreEq n)) :
    sourceMap D n i a = coreMap D n c ↔ contact D n i a = some c := by
  refine Quotient.inductionOn a ?_
  intro x
  refine Quotient.inductionOn c ?_
  intro y
  rw [SourceStar.contact_eq_some_iff _ _ _ _ (D.compatible n)]
  change Quot.mk (Step D n) (.inr ⟨i, x⟩) = Quot.mk _ (.inl y) ↔ _
  constructor
  · intro h
    have hgen := Quot.eqvGen_exact h
    obtain ⟨s, hs, hc⟩ :=
      (SourceStar.generated_source_core_iff _ _ _ _ (D.compatible n) i x y).mp hgen
    exact ⟨s, Quotient.sound hs, Quotient.sound hc⟩
  · rintro ⟨s, hs, hc⟩
    apply Quot.eqvGen_sound
    apply (SourceStar.generated_source_core_iff _ _ _ _ (D.compatible n) i x y).mpr
    exact ⟨s, Quotient.exact hs, Quotient.exact hc⟩

/-- Parent contact is decided at the higher level, even when the child
has no core contact at its own level. -/
theorem parent_sourceMap_eq_coreMap_iff {m n : ℕ} (hmn : m ≤ n) (i : I)
    (a : Quotient (D.sourceEq m i)) (c : Quotient (D.coreEq n)) :
    parent D hmn (sourceMap D m i a) = coreMap D n c ↔
      contact D n i (sourceParent D hmn i a) = some c := by
  rw [parent_sourceMap, sourceMap_eq_coreMap_iff]

/-- The actual glued basic nodes are the level-zero quotient. -/
abbrev Node := Wagon D 0

def nodeCore (c : Core) : Node D := Quot.mk _ (.inl c)
def nodeSource (i : I) (a : Source i) : Node D := Quot.mk _ (.inr ⟨i, a⟩)

theorem nodeCore_injective : Function.Injective (nodeCore D) := by
  intro c d h
  exact (D.core_zero c d).mp ((generated_core_iff D 0 c d).mp (Quot.eqvGen_exact h))

theorem nodeSource_injective (i : I) : Function.Injective (nodeSource D i) := by
  intro a b h
  exact (D.source_zero i a b).mp
    ((generated_source_iff D 0 i a b).mp (Quot.eqvGen_exact h))

/-- Higher relations on the actual node pushout are induced by the
generated wagon quotient, without any independently prescribed relation. -/
def nodeSetoid (n : ℕ) : Setoid (Node D) where
  r x y := parent D (Nat.zero_le n) x = parent D (Nat.zero_le n) y
  iseqv := ⟨fun _ => rfl, fun h => h.symm, fun h₁ h₂ => h₁.trans h₂⟩

/-- This connects the derived relation on glued nodes to the original
equivalence closure, rather than postulating a normal-form criterion. -/
theorem nodeSetoid_mk_iff (n : ℕ) (x y : Raw (Core := Core) (Source := Source)) :
    nodeSetoid D n (Quot.mk _ x) (Quot.mk _ y) ↔ Generated D n x y :=
  ⟨Quot.eqvGen_exact, Quot.eqvGen_sound⟩

theorem nodeSetoid_nested {m n : ℕ} (hmn : m ≤ n) {x y : Node D}
    (h : nodeSetoid D m x y) : nodeSetoid D n x y := by
  have hp := congrArg (parent D hmn) h
  change parent D (Nat.zero_le n) x = parent D (Nat.zero_le n) y
  simpa only [parent_comp] using hp

theorem nodeSetoid_zero (x y : Node D) : nodeSetoid D 0 x y ↔ x = y := by
  change parent D (Nat.zero_le 0) x = parent D (Nat.zero_le 0) y ↔ x = y
  rw [parent_refl, parent_refl]

theorem nodeSetoid_core_iff (n : ℕ) (c d : Core) :
    nodeSetoid D n (nodeCore D c) (nodeCore D d) ↔ D.coreEq n c d :=
  (nodeSetoid_mk_iff D n _ _).trans (generated_core_iff D n c d)

theorem nodeSetoid_source_iff (n : ℕ) (i : I) (a b : Source i) :
    nodeSetoid D n (nodeSource D i a) (nodeSource D i b) ↔ D.sourceEq n i a b :=
  (nodeSetoid_mk_iff D n _ _).trans (generated_source_iff D n i a b)

/-- Quotienting the actual glued nodes gives exactly the generated wagon labels. -/
def nodeWagonMap (n : ℕ) : Quotient (nodeSetoid D n) → Wagon D n :=
  Quotient.lift (parent D (Nat.zero_le n)) (fun _ _ h => h)

theorem nodeWagonMap_bijective (n : ℕ) : Function.Bijective (nodeWagonMap D n) := by
  constructor
  · intro x y
    refine Quotient.inductionOn x ?_
    intro a
    refine Quotient.inductionOn y ?_
    intro b h
    exact Quotient.sound h
  · intro q
    obtain ⟨x, hx⟩ := parent_surjective D (Nat.zero_le n) q
    exact ⟨Quotient.mk _ x, hx⟩

noncomputable def nodeWagonEquiv (n : ℕ) : Quotient (nodeSetoid D n) ≃ Wagon D n :=
  Equiv.ofBijective (nodeWagonMap D n) (nodeWagonMap_bijective D n)

/-- When source top relations are universal, each source top contacts
the core through a node of its nonempty shared domain. -/
theorem top_source_core (top : ℕ)
    (hCore : ∀ c d, D.coreEq top c d)
    (hSource : ∀ i a b, D.sourceEq top i a b)
    (hShared : ∀ i, Nonempty (Shared i))
    (i : I) (a : Source i) (c : Core) :
    Generated D top (.inr ⟨i, a⟩) (.inl c) := by
  obtain ⟨s⟩ := hShared i
  exact (SourceStar.generated_source_core_iff _ _ _ _ (D.compatible top) i a c).mpr
    ⟨s, hSource i _ _, hCore _ _⟩

/-- The universal top is generated, not assumed for the output. -/
theorem generated_top (top : ℕ)
    (hCore : ∀ c d, D.coreEq top c d)
    (hSource : ∀ i a b, D.sourceEq top i a b)
    (hShared : ∀ i, Nonempty (Shared i))
    (x y : Raw (Core := Core) (Source := Source)) : Generated D top x y := by
  cases x with
  | inl c =>
      cases y with
      | inl d => exact (generated_core_iff D top c d).mpr (hCore c d)
      | inr s => exact .symm _ _ (top_source_core D top hCore hSource hShared s.1 s.2 c)
  | inr s =>
      cases y with
      | inl c => exact top_source_core D top hCore hSource hShared s.1 s.2 c
      | inr t =>
          obtain ⟨z⟩ := hShared s.1
          exact .trans _ _ _
            (top_source_core D top hCore hSource hShared s.1 s.2 (D.alpha s.1 z))
            (.symm _ _ (top_source_core D top hCore hSource hShared t.1 t.2 (D.alpha s.1 z)))

theorem top_subsingleton (top : ℕ)
    (hCore : ∀ c d, D.coreEq top c d)
    (hSource : ∀ i a b, D.sourceEq top i a b)
    (hShared : ∀ i, Nonempty (Shared i)) : Subsingleton (Wagon D top) := by
  constructor
  intro x y
  refine Quot.inductionOn x ?_
  intro a
  refine Quot.inductionOn y ?_
  intro b
  exact Quot.eqvGen_sound (generated_top D top hCore hSource hShared a b)

theorem nodeSetoid_top (top : ℕ)
    (hCore : ∀ c d, D.coreEq top c d)
    (hSource : ∀ i a b, D.sourceEq top i a b)
    (hShared : ∀ i, Nonempty (Shared i)) (x y : Node D) : nodeSetoid D top x y :=
  (top_subsingleton D top hCore hSource hShared).elim _ _

/-- A nonempty core supplies the unique top class of the glued hierarchy. -/
@[instance_reducible] noncomputable def uniqueTop [Nonempty Core] (top : ℕ)
    (hCore : ∀ c d, D.coreEq top c d)
    (hSource : ∀ i a b, D.sourceEq top i a b)
    (hShared : ∀ i, Nonempty (Shared i)) : Unique (Wagon D top) where
  default := Quot.mk _ (.inl (Classical.choice inferInstance))
  uniq := fun _ => (top_subsingleton D top hCore hSource hShared).elim _ _

end StructuralRamsey.Girth.ACopyLayeredStar
