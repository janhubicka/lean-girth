import Girth.Berge

/-!
# Restriction of nested train edge-equivalence levels

A train in the circulation manuscript consists of nested edge
equivalence relations, starting with equality and ending with the
universal relation. Its wagon parent maps act on equivalence
CLASSES of edges, not on graph vertices.

Deleting unsupported edges restricts every equivalence relation to
the surviving edge labels. This keeps the train height, nesting,
bottom equality and top universal relation. Every restricted wagon
carrier (union of retained child-edge carriers) is contained in
the corresponding old wagon carrier. This is the parent/cut side
of the edge-coverage normalization.

To deduce horizontal-cut girth one additionally passes to the
INJECTIVE map of surviving equivalence classes into old ones and
uses the labelled Berge girth shrinking theorem (#317).
-/

namespace StructuralRamsey.Girth

universe v
variable {E F W : Type v}

/-- The equivalence-level data of a height-m train, with
explicit bottom equality, top universal class and nesting. -/
structure EdgeTrainLevels (E : Type v) (m : ℕ) where
  rel : Fin (m + 1) → E → E → Prop
  equivalent : ∀ μ, Equivalence (rel μ)
  nested : ∀ μ ν : Fin (m + 1), μ ≤ ν →
    ∀ e f : E, rel μ e f → rel ν e f
  bottom : ∀ e f : E,
    rel ⟨0, Nat.zero_lt_succ m⟩ e f ↔ e = f
  top : ∀ e f : E, rel ⟨m, Nat.lt_succ_self m⟩ e f

/-- Restrict every train equivalence level along an injective
embedding of surviving edge labels. -/
def EdgeTrainLevels.restrict
    {m : ℕ} (T : EdgeTrainLevels E m)
    (keep : F ↪ E) : EdgeTrainLevels F m where
  rel := fun μ e f => T.rel μ (keep e) (keep f)
  equivalent := by
    intro μ
    let h := T.equivalent μ
    exact ⟨fun x => h.refl (keep x),
      fun x y hxy => h.symm hxy,
      fun x y z hxy hyz => h.trans hxy hyz⟩
  nested := by
    intro μ ν hle e f hef
    exact T.nested μ ν hle (keep e) (keep f) hef
  bottom := by
    intro e f
    constructor
    · intro h
      exact keep.injective ((T.bottom (keep e) (keep f)).mp h)
    · intro h
      subst f
      exact (T.bottom (keep e) (keep e)).mpr rfl
  top := by
    intro e f
    exact T.top (keep e) (keep f)

/-- A μ-wagon carrier is the union of the physical carriers
of the edges in the μ-equivalence class of its label. -/
def EdgeTrainLevels.wagonCarrier
    {m : ℕ} (T : EdgeTrainLevels E m)
    (edge : E → Set W) (μ : Fin (m + 1)) (a : E) :
    Set W :=
  {x | ∃ b : E, T.rel μ a b ∧ x ∈ edge b}

/-- In a covered-edge subtrain the wagon carrier is a subset of
its original counterpart, for EVERY level and surviving label.
No assumptions about disjoint wagon carriers are necessary. -/
theorem EdgeTrainLevels.wagonCarrier_restrict_subset
    {m : ℕ} (T : EdgeTrainLevels E m)
    (old : E → Set W)
    (keep : F ↪ E) (reduced : F → Set W)
    (hShrink : ∀ f : F, reduced f ⊆ old (keep f))
    (μ : Fin (m + 1)) (a : F) :
    (T.restrict keep).wagonCarrier reduced μ a ⊆
      T.wagonCarrier old μ (keep a) := by
  rintro x ⟨b, hab, hx⟩
  exact ⟨keep b, hab, hShrink b hx⟩

/-- The parent/ancestor equivalence of surviving labels is
exactly the restriction of its old equivalence. -/
theorem EdgeTrainLevels.restrict_rel_iff
    {m : ℕ} (T : EdgeTrainLevels E m)
    (keep : F ↪ E) (μ : Fin (m + 1)) (a b : F) :
    (T.restrict keep).rel μ a b ↔
      T.rel μ (keep a) (keep b) :=
  Iff.rfl

end StructuralRamsey.Girth
