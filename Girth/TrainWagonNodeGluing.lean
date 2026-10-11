import Mathlib.Tactic

/-!
# Exact wagon ancestor gluing by shared and private tagged nodes

The circulation manuscript describes generated train equivalences
as a free union of unary wagon-ancestor nodes, identifying precisely
the local subsystem nodes with their core ancestors.

Represent nodes in a plain tagged sum:
* a shared core ancestor u, or
* a private labelled pair (standard-copy index, old ancestor).
Only the *generated subset* of this ambient sum is used: it consists
of all core-node images and all standard-node images. Thus a private
label for an ancestor already glued to the core is NOT a generated
node. This separates the easy equality calculation on the ambient
sum from the honest free-union membership condition.

Every standard picture contributes its original ancestor labels,
mapped to the common core when identified and otherwise retained
under a private copy tag. Distinct standard copies can therefore
share a wagon node ONLY via a genuine common core ancestor.

The local injection condition says that no two different ancestors
of one standard picture are identified with the same core ancestor.
It guarantees exact restrictions. A parent compatibility condition
then induces a unary global parent map commuting with all core and
standard embeddings, even when a private child gains a shared parent.

This is a precise finite-language presentation of the generated
wagon-equivalence construction. It does not yet establish geometric
wagon intersection predicates, cycle acceptability or full
system-Girth preservation.
-/

namespace StructuralRamsey.Girth

universe u v w
variable {Core : Type u} {Old : Type v} {I : Type w}

/-- A shared core wagon ancestor, or a private old ancestor tagged
by its standard-copy index. -/
abbrev GluedWagonNode (Core : Type u) (Old : Type v) (I : Type w)
    (_glue : I → Old → Option Core) :=
  Core ⊕ (I × Old)

/-- The core's wagon node embeds literally as a shared node. -/
def gluedCoreNode (glue : I → Old → Option Core) (c : Core) :
    GluedWagonNode Core Old I glue :=
  Sum.inl c

/-- Each standard wagon ancestor goes either to its designated
core ancestor, or to a private labelled copy. -/
def gluedStandardNode (glue : I → Old → Option Core)
    (i : I) (a : Old) :
    GluedWagonNode Core Old I glue :=
  match glue i a with
  | none => Sum.inr (i, a)
  | some c => Sum.inl c

/-- Precisely the node labels actually created by identifying
standard-picture ancestors with their shared core ancestors.
The ambient tagged sum may contain inactive private labels for
ancestors that map to a core node; those are not generated. -/
def generatedWagonNodes (glue : I → Old → Option Core) :
    Set (GluedWagonNode Core Old I glue) :=
  Set.range (gluedCoreNode glue) ∪
    ⋃ i : I, Set.range (gluedStandardNode glue i)

/-- Every shared core node belongs to the generated node set. -/
theorem gluedCoreNode_generated (glue : I → Old → Option Core)
    (c : Core) :
    gluedCoreNode glue c ∈ generatedWagonNodes glue :=
  Or.inl ⟨c, rfl⟩

/-- Every standard-picture ancestor has a generated node image. -/
theorem gluedStandardNode_generated (glue : I → Old → Option Core)
    (i : I) (a : Old) :
    gluedStandardNode glue i a ∈ generatedWagonNodes glue :=
  Or.inr (Set.mem_iUnion.mpr ⟨i, ⟨a, rfl⟩⟩)

/-- A standard picture has an EXACT copy of its own wagon nodes:
different local ancestors never collapse in the common core. -/
theorem gluedStandardNode_injective
    (glue : I → Old → Option Core)
    (hInj : ∀ i a b c,
      glue i a = some c → glue i b = some c → a = b)
    (i : I) :
    Function.Injective (gluedStandardNode glue i) := by
  intro a b heq
  cases ha : glue i a with
  | none =>
      cases hb : glue i b with
      | none =>
          have hs :
              (Sum.inr (i, a) : GluedWagonNode Core Old I glue) =
                Sum.inr (i, b) := by
            simpa only [gluedStandardNode, ha, hb] using heq
          exact congrArg Prod.snd (Sum.inr.inj hs)
      | some c =>
          simp [gluedStandardNode, ha, hb] at heq
  | some c =>
      cases hb : glue i b with
      | none =>
          simp [gluedStandardNode, ha, hb] at heq
      | some d =>
          have hs :
              (Sum.inl c : GluedWagonNode Core Old I glue) =
                Sum.inl d := by
            simpa only [gluedStandardNode, ha, hb] using heq
          have hcd : c = d := Sum.inl.inj hs
          exact hInj i a b c ha (by simpa [hcd] using hb)

/-- A standard node meets the shared core exactly at its explicitly
identified core ancestor, not at an accidental image coincidence. -/
theorem gluedStandardNode_eq_core_iff
    (glue : I → Old → Option Core)
    (i : I) (a : Old) (c : Core) :
    gluedStandardNode glue i a = gluedCoreNode glue c ↔
      glue i a = some c := by
  cases h : glue i a with
  | none =>
      simp [gluedStandardNode, gluedCoreNode, h]
  | some d =>
      constructor
      · intro heq
        have hs :
            (Sum.inl d : GluedWagonNode Core Old I glue) =
              Sum.inl c := by
          simpa only [gluedStandardNode, gluedCoreNode, h] using heq
        exact congrArg some (Sum.inl.inj hs)
      · intro hh
        have hdc : d = c := Option.some.inj hh
        have hs :
            (Sum.inl d : GluedWagonNode Core Old I glue) =
              Sum.inl c := congrArg Sum.inl hdc
        simpa only [gluedStandardNode, gluedCoreNode, h] using hs

/-- Different standard pictures can share a wagon ancestor only
through the SAME actual core ancestor. Two private nodes with
different standard-copy labels remain distinct. -/
theorem gluedStandardNode_shared_of_distinct_indices
    (glue : I → Old → Option Core)
    (i j : I) (hi : i ≠ j) (a b : Old)
    (heq : gluedStandardNode glue i a =
      gluedStandardNode glue j b) :
    ∃ c : Core, glue i a = some c ∧ glue j b = some c := by
  cases ha : glue i a with
  | none =>
      cases hb : glue j b with
      | none =>
          have hs :
              (Sum.inr (i, a) : GluedWagonNode Core Old I glue) =
                Sum.inr (j, b) := by
            simpa only [gluedStandardNode, ha, hb] using heq
          exact False.elim
            (hi (congrArg Prod.fst (Sum.inr.inj hs)))
      | some c =>
          simp [gluedStandardNode, ha, hb] at heq
  | some c =>
      cases hb : glue j b with
      | none =>
          simp [gluedStandardNode, ha, hb] at heq
      | some d =>
          have hs :
              (Sum.inl c : GluedWagonNode Core Old I glue) =
                Sum.inl d := by
            simpa only [gluedStandardNode, ha, hb] using heq
          have hcd : c = d := Sum.inl.inj hs
          refine ⟨c, ?_, ?_⟩
          · simp [ha]
          · simp [hb, hcd]

/-- Parent map on the globally glued ancestor nodes. A private child
may have a shared or private parent; the local gluing map at the
parent level determines which case applies. -/
noncomputable def gluedWagonParent
    {CoreChild : Type u} {OldChild : Type v}
    {CoreParent : Type u} {OldParent : Type v}
    (childGlue : I → OldChild → Option CoreChild)
    (parentGlue : I → OldParent → Option CoreParent)
    (pCore : CoreChild → CoreParent)
    (pOld : OldChild → OldParent) :
    GluedWagonNode CoreChild OldChild I childGlue →
      GluedWagonNode CoreParent OldParent I parentGlue
  | .inl c => Sum.inl (pCore c)
  | .inr z => gluedStandardNode parentGlue z.1 (pOld z.2)

/-- Global parent maps restrict EXACTLY to the original
core parent maps. -/
theorem gluedWagonParent_core
    {CoreChild : Type u} {OldChild : Type v}
    {CoreParent : Type u} {OldParent : Type v}
    (childGlue : I → OldChild → Option CoreChild)
    (parentGlue : I → OldParent → Option CoreParent)
    (pCore : CoreChild → CoreParent)
    (pOld : OldChild → OldParent)
    (c : CoreChild) :
    gluedWagonParent childGlue parentGlue pCore pOld
      (gluedCoreNode childGlue c) =
      gluedCoreNode parentGlue (pCore c) := rfl

/-- Parent compatibility means that a shared child ancestor has
the corresponding shared parent ancestor in the core. -/
theorem gluedWagonParent_standard
    {CoreChild : Type u} {OldChild : Type v}
    {CoreParent : Type u} {OldParent : Type v}
    (childGlue : I → OldChild → Option CoreChild)
    (parentGlue : I → OldParent → Option CoreParent)
    (pCore : CoreChild → CoreParent)
    (pOld : OldChild → OldParent)
    (hCompat : ∀ i a c, childGlue i a = some c →
      parentGlue i (pOld a) = some (pCore c))
    (i : I) (a : OldChild) :
    gluedWagonParent childGlue parentGlue pCore pOld
      (gluedStandardNode childGlue i a) =
      gluedStandardNode parentGlue i (pOld a) := by
  cases h : childGlue i a with
  | none =>
      have hs :
          gluedStandardNode childGlue i a =
            (Sum.inr (i, a) :
              GluedWagonNode CoreChild OldChild I childGlue) := by
        simp [gluedStandardNode, h]
      rw [hs]
      rfl
  | some c =>
      have hs :
          gluedStandardNode childGlue i a =
            (Sum.inl c :
              GluedWagonNode CoreChild OldChild I childGlue) := by
        simp [gluedStandardNode, h]
      have hp := hCompat i a c h
      rw [hs]
      change (Sum.inl (pCore c) :
          GluedWagonNode CoreParent OldParent I parentGlue) =
        gluedStandardNode parentGlue i (pOld a)
      simp [gluedStandardNode, hp]

end StructuralRamsey.Girth
