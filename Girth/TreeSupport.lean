import Girth.TreeGeometry

/-! # Singleton support in supported tree amalgams

This module isolates the remaining relational clause of Lemma 2.1: when two
constituent/ambient B-copies meet in a singleton, that vertex is contained in
an A-copy inside each incident B-copy.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {U V W X : Type v}

/-- A vertex is supported inside a chosen B-copy when it belongs to an
ambient A-copy whose carrier is contained in that B-copy. -/
def VertexSupportedInBCopy
    (A : RelStructure L U) {B : RelStructure L V}
    {T : RelStructure L W}
    (b : Embedding B T) (x : W) : Prop :=
  ∃ a : Embedding A T,
    x ∈ copyCarrier a ∧ copyCarrier a ⊆ copyCarrier b

/-- Every singleton-sized intersection of distinct B-copy carriers is supported
on both incident sides.  Empty intersections are vacuous. -/
def BSingletonIntersectionsSupported
    (A : RelStructure L U) (B : RelStructure L V)
    (T : RelStructure L W) : Prop :=
  ∀ b₁ b₂ : Embedding B T, ¬ SameCopy b₁ b₂ →
    (copyCarrier b₁ ∩ copyCarrier b₂).Subsingleton →
    ∀ x, x ∈ copyCarrier b₁ ∩ copyCarrier b₂ →
      VertexSupportedInBCopy A b₁ x ∧
        VertexSupportedInBCopy A b₂ x

/-- Support transports through an ambient embedding. -/
theorem vertexSupported_comp
    {A : RelStructure L U} {B : RelStructure L V}
    {T : RelStructure L W} {S : RelStructure L X}
    {b : Embedding B T} {x : W}
    (h : VertexSupportedInBCopy A b x)
    (i : Embedding T S) :
    VertexSupportedInBCopy A (i.comp b) (i x) := by
  rcases h with ⟨a, hx, ha⟩
  refine ⟨i.comp a, ?_, ?_⟩
  · rcases hx with ⟨u, hu⟩
    exact ⟨u, congrArg i hu⟩
  · intro y hy
    rcases hy with ⟨u, hu⟩
    have hau : a u ∈ copyCarrier b := ha ⟨u, rfl⟩
    rcases hau with ⟨v, hv⟩
    refine ⟨v, ?_⟩
    calc
      i (b v) = i (a u) := congrArg i hv
      _ = y := hu

/-- Support depends only on the carrier of the B-copy. -/
theorem vertexSupported_congr
    {A : RelStructure L U} {B : RelStructure L V}
    {T : RelStructure L W}
    {b c : Embedding B T} {x : W}
    (hbc : SameCopy b c)
    (h : VertexSupportedInBCopy A b x) :
    VertexSupportedInBCopy A c x := by
  rcases h with ⟨a, hx, ha⟩
  refine ⟨a, hx, ?_⟩
  intro y hy
  have hby : y ∈ copyCarrier b := ha hy
  change copyCarrier b = copyCarrier c at hbc
  rw [hbc] at hby
  exact hby

/-- Swap the two incident copies in a singleton-support conclusion. -/
theorem singletonSupport_swap
    {A : RelStructure L U} {B : RelStructure L V}
    {T : RelStructure L W}
    {b₁ b₂ : Embedding B T} {x : W}
    (h :
      VertexSupportedInBCopy A b₁ x ∧
        VertexSupportedInBCopy A b₂ x) :
    VertexSupportedInBCopy A b₂ x ∧
      VertexSupportedInBCopy A b₁ x :=
  ⟨h.2, h.1⟩

/-- A singleton-support conclusion can be transferred to different embeddings
representing the same two B-copy carriers. -/
theorem singletonSupport_congr
    {A : RelStructure L U} {B : RelStructure L V}
    {T : RelStructure L W}
    {b₁ b₂ c₁ c₂ : Embedding B T} {x : W}
    (h₁ : SameCopy b₁ c₁) (h₂ : SameCopy b₂ c₂)
    (h :
      VertexSupportedInBCopy A c₁ x ∧
        VertexSupportedInBCopy A c₂ x) :
    VertexSupportedInBCopy A b₁ x ∧
      VertexSupportedInBCopy A b₂ x := by
  exact ⟨vertexSupported_congr h₁.symm h.1,
    vertexSupported_congr h₂.symm h.2⟩

end StructuralRamsey.Girth
