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

/-- Subsingleton-ness of a B-copy intersection depends only on the two
image carriers. -/
theorem intersectionSubsingleton_congr
    {B : RelStructure L V} {T : RelStructure L W}
    {b₁ b₂ c₁ c₂ : Embedding B T}
    (h₁ : SameCopy b₁ c₁) (h₂ : SameCopy b₂ c₂) :
    (copyCarrier b₁ ∩ copyCarrier b₂).Subsingleton ↔
      (copyCarrier c₁ ∩ copyCarrier c₂).Subsingleton := by
  change copyCarrier b₁ = copyCarrier c₁ at h₁
  change copyCarrier b₂ = copyCarrier c₂ at h₂
  rw [h₁, h₂]

/-- Membership in a B-copy intersection depends only on the two image
carriers. -/
theorem intersectionMem_congr
    {B : RelStructure L V} {T : RelStructure L W}
    {b₁ b₂ c₁ c₂ : Embedding B T}
    (h₁ : SameCopy b₁ c₁) (h₂ : SameCopy b₂ c₂)
    (x : W) :
    x ∈ copyCarrier b₁ ∩ copyCarrier b₂ ↔
      x ∈ copyCarrier c₁ ∩ copyCarrier c₂ := by
  change copyCarrier b₁ = copyCarrier c₁ at h₁
  change copyCarrier b₂ = copyCarrier c₂ at h₂
  rw [h₁, h₂]

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


/-- If a vertex lies in both a B-copy and an ambient A-copy, then controlled
B-intersections plus singleton support let us find an A-copy through that
vertex contained in the chosen B-copy. -/
theorem vertexSupported_of_common_ACopy
    {A : RelStructure L U} {B : RelStructure L V}
    {T : RelStructure L W}
    (hCover : ACopiesCoveredByB A B T)
    (hInter : BIntersectionsControlled A B T)
    (hSingleton : BSingletonIntersectionsSupported A B T)
    (b : Embedding B T) (a : Embedding A T) (x : W)
    (hxA : x ∈ copyCarrier a) (hxB : x ∈ copyCarrier b) :
    VertexSupportedInBCopy A b x := by
  obtain ⟨b₀, ha₀⟩ := hCover a
  by_cases hSame : SameCopy b b₀
  · refine ⟨a, hxA, ?_⟩
    intro y hy
    have hy₀ : y ∈ copyCarrier b₀ := ha₀ hy
    change copyCarrier b = copyCarrier b₀ at hSame
    rw [← hSame] at hy₀
    exact hy₀
  · rcases hInter b b₀ hSame with hSmall | ⟨d, hd⟩
    · exact (hSingleton b b₀ hSame hSmall x
        ⟨hxB, ha₀ hxA⟩).1
    · refine ⟨d, ?_, ?_⟩
      · have hxBoth : x ∈ copyCarrier b ∩ copyCarrier b₀ :=
          ⟨hxB, ha₀ hxA⟩
        rw [hd] at hxBoth
        exact hxBoth
      · intro y hy
        have hyBoth : y ∈ copyCarrier b ∩ copyCarrier b₀ := by
          rw [hd]
          exact hy
        exact hyBoth.1

/-- The singleton-intersection support property transports through an ambient
embedding, for two old B-copies. -/
theorem singletonIntersectionsSupported_comp
    {A : RelStructure L U} {B : RelStructure L V}
    {T : RelStructure L W} {S : RelStructure L X}
    (hSingleton : BSingletonIntersectionsSupported A B T)
    (i : Embedding T S)
    (b₁ b₂ : Embedding B T)
    (hne : ¬ SameCopy (i.comp b₁) (i.comp b₂))
    (hSmall :
      (copyCarrier (i.comp b₁) ∩ copyCarrier (i.comp b₂)).Subsingleton)
    (x : X)
    (hx : x ∈ copyCarrier (i.comp b₁) ∩ copyCarrier (i.comp b₂)) :
    VertexSupportedInBCopy A (i.comp b₁) x ∧
      VertexSupportedInBCopy A (i.comp b₂) x := by
  have hneOld : ¬ SameCopy b₁ b₂ := by
    intro h
    exact hne (sameCopy_comp h i)
  have hSmallOld : (copyCarrier b₁ ∩ copyCarrier b₂).Subsingleton := by
    intro y hy z hz
    apply i.injective
    apply hSmall
    · constructor
      · rcases hy.1 with ⟨u, hu⟩
        exact ⟨u, congrArg i hu⟩
      · rcases hy.2 with ⟨u, hu⟩
        exact ⟨u, congrArg i hu⟩
    · constructor
      · rcases hz.1 with ⟨u, hu⟩
        exact ⟨u, congrArg i hu⟩
      · rcases hz.2 with ⟨u, hu⟩
        exact ⟨u, congrArg i hu⟩
  rcases hx.1 with ⟨u₁, hu₁⟩
  rcases hx.2 with ⟨u₂, hu₂⟩
  have hEq : b₁ u₁ = b₂ u₂ := by
    apply i.injective
    exact hu₁.trans hu₂.symm
  have hOld := hSingleton b₁ b₂ hneOld hSmallOld (b₁ u₁)
    ⟨⟨u₁, rfl⟩, ⟨u₂, hEq.symm⟩⟩
  have hNew :
      VertexSupportedInBCopy A (i.comp b₁) (i (b₁ u₁)) ∧
        VertexSupportedInBCopy A (i.comp b₂) (i (b₁ u₁)) :=
    ⟨vertexSupported_comp hOld.1 i, vertexSupported_comp hOld.2 i⟩
  rw [hu₁] at hNew
  exact hNew

end StructuralRamsey.Girth
