import Girth.TrainRecursiveSelectedPartiteCriterion
import Mathlib.Data.Fintype.Card

set_option autoImplicit false

/-!
# A nontrivial active target cannot embed into an A-sized relational base

Two actual projected A-copies over the same injective part projection
have one source vertex per A-part, but physically different carriers.
If their carriers differ, there is a coordinate where the second
copy has a vertex outside the entire first copy: identifying it with
any first-copy vertex would force the same A-part coordinate.

Thus the true active target has STRICTLY more vertices than finite A.
The argument uses the exact active carrier, not an enlarged ambient
set or a count of duplicated support labels.  Any injection of its
vertex carrier into the A-vertex type would compose with the first
copy's inclusion to an injective self-map of finite A, hence a
surjection, leaving no room for the extra second-copy vertex.

In particular no selected-copy BASE EMBEDDING of the whole active
target into a relational base on the same A-vertex type exists.
This prevents one tempting canonical selected-copy substitution in
the nontrivial-fibre recursion; it does not exclude a genuine
partite gluing construction using another target/base presentation.
No appendix or Ramsey theorem claim.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}} {UA P X Y : Type v}

section ActiveSourceNoSmallBase

variable (A : RelStructure L UA)
variable (C : StructuralRamsey.Partite.System L P X)
variable (α : UA ↪ P)
variable [Finite UA]

local notation "Source" =>
  C.toRelStructure.induce (activeCarrier A C α)

/-- Two physically different projected A-copies in one active fibre
prevent ANY injection of the true active vertex carrier into UA.
Finiteness of UA is used only for injective endomorphism surjectivity. -/
theorem activeCarrier_no_injection_to_A_of_two_copies
    (a b : StructuralRamsey.Partite.ProjectedEmbedding A C α)
    (hDifferent : copyCarrier a.val ≠ copyCarrier b.val)
    (f : activeCarrier A C α → UA)
    (hf : Function.Injective f) : False := by
  classical
  have hPoint : ∃ u : UA, a.val u ≠ b.val u := by
    by_contra hNo
    push Not at hNo
    have hEmb : a.val = b.val := Embedding.ext (fun u => hNo u)
    exact hDifferent (congrArg copyCarrier hEmb)
  obtain ⟨u, hDiff⟩ := hPoint
  have hOutside (v : UA) : a.val v ≠ b.val u := by
    intro hv
    have hvEq : v = u := α.injective (by
      calc
        α v = C.part (a.val v) := (a.property v).symm
        _ = C.part (b.val u) := congrArg C.part hv
        _ = α u := b.property u)
    subst v
    exact hDiff hv
  let copyA : UA → activeCarrier A C α :=
    fun v => ⟨a.val v, projected_mem_activeCarrier A C α a v⟩
  have hCopyA : Function.Injective copyA := by
    intro v w hvw
    exact a.val.injective (congrArg Subtype.val hvw)
  have hSelfInjective : Function.Injective (fun v : UA => f (copyA v)) := by
    intro v w hvw
    exact hCopyA (hf hvw)
  have hSelfSurjective : Function.Surjective (fun v : UA => f (copyA v)) :=
    Finite.surjective_of_injective hSelfInjective
  let extra : activeCarrier A C α :=
    ⟨b.val u, projected_mem_activeCarrier A C α b u⟩
  obtain ⟨v, hv⟩ := hSelfSurjective (f extra)
  have heq : copyA v = extra := hf hv
  exact hOutside v (congrArg Subtype.val heq)

/-- In the nontrivial active fibre the ENTIRE active relational target
cannot embed in a relational base with exactly the A-vertex type.
This is stronger than failure of part-map compatibility: such a
base embedding does not exist even without a part-preservation rule. -/
theorem activeSource_no_embedding_to_A_base_of_two_copies
    (D : RelStructure L UA)
    (a b : StructuralRamsey.Partite.ProjectedEmbedding A C α)
    (hDifferent : copyCarrier a.val ≠ copyCarrier b.val) :
    ¬ Nonempty (Embedding Source D) := by
  rintro ⟨e⟩
  exact activeCarrier_no_injection_to_A_of_two_copies
    A C α a b hDifferent e.toFun e.injective

/-- Consequently the selected-copy type for the whole active relational
target over an A-sized base is empty, whatever local output witness and
prescribed base family are chosen.  This does not forbid nonempty
families of partite embeddings for a differently presented target. -/
theorem fullActive_selectedCopy_isEmpty_of_two_copies
    (D : RelStructure L UA)
    (E : StructuralRamsey.Partite.System L UA Y)
    (family : Set (Embedding Source D))
    (a b : StructuralRamsey.Partite.ProjectedEmbedding A C α)
    (hDifferent : copyCarrier a.val ≠ copyCarrier b.val) :
    IsEmpty (DesignatedCopy Source D E family) :=
  ⟨fun q =>
    (activeSource_no_embedding_to_A_base_of_two_copies A C α D
      a b hDifferent) ⟨q.base⟩⟩

end ActiveSourceNoSmallBase

end StructuralRamsey.Girth
