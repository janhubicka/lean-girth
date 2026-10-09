import Girth.MappedOwnerGirth
import Girth.ForestUsedOwnerLocalForest

/-!
# Short untouched cycles use only a bounded local forest

The local-forest partite lemma guarantees foresthood only for each
bounded subfamily of local copies, NOT for the whole collection of
all local Ramsey copies. The earlier mapped-owner girth interface
assumed an arbitrary finite global forest of all local copies.

A short Berge cycle supplies one owner label per edge. Its distinct
used labels form a family of at most the cycle length. Restrict the
local witness to exactly those used labels. LocalForestThrough then
proves foresthood, and the original mapped-owner girth theorem
applies verbatim to that restricted family.

This corrects a quantifier mismatch at the boundary of the
circulation untouched-subsystem proof without needing a stronger
local Ramsey theorem or any successor-history argument.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {UA X Y Z I : Type v}

/-- Mapped-owner girth preservation from only the honest
bounded-subfamily forest conclusion of the local partite lemma.
The entire local family indexed by I need NOT form one forest. -/
theorem no_short_support_cycle_of_mapped_bounded_forest
    (A : RelStructure L UA)
    (Old : RelStructure L X)
    (Whole : RelStructure L Z)
    (standard : I → RelStructure.Embedding Old Whole)
    (F : I → HypergraphPiece Y)
    (P : Set Y)
    (core : Y ↪ Z)
    (g : ℕ)
    (hLocal : LocalForestThrough F g)
    (hPart : EdgesMeetPartAtMostOne F P)
    (hOld : GirthGT (supportCopies A Old) g)
    (c : BergeCycle (supportCopies A Whole))
    (hLen : c.length ≤ g)
    (owner : Fin c.length → I)
    (hEdgeOwner :
      ∀ j, c.edge j ⊆ copyCarrier (standard (owner j)))
    (hBoundary :
      ∀ j, owner j ≠ owner (cyclicSucc j) →
        c.vertex j ∈
          core '' ((F (owner j)).restrictCarrier P).carrier ∧
        c.vertex j ∈
          core '' ((F (owner (cyclicSucc j))).restrictCarrier P).carrier) :
    False := by
  classical
  have hPositive : 0 < c.length :=
    lt_of_lt_of_le (by decide) c.hlength
  letI : Nonempty (Fin c.length) := ⟨⟨0, hPositive⟩⟩
  -- The index type of actually used local copies lives at the universe
  -- level of I, whereas the edge index Fin c.length is finite in Type 0.
  -- Construct the finite range directly, without identifying their levels.
  let Q : Type v := {i : I // i ∈ Set.range owner}
  let select : Fin c.length → Q :=
    fun j => ⟨owner j, ⟨j, rfl⟩⟩
  have hSurj : Function.Surjective select := by
    rintro ⟨i, ⟨j, hj⟩⟩
    refine ⟨j, ?_⟩
    apply Subtype.ext
    exact hj
  have hFinite : Finite Q :=
    Finite.of_surjective select hSurj
  letI : Fintype Q := Fintype.ofFinite Q
  letI : Nonempty Q := ⟨select ⟨0, hPositive⟩⟩
  have hCardUsed : Fintype.card Q ≤ g := by
    have hLE := Fintype.card_le_of_surjective select hSurj
    exact hLE.trans (by simpa using hLen)
  let incl : Q ↪ I :=
    ⟨Subtype.val, Subtype.val_injective⟩
  have hUsed : ForestOfCopies (fun q : Q => F q.1) :=
    hLocal Q incl hCardUsed
  have hPartUsed :
      EdgesMeetPartAtMostOne (fun q : Q => F q.1) P := by
    intro q e he
    exact hPart q.1 e he
  apply no_short_support_cycle_of_owner_mapped_forest
    A Old Whole
    (fun q : Q => standard q.1)
    hUsed P hPartUsed core g hOld c hLen select
  · intro j
    exact hEdgeOwner j
  · intro j hNe
    have hNeOriginal : owner j ≠ owner (cyclicSucc j) := by
      intro hEq
      apply hNe
      exact Subtype.ext hEq
    exact hBoundary j hNeOriginal

end StructuralRamsey.Girth
