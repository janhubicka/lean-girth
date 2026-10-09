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
  letI : Fintype (UsedOwner owner) := usedOwnerFintype owner
  letI : Nonempty (UsedOwner owner) := usedOwner_nonempty owner
  have hCard : Fintype.card (Fin c.length) ≤ g := by
    simpa using hLen
  have hUsed : ForestOfCopies
      (fun q : UsedOwner owner => F q.1) :=
    localForest_usedOwners owner F g hLocal hCard
  have hPartUsed :
      EdgesMeetPartAtMostOne
        (fun q : UsedOwner owner => F q.1) P := by
    intro q e he
    exact hPart q.1 e he
  apply no_short_support_cycle_of_owner_mapped_forest
    A Old Whole
    (fun q : UsedOwner owner => standard q.1)
    hUsed P hPartUsed core g hOld c hLen
    (usedOwnerMap owner)
  · intro j
    exact hEdgeOwner j
  · intro j hNe
    have hNeOriginal :
        owner j ≠ owner (cyclicSucc j) := by
      intro hEq
      apply hNe
      exact Subtype.ext hEq
    exact hBoundary j hNeOriginal

end StructuralRamsey.Girth
