import Girth.UntouchedGirthStep

/-! # Untouched-subsystem girth without a chosen fine part

Two distinct base A-copy supports in an A-linear base meet in at most one
point.  If their intersection is nonempty, that point determines the fine
part used by every owner change; if it is empty, any part can be chosen and
the uniqueness premise is vacuous.  Consequently the one-step girth theorem
only needs local forest transversal control at *all* fine parts, not a
separate chosen-point hypothesis.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {UA P X Y I : Type v}

/-- A subsingleton intersection of two base copies is either empty or has a
unique point.  Choose that point when present; otherwise use an arbitrary
point of the first (nonempty) base copy. -/
theorem exists_unique_finePart
    (α β : UA ↪ P)
    (hInter : (Set.range α ∩ Set.range β).Subsingleton)
    (u : UA) :
    ∃ p : P,
      ∀ w : P, w ∈ Set.range α ∩ Set.range β → w = p := by
  classical
  by_cases hn : (Set.range α ∩ Set.range β).Nonempty
  · rcases hn with ⟨p, hp⟩
    exact ⟨p, fun w hw => hInter hw hp⟩
  · refine ⟨α u, ?_⟩
    intro w hw
    exact (hn ⟨w, hw⟩).elim

/-- The conditional girth-preservation theorem with no fixed fine part.
For the structural local-forest witness, the all-parts hypothesis follows
from transversality of the support hypergraph. -/
theorem no_short_untouched_projected_cycle_all_parts
    (A : RelStructure L UA)
    (C : StructuralRamsey.Partite.System L P X)
    (S : Set X)
    (E : StructuralRamsey.Partite.System L P Y)
    (f : I → StructuralRamsey.Partite.Embedding (C.induce S) E)
    (α β : UA ↪ P)
    (hA : A.Irreducible)
    (hCoreSupport : ∀ y : Y, E.part y ∈ Set.range α)
    (hInter : (Set.range α ∩ Set.range β).Subsingleton)
    (u v : UA) (huv : u ≠ v)
    [Nonempty I]
    (F : I → HypergraphPiece Y)
    (g : ℕ)
    (hLocalForest : LocalForestThrough F g)
    (hCarrier : ∀ i : I,
      (F i).carrier = copyCarrier ((f i).toEmbedding))
    (hPart : ∀ p : P,
      EdgesMeetPartAtMostOne F {y | E.part y = p})
    (hOldBeta :
      GirthGT
        (supportCopies A
          (C.induce (activeCarrier A C β)).toRelStructure) g)
    (c : BergeCycle (supportCopies A
      (StructuralRamsey.Partite.Attachment.attach C S E f).toRelStructure))
    (hLen : c.length ≤ g)
    (hProjected : ∀ j : Fin c.length,
      ∃ a : StructuralRamsey.Partite.ProjectedEmbedding A
        (StructuralRamsey.Partite.Attachment.attach C S E f) β,
        c.edge j = copyCarrier a.val) :
    False := by
  obtain ⟨p, hp⟩ := exists_unique_finePart α β hInter u
  exact
    no_short_untouched_projected_cycle
      A C S E f α β hA hCoreSupport hInter u v huv
      F g hLocalForest hCarrier p hp (hPart p) hOldBeta
      c hLen hProjected

end StructuralRamsey.Girth
