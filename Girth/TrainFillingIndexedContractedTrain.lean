import Girth.TrainFillingIndexedChoiceCore
import Girth.TrainRecursiveWitnessInitial

set_option Elab.async false

/-!
# Exact proper-cut wagon quotient of the contracted choice train

The contracted G0 has one physical first-wagon edge for each (c,p),
where c is a heterogeneous W* choice and p an original first-wagon
label. All choices retain the old proper train relations; only the
universal top joins different choices.

The already checked TrainRecursiveWitness.componentTrain constructs
this train, avoiding a second hand-written equivalence hierarchy.
At a nonterminal cut ν its physical quotient wagon names are exactly
C × Quotient (T.wagonSetoid ν). Their equality reflects AND preserves
the actual contracted edge train relation, with no phantom labels.

At the universal top the relation is deliberately universal, so it
is not represented by this proper-cut tagged quotient. This matches
the circulation proof and the verified scattering interfaces.
-/

namespace StructuralRamsey.Girth.IndexedPrivateChoice

universe v
variable {C V P X : Type v}
variable (U : C → PrivateWagonInput V P X)

/-- The actual train on contracted first wagons: disjoint components
at proper cuts, and one global universal top. -/
def contractedChoiceTrain {m : ℕ}
    (_U : C → PrivateWagonInput V P X)
    (T : EdgeTrainLevels P m) (hm : 0 < m) :
    EdgeTrainLevels (C × P) m :=
  TrainRecursiveWitness.componentTrain (I := C) T hm

/-- The literal quotient wagon name on a contracted first wagon.
These names exist for every old train level, but represent the
contracted train itself ONLY at nonterminal levels. -/
def contractedProperParent {m : ℕ}
    (T : EdgeTrainLevels P m) (ν : Fin (m + 1))
    (e : C × P) :
    ProperWagon (Q := Quotient (T.wagonSetoid ν)) U :=
  (e.1, Quotient.mk (T.wagonSetoid ν) e.2)

/-- Every tagged quotient wagon is represented by a contracted
physical first-wagon edge, even for an empty choice type. -/
theorem contractedProperParent_surjective {m : ℕ}
    (T : EdgeTrainLevels P m) (ν : Fin (m + 1)) :
    Function.Surjective (contractedProperParent U T ν) := by
  rintro ⟨c, q⟩
  induction q using Quotient.inductionOn with
  | h p =>
    exact ⟨(c, p), rfl⟩

/-- The crucial proper-cut equivalence: equality of actual tagged
quotient wagon names is exactly the generated contracted train relation.
We do not assert this at the universal top, where distinct choices
have been joined and hence their tagged names would differ. -/
theorem contractedProperParent_eq_iff_rel {m : ℕ}
    (T : EdgeTrainLevels P m) (hm : 0 < m)
    (ν : Fin (m + 1)) (hProper : ν.val < m)
    (e f : C × P) :
    contractedProperParent U T ν e =
        contractedProperParent U T ν f ↔
      (contractedChoiceTrain U T hm).rel ν e f := by
  change (e.1, Quotient.mk (T.wagonSetoid ν) e.2) =
      (f.1, Quotient.mk (T.wagonSetoid ν) f.2) ↔
    ν.val = m ∨ (e.1 = f.1 ∧ T.rel ν e.2 f.2)
  constructor
  · intro h
    exact Or.inr ⟨congrArg Prod.fst h,
      Quotient.exact (congrArg Prod.snd h)⟩
  · rintro (hTop | ⟨hChoice, hRel⟩)
    · exact False.elim ((Nat.ne_of_lt hProper) hTop)
    · exact Prod.ext hChoice (Quotient.sound hRel)

/-- The parent of any heterogeneous G0 filled physical edge is
literally the quotient wagon of its contracted first-wagon owner. -/
@[simp] theorem indexedEdge_properParent_eq_contracted {m : ℕ}
    (T : EdgeTrainLevels P m) (ν : Fin (m + 1))
    (e : Edge U) :
    properParentOf U (fun p => Quotient.mk (T.wagonSetoid ν) p) e =
      contractedProperParent U T ν (e.1, e.2.1) := rfl

end StructuralRamsey.Girth.IndexedPrivateChoice
