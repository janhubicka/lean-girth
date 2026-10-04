import Girth.TargetClosure
import PartiteConstruction.Structure.Basic
import Mathlib.Data.Fin.VecNotation

/-! # Actual function-language closure expansions

This module realizes the manuscript's closure functions as genuine set-valued
function symbols in StructuralRamsey.Structure.  The elementary expansion has
only the c_A closure active; the target expansion additionally activates c_B.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {U V : Type v}

/-- The two closure symbols used in the Ramsey input. -/
inductive ClosureFunc : Type u
  | cA
  | cB
  deriving DecidableEq

/-- Add the two closure function symbols to a relational language. -/
def closureLanguage (L : RelLanguage.{u}) : StructuralRamsey.Language.{u} where
  RelSymbol := L.Symbol
  FuncSymbol := ClosureFunc.{u}
  relArity := L.arity
  funcArity
    | .cA => 2
    | .cB => 3

/-- The elementary c_A fibre: the union of all A-copy carriers containing the
displayed distinct pair.  In an A-linear structure this is either empty or one
A-copy carrier. -/
def cAValue
    (A : RelStructure L U) (D : RelStructure L V)
    (x : Fin 2 → V) : Set V :=
  {z | x 0 ≠ x 1 ∧
    ∃ a : Embedding A D,
      x 0 ∈ copyCarrier a ∧
      x 1 ∈ copyCarrier a ∧
      z ∈ copyCarrier a}

/-- The target c_B fibre is the whole carrier exactly on an activating triple:
at least two entries are distinct and the triple is not contained in one
A-copy. -/
def cBValue
    (A : RelStructure L U) (D : RelStructure L V)
    (x : Fin 3 → V) : Set V :=
  {z | (x 0 ≠ x 1 ∨ x 0 ≠ x 2 ∨ x 1 ≠ x 2) ∧
    ¬ TripleInACopy A D (x 0) (x 1) (x 2)}

/-- Elementary A-closure expansion: c_A is active and c_B is everywhere
undefined. -/
def elementaryClosureExpansion
    (A : RelStructure L U) (D : RelStructure L V) :
    StructuralRamsey.Structure (closureLanguage L) V where
  rel R x := D.rel R x
  func
    | .cA, x => cAValue A D x
    | .cB, _ => ∅

/-- Target expansion used for B: both c_A and c_B are active. -/
def targetClosureExpansion
    (A : RelStructure L U) (B : RelStructure L V) :
    StructuralRamsey.Structure (closureLanguage L) V where
  rel R x := B.rel R x
  func
    | .cA, x => cAValue A B x
    | .cB, x => cBValue A B x

/-- Closed subsets of the elementary expansion are exactly pair-closed sets. -/
theorem elementaryClosure_isClosed_iff_pairClosed
    (A : RelStructure L U) (D : RelStructure L V)
    (S : Set V) :
    (elementaryClosureExpansion A D).IsClosed S ↔
      PairClosed A D S := by
  constructor
  · intro hClosed x hx y hy hxy a hxa hya z hz
    let t : Fin 2 → V := ![x, y]
    have ht : ∀ i, t i ∈ S := by
      intro i
      fin_cases i
      · exact hx
      · exact hy
    have hzOut :
        z ∈ (elementaryClosureExpansion A D).func .cA t := by
      exact ⟨hxy, a, hxa, hya, hz⟩
    exact hClosed .cA t ht hzOut
  · intro hPair F x hx z hz
    cases F with
    | cA =>
        rcases hz with ⟨hneq, a, h0, h1, hz⟩
        exact hPair (x 0) (hx 0) (x 1) (hx 1)
          hneq a h0 h1 hz
    | cB =>
        simpa [elementaryClosureExpansion] using hz

/-- Hence elementary function-closed subsets are exactly A-strongly induced
subsets of the relational reduct. -/
theorem elementaryClosure_isClosed_iff_aStrong
    (A : RelStructure L U) (D : RelStructure L V)
    (S : Set V) :
    (elementaryClosureExpansion A D).IsClosed S ↔
      AStrong A D S := by
  exact (elementaryClosure_isClosed_iff_pairClosed A D S).trans
    (pairClosed_iff_aStrong A D S)

/-- Closed subsets of the actual target expansion are exactly the
combinatorial target-closed subsets. -/
theorem targetClosure_isClosed_iff
    (A : RelStructure L U) (B : RelStructure L V)
    (S : Set V) :
    (targetClosureExpansion A B).IsClosed S ↔
      TargetClosed A B S := by
  constructor
  · intro hClosed
    constructor
    · intro x hx y hy hxy a hxa hya z hz
      let t : Fin 2 → V := ![x, y]
      have ht : ∀ i, t i ∈ S := by
        intro i
        fin_cases i
        · exact hx
        · exact hy
      have hzOut :
          z ∈ (targetClosureExpansion A B).func .cA t := by
        exact ⟨hxy, a, hxa, hya, hz⟩
      exact hClosed .cA t ht hzOut
    · intro x hx y hy z hz hdist hno
      apply Set.Subset.antisymm
      · exact Set.subset_univ S
      · intro w _
        let t : Fin 3 → V := ![x, y, z]
        have ht : ∀ i, t i ∈ S := by
          intro i
          fin_cases i
          · exact hx
          · exact hy
          · exact hz
        have hwOut :
            w ∈ (targetClosureExpansion A B).func .cB t := by
          exact ⟨hdist, hno⟩
        exact hClosed .cB t ht hwOut
  · intro hTarget F x hx z hz
    cases F with
    | cA =>
        rcases hz with ⟨hneq, a, h0, h1, hz⟩
        exact hTarget.1 (x 0) (hx 0) (x 1) (hx 1)
          hneq a h0 h1 hz
    | cB =>
        rcases hz with ⟨hdist, hno⟩
        have hall :=
          hTarget.2 (x 0) (hx 0) (x 1) (hx 1)
            (x 2) (hx 2) hdist hno
        rw [hall]
        exact Set.mem_univ z

/-- Actual function-closed nonempty subsets of the target expansion are exactly
singletons, A-copy carriers, or the whole target. -/
theorem targetClosure_closed_classify_nonempty
    {A : RelStructure L U} {B : RelStructure L V}
    {S : Set V}
    (hLinear : ALinear A B)
    (hClosed : (targetClosureExpansion A B).IsClosed S)
    (hne : S.Nonempty) :
    (∃ x : V, S = {x}) ∨
      (∃ a : Embedding A B, S = copyCarrier a) ∨
      S = Set.univ := by
  exact targetClosed_classify_nonempty hLinear
    ((targetClosure_isClosed_iff A B S).mp hClosed) hne

end StructuralRamsey.Girth
