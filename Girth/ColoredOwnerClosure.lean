import Girth.Support
import Girth.ClosureEmbeddingGeometry
import PartiteConstruction.Structure.Basic
import Mathlib.Tactic

set_option autoImplicit false

/-!
# Owner-closure expansion for the coloured edge Ramsey input

For one support edge A, add two kinds of set-valued functions.

* pair: on two distinct edge vertices its value is the whole edge.
  Thus every full expanded A-copy is strongly induced among expanded
  A-copies.
* owner j: if the input vertex lies in the blocked part named by j,
  its value is the whole edge; otherwise its value is the singleton input.
  Thus two distinct expanded A-copies cannot share a vertex in a blocked
  part.

These are purely local consequences of FULL function-language embeddings.
No ambient canonical semantics and no Ramsey theorem are used here.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey
open StructuralRamsey.RelStructure

universe u v w
variable {L : RelLanguage.{u}}
variable {U P J : Type u} {X : Type v} {Y : Type w}

/-- Pair closure together with one unary owner symbol for every blocked-part
name. -/
inductive OwnerClosureFunc (J : Type u) : Type u
  | pair
  | owner (j : J)

/-- Keep the old relations and add the owner-closure functions. -/
def ownerClosureLanguage (L : RelLanguage.{u}) (J : Type u) :
    StructuralRamsey.Language.{u} where
  RelSymbol := L.Symbol
  FuncSymbol := OwnerClosureFunc J
  relArity := L.arity
  funcArity
    | .pair => 2
    | .owner _ => 1

/-- The expansion of the ONE edge A. Pair closure and the relevant owner
fibre both return the complete edge carrier. On a vertex from another part,
an owner function returns only that vertex. -/
def ownerEdgeExpansion
    (A : RelStructure L U) (part : U → P) (ownerPart : J → P)
    [DecidableEq U] [DecidableEq P] :
    StructuralRamsey.Structure (ownerClosureLanguage L J) U where
  rel R x := A.rel R x
  func
    | .pair, x => if x 0 = x 1 then ∅ else Set.univ
    | .owner j, x =>
        if part (x 0) = ownerPart j then Set.univ else {x 0}

namespace OwnerEdgeExpansion

variable (A : RelStructure L U) (part : U → P) (ownerPart : J → P)
variable [DecidableEq U] [DecidableEq P]

local notation "Ahat" => ownerEdgeExpansion A part ownerPart

@[simp] theorem pair_value_of_ne (x y : U) (hxy : x ≠ y) :
    Ahat.func (.pair : OwnerClosureFunc J) ![x,y] = Set.univ := by
  simp [ownerEdgeExpansion, hxy]

@[simp] theorem owner_value_of_part (j : J) (x : U)
    (hx : part x = ownerPart j) :
    Ahat.func (.owner j) (fun _ : Fin 1 => x) = Set.univ := by
  simp [ownerEdgeExpansion, hx]

@[simp] theorem owner_value_of_other (j : J) (x : U)
    (hx : part x ≠ ownerPart j) :
    Ahat.func (.owner j) (fun _ : Fin 1 => x) = {x} := by
  simp [ownerEdgeExpansion, hx]

private theorem imageSet_univ_eq_range (f : U → X) :
    StructuralRamsey.Structure.imageSet f Set.univ = Set.range f := by
  ext x
  constructor
  · rintro ⟨u, _, rfl⟩
    exact ⟨u, rfl⟩
  · rintro ⟨u, rfl⟩
    exact ⟨u, Set.mem_univ u, rfl⟩

private theorem imageSet_singleton (f : U → X) (u : U) :
    StructuralRamsey.Structure.imageSet f {u} = {f u} := by
  ext x
  constructor
  · rintro ⟨z, hz, rfl⟩
    simpa using hz
  · intro hx
    have : x = f u := by simpa using hx
    subst x
    exact ⟨u, by simp, rfl⟩

/-- Every full expanded edge copy is pair-closed in an arbitrary ambient
functional structure: any closed set containing two distinct vertices of
the edge contains the whole edge. -/
theorem range_subset_of_closed_of_two_mem
    {C : StructuralRamsey.Structure (ownerClosureLanguage L J) X}
    (e : StructuralRamsey.Structure.Embedding Ahat C)
    (S : Set X) (hS : C.IsClosed S)
    (u v : U) (huv : u ≠ v)
    (hu : e u ∈ S) (hv : e v ∈ S) :
    Set.range e ⊆ S := by
  intro z hz
  obtain ⟨w, rfl⟩ := hz
  have hArgs : ∀ i : Fin 2, (![e u, e v] : Fin 2 → X) i ∈ S := by
    intro i
    fin_cases i
    · exact hu
    · exact hv
  have hOut : e w ∈ C.func (.pair : OwnerClosureFunc J) ![e u,e v] := by
    have hMap := e.map_func (.pair : OwnerClosureFunc J) ![u,v]
    have hw : e w ∈
        StructuralRamsey.Structure.imageSet e
          (Ahat.func (.pair : OwnerClosureFunc J) ![u,v]) := by
      rw [pair_value_of_ne A part ownerPart u v huv]
      exact ⟨w, Set.mem_univ w, rfl⟩
    have hComp : e ∘ ![u,v] = (![e u,e v] : Fin 2 → X) := by
      funext i
      fin_cases i <;> rfl
    rw [hMap, hComp] at hw
    exact hw
  exact hS (.pair : OwnerClosureFunc J) ![e u,e v] hArgs hOut

/-- In particular, if two points of one expanded edge lie in the closed range
of any full functional embedding, the whole edge lies in that range. -/
theorem range_subset_of_embedding_range_of_two_mem
    {B : StructuralRamsey.Structure (ownerClosureLanguage L J) Y}
    {C : StructuralRamsey.Structure (ownerClosureLanguage L J) X}
    (e : StructuralRamsey.Structure.Embedding Ahat C)
    (b : StructuralRamsey.Structure.Embedding B C)
    (u v : U) (huv : u ≠ v)
    (hu : e u ∈ Set.range b) (hv : e v ∈ Set.range b) :
    Set.range e ⊆ Set.range b := by
  exact range_subset_of_closed_of_two_mem A part ownerPart e
    (Set.range b) (structureEmbedding_range_isClosed b)
    u v huv hu hv

/-- A shared vertex occurring in a blocked source part forces two full
expanded A-copies to have the same entire physical carrier. -/
theorem same_range_of_shared_blocked
    [Nontrivial U]
    {C : StructuralRamsey.Structure (ownerClosureLanguage L J) X}
    (e f : StructuralRamsey.Structure.Embedding Ahat C)
    (j : J) (u v : U)
    (huPart : part u = ownerPart j)
    (hshared : e u = f v) :
    Set.range e = Set.range f := by
  have heMap := e.map_func (.owner j) (fun _ : Fin 1 => u)
  have heRange :
      C.func (.owner j) (fun _ : Fin 1 => e u) = Set.range e := by
    rw [← heMap, owner_value_of_part A part ownerPart j u huPart,
      imageSet_univ_eq_range]
  by_cases hvPart : part v = ownerPart j
  · have hfMap := f.map_func (.owner j) (fun _ : Fin 1 => v)
    have hfRange :
        C.func (.owner j) (fun _ : Fin 1 => f v) = Set.range f := by
      rw [← hfMap, owner_value_of_part A part ownerPart j v hvPart,
        imageSet_univ_eq_range]
    calc
      Set.range e = C.func (.owner j) (fun _ : Fin 1 => e u) := heRange.symm
      _ = C.func (.owner j) (fun _ : Fin 1 => f v) := by rw [hshared]
      _ = Set.range f := hfRange
  · have hfMap := f.map_func (.owner j) (fun _ : Fin 1 => v)
    have hfSingleton :
        C.func (.owner j) (fun _ : Fin 1 => f v) = {f v} := by
      rw [← hfMap, owner_value_of_other A part ownerPart j v hvPart,
        imageSet_singleton]
    obtain ⟨w, hwu⟩ := exists_ne u
    have hew : e w ∈ Set.range e := ⟨w, rfl⟩
    have hewSingleton : e w ∈ ({f v} : Set X) := by
      rw [← hfSingleton, ← hshared, heRange]
      exact hew
    have hewv : e w = f v := by
      simpa using hewSingleton
    have heq : e w = e u := hewv.trans hshared.symm
    exact False.elim (hwu (e.injective heq))

/-- Hence two physically distinct expanded edges cannot meet at any source
vertex whose part is one of the blocked owner parts. -/
theorem no_shared_blocked_of_distinct_ranges
    [Nontrivial U]
    {C : StructuralRamsey.Structure (ownerClosureLanguage L J) X}
    (e f : StructuralRamsey.Structure.Embedding Ahat C)
    (hne : Set.range e ≠ Set.range f)
    (u v : U) (hshared : e u = f v) (j : J) :
    part u ≠ ownerPart j := by
  intro hu
  exact hne (same_range_of_shared_blocked A part ownerPart e f j u v hu hshared)

end OwnerEdgeExpansion
end StructuralRamsey.Girth
