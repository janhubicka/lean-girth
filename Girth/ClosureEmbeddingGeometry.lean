import Girth.ClosureExpansion
import Girth.ClosedCopyGeometry

/-! # Geometry of full embeddings of the closure target

Full embeddings have function-closed ranges, and closed sets pull back along
full embeddings.  Combined with the closure semantics from ClosureExpansion,
this gives the actual closed-copy geometry used in the Ramsey input.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v w
variable {L : RelLanguage.{u}}
variable {U V : Type v} {W : Type w}

/-- The relational reduct of a structure in the closure language. -/
def closureRelReduct
    (C : StructuralRamsey.Structure (closureLanguage L) W) :
    RelStructure L W where
  rel R x := C.rel R x

/-- Forget the closure functions from an embedding of the target expansion. -/
def targetEmbeddingRel
    {A : RelStructure L U} {B : RelStructure L V}
    {C : StructuralRamsey.Structure (closureLanguage L) W}
    (e : StructuralRamsey.Structure.Embedding
      (targetClosureExpansion A B) C) :
    RelStructure.Embedding B (closureRelReduct C) where
  toFun := e
  injective := e.injective
  map_rel_iff R x := by
    simpa [targetClosureExpansion, closureRelReduct] using
      e.map_rel_iff R x

/-- The range of every full relation/function embedding is function-closed. -/
theorem structureEmbedding_range_isClosed
    {K : StructuralRamsey.Language.{u}}
    {X : Type v} {Y : Type w}
    {M : StructuralRamsey.Structure K X}
    {N : StructuralRamsey.Structure K Y}
    (e : StructuralRamsey.Structure.Embedding M N) :
    N.IsClosed (Set.range e) := by
  classical
  intro F x hx y hy
  choose a ha using hx
  let xa : Fin (K.funcArity F) → X := a
  have hargs : e ∘ xa = x := by
    funext i
    exact ha i
  have hy' : y ∈ N.func F (e ∘ xa) := by
    rw [hargs]
    exact hy
  rw [← e.map_func F xa] at hy'
  rcases hy' with ⟨z, hz, hzy⟩
  exact ⟨z, hzy⟩

/-- Intersections of function-closed subsets are function-closed. -/
theorem structureIsClosed_inter
    {K : StructuralRamsey.Language.{u}}
    {X : Type v}
    {M : StructuralRamsey.Structure K X}
    {S T : Set X}
    (hS : M.IsClosed S) (hT : M.IsClosed T) :
    M.IsClosed (S ∩ T) := by
  intro F x hx y hy
  exact ⟨hS F x (fun i => (hx i).1) hy,
    hT F x (fun i => (hx i).2) hy⟩

/-- Preimages of closed sets under full embeddings are closed. -/
theorem structureIsClosed_preimage
    {K : StructuralRamsey.Language.{u}}
    {X : Type v} {Y : Type w}
    {M : StructuralRamsey.Structure K X}
    {N : StructuralRamsey.Structure K Y}
    (e : StructuralRamsey.Structure.Embedding M N)
    {T : Set Y} (hT : N.IsClosed T) :
    M.IsClosed {x | e x ∈ T} := by
  intro F x hx y hy
  have heyImg :
      e y ∈ N.func F (e ∘ x) := by
    have h :
        e y ∈ StructuralRamsey.Structure.imageSet e (M.func F x) :=
      ⟨y, hy, rfl⟩
    rw [e.map_func F x] at h
    exact h
  exact hT F (e ∘ x) (fun i => hx i) heyImg

/-- Cast a binary tuple to the definitional arity of c_A. -/
def cAInput
    (x : Fin 2 → W) :
    Fin ((closureLanguage L).funcArity (ClosureFunc.cA : ClosureFunc.{u})) → W := by
  simpa [closureLanguage] using x

/-- The ambient structure interprets c_A as the elementary A-closure
function on its relational reduct.  No restriction is placed on c_B. -/
def HasElementaryCA
    (A : RelStructure L U)
    (C : StructuralRamsey.Structure (closureLanguage L) W) : Prop :=
  ∀ x : Fin 2 → W,
    C.func (ClosureFunc.cA : ClosureFunc.{u}) (cAInput x) =
      cAValue A (closureRelReduct C) x

/-- The relational image of an expanded target embedding is pair-closed in
every ambient structure with the elementary c_A semantics. -/
theorem targetEmbedding_range_pairClosed
    {A : RelStructure L U} {B : RelStructure L V}
    {C : StructuralRamsey.Structure (closureLanguage L) W}
    (hCA : HasElementaryCA A C)
    (b : StructuralRamsey.Structure.Embedding
      (targetClosureExpansion A B) C) :
    PairClosed A (closureRelReduct C)
      (copyCarrier (targetEmbeddingRel b)) := by
  have hRange := structureEmbedding_range_isClosed b
  intro x hx y hy hxy a hxa hya z hz
  let t2 : Fin 2 → W := ![x, y]
  let t := cAInput t2
  have ht2 : ∀ i : Fin 2, t2 i ∈ Set.range b := by
    intro i
    fin_cases i
    · exact hx
    · exact hy
  have ht : ∀ i, t i ∈ Set.range b := by
    simpa [t, cAInput, closureLanguage] using ht2
  have hzValue : z ∈ cAValue A (closureRelReduct C) t2 :=
    ⟨hxy, a, hxa, hya, hz⟩
  have hzFunc :
      z ∈ C.func (ClosureFunc.cA : ClosureFunc.{u}) t := by
    rw [hCA t2]
    exact hzValue
  exact hRange (ClosureFunc.cA : ClosureFunc.{u}) t ht hzFunc

/-- Therefore every full embedding of the expanded target has an A-strong
relational image. -/
theorem targetEmbedding_range_aStrong
    {A : RelStructure L U} {B : RelStructure L V}
    {C : StructuralRamsey.Structure (closureLanguage L) W}
    (hCA : HasElementaryCA A C)
    (b : StructuralRamsey.Structure.Embedding
      (targetClosureExpansion A B) C) :
    AStrong A (closureRelReduct C)
      (copyCarrier (targetEmbeddingRel b)) := by
  exact (pairClosed_iff_aStrong A (closureRelReduct C)
    (copyCarrier (targetEmbeddingRel b))).mp
      (targetEmbedding_range_pairClosed hCA b)

/-- The intersection pulled back along one full target embedding is
target-closed. -/
theorem targetEmbedding_pullback_targetClosed
    {A : RelStructure L U} {B : RelStructure L V}
    {C : StructuralRamsey.Structure (closureLanguage L) W}
    (b c : StructuralRamsey.Structure.Embedding
      (targetClosureExpansion A B) C) :
    TargetClosed A B
      (pullbackIntersection (targetEmbeddingRel b) (targetEmbeddingRel c)) := by
  let S : Set V := {x | b x ∈ Set.range c}
  have hRangeC := structureEmbedding_range_isClosed c
  have hPre :
      (targetClosureExpansion A B).IsClosed S :=
    structureIsClosed_preimage b hRangeC
  have hTarget : TargetClosed A B S :=
    (targetClosure_isClosed_iff A B S).mp hPre
  have hEq :
      S =
        pullbackIntersection (targetEmbeddingRel b) (targetEmbeddingRel c) := by
    rfl
  rw [← hEq]
  exact hTarget

/-- Two distinct full embeddings of the expanded target have a controlled
relational intersection. -/
theorem targetEmbeddings_controlledIntersection
    {A : RelStructure L U} {B : RelStructure L V}
    {C : StructuralRamsey.Structure (closureLanguage L) W}
    [Finite V]
    (hBase : ALinear A B)
    (b c : StructuralRamsey.Structure.Embedding
      (targetClosureExpansion A B) C)
    (hne : ¬ SameCopy (targetEmbeddingRel b) (targetEmbeddingRel c)) :
    (copyCarrier (targetEmbeddingRel b) ∩
        copyCarrier (targetEmbeddingRel c)).Subsingleton ∨
      ∃ a : RelStructure.Embedding A (closureRelReduct C),
        copyCarrier (targetEmbeddingRel b) ∩
          copyCarrier (targetEmbeddingRel c) = copyCarrier a := by
  exact controlledIntersection_of_targetClosedPullback
    hBase (targetEmbeddingRel b) (targetEmbeddingRel c) hne
      (targetEmbedding_pullback_targetClosed b c)

end StructuralRamsey.Girth
