import Girth.ForestDisjoint
import Girth.InitialACopyGeometry
import Girth.InitialComponentForest

/-! # Forest completion for the initial picture

The initial picture is a disjoint union of B-components.  Every ambient
irreducible A-copy factors through exactly one component.  We add every
designated B-component as a center and attach the selected A-copies in that
component as one-edge leaves.  The local stars are forests by A-linearity and
the component forests combine because the outer components are disjoint.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {UA VB P I J : Type v}

/-- Same-copy equality is preserved by composition with an ambient embedding. -/
theorem sameCopy_comp_of_sameCopy
    {X Y Z : Type v}
    {A : RelStructure L X} {B : RelStructure L Y}
    {C : RelStructure L Z}
    (i : Embedding B C)
    {e f : Embedding A B}
    (h : SameCopy e f) :
    SameCopy (i.comp e) (i.comp f) := by
  change Set.range (i.comp e) = Set.range (i.comp f)
  apply Set.Subset.antisymm
  · rintro x ⟨a, rfl⟩
    have ha : e a ∈ copyCarrier f := by
      rw [← h]
      exact ⟨a, rfl⟩
    rcases ha with ⟨b, hb⟩
    exact ⟨b, congrArg i hb⟩
  · rintro x ⟨a, rfl⟩
    have ha : f a ∈ copyCarrier e := by
      rw [h]
      exact ⟨a, rfl⟩
    rcases ha with ⟨b, hb⟩
    exact ⟨b, congrArg i hb⟩

/-- A-linearity of B passes to the disjoint-union initial picture. -/
theorem initialPicture_aLinear
    (A : RelStructure L UA)
    (hA : A.Irreducible)
    (B : RelStructure L VB)
    (β : I → VB ↪ P)
    [Nonempty I]
    (hB : ALinear A B) :
    ALinear A
      (StructuralRamsey.Partite.Initial.picture B β).toRelStructure := by
  intro e f hne
  obtain ⟨i, eB, he⟩ :=
    initialACopy_factors_component A hA B β e
  obtain ⟨j, fB, hf⟩ :=
    initialACopy_factors_component A hA B β f
  rw [he, hf] at hne ⊢
  by_cases hij : i = j
  · subst j
    let copy : Embedding B
        (StructuralRamsey.Partite.Initial.picture B β).toRelStructure :=
      StructuralRamsey.Partite.Initial.copyEmbedding B β i
    have hneB : ¬ SameCopy eB fB := by
      intro hs
      exact hne (sameCopy_comp_of_sameCopy copy hs)
    have hsmall := hB eB fB hneB
    intro x hx y hy
    rcases hx.1 with ⟨u, hu⟩
    rcases hx.2 with ⟨v, hv⟩
    rcases hy.1 with ⟨u', hu'⟩
    rcases hy.2 with ⟨v', hv'⟩
    have hxB : eB u = fB v := by
      apply copy.injective
      exact hu.trans hv.symm
    have hyB : eB u' = fB v' := by
      apply copy.injective
      exact hu'.trans hv'.symm
    have hxInner :
        eB u ∈ copyCarrier eB ∩ copyCarrier fB :=
      ⟨⟨u, rfl⟩, ⟨v, hxB.symm⟩⟩
    have hyInner :
        eB u' ∈ copyCarrier eB ∩ copyCarrier fB :=
      ⟨⟨u', rfl⟩, ⟨v', hyB.symm⟩⟩
    have hEq := hsmall hxInner hyInner
    calc
      x = copy (eB u) := hu.symm
      _ = copy (eB u') := congrArg copy hEq
      _ = y := hu'
  · intro x hx y hy
    exfalso
    rcases hx.1 with ⟨u, hu⟩
    rcases hx.2 with ⟨v, hv⟩
    have hidx : i = j := by
      exact congrArg Prod.fst (hu.trans hv.symm)
    exact hij hidx

/-- Chosen owner of an A-copy in the initial picture. -/
noncomputable def initialACopyOwner
    (A : RelStructure L UA)
    (hA : A.Irreducible)
    (B : RelStructure L VB)
    (β : I → VB ↪ P)
    [Nonempty I]
    (a : Embedding A
      (StructuralRamsey.Partite.Initial.picture B β).toRelStructure) : I :=
  Classical.choose (initialACopy_factors_component A hA B β a)

/-- Chosen factor of an A-copy through its owner B-component. -/
noncomputable def initialACopyFactor
    (A : RelStructure L UA)
    (hA : A.Irreducible)
    (B : RelStructure L VB)
    (β : I → VB ↪ P)
    [Nonempty I]
    (a : Embedding A
      (StructuralRamsey.Partite.Initial.picture B β).toRelStructure) :
    Embedding A B :=
  Classical.choose
    (Classical.choose_spec
      (initialACopy_factors_component A hA B β a))

theorem initialACopy_factor_spec
    (A : RelStructure L UA)
    (hA : A.Irreducible)
    (B : RelStructure L VB)
    (β : I → VB ↪ P)
    [Nonempty I]
    (a : Embedding A
      (StructuralRamsey.Partite.Initial.picture B β).toRelStructure) :
    a =
      (StructuralRamsey.Partite.Initial.copyEmbedding B β
        (initialACopyOwner A hA B β a)).comp
        (initialACopyFactor A hA B β a) :=
  Classical.choose_spec
    (Classical.choose_spec
      (initialACopy_factors_component A hA B β a))

/-- Local completion labels at component i: the B-center plus all selected
A-copies owned by i. -/
def InitialCompletionLabel
    (A : RelStructure L UA)
    (hA : A.Irreducible)
    (B : RelStructure L VB)
    (β : I → VB ↪ P)
    [Nonempty I]
    (a : J → Embedding A
      (StructuralRamsey.Partite.Initial.picture B β).toRelStructure)
    (i : I) : Type v :=
  Option {j : J // initialACopyOwner A hA B β (a j) = i}

/-- Hypergraph member represented by one initial-completion label. -/
def initialCompletionPiece
    (A : RelStructure L UA)
    (hA : A.Irreducible)
    (B : RelStructure L VB)
    (β : I → VB ↪ P)
    [Nonempty I]
    (a : J → Embedding A
      (StructuralRamsey.Partite.Initial.picture B β).toRelStructure)
    (i : I) :
    InitialCompletionLabel A hA B β a i →
      HypergraphPiece (I × VB)
  | none =>
      bSupportPiece A
        (StructuralRamsey.Partite.Initial.copyEmbedding B β i)
  | some j =>
      oneEdgePiece (copyCarrier (a j.1))

/-- Exact forest-completion statement for the initial picture: adding all
designated B-components to any finite pairwise-distinct family of A-copies
produces a forest. -/
theorem initialPicture_forestCompletion
    (A : RelStructure L UA)
    (hA : A.Irreducible)
    (B : RelStructure L VB)
    (β : I → VB ↪ P)
    [Fintype I] [Nonempty I]
    [Fintype J]
    (hBLinear : ALinear A B)
    (a : J → Embedding A
      (StructuralRamsey.Partite.Initial.picture B β).toRelStructure)
    (hDistinct :
      ∀ ⦃j k : J⦄, j ≠ k → ¬ SameCopy (a j) (a k)) :
    ForestOfCopies
      (fun z : Sigma (InitialCompletionLabel A hA B β a) =>
        initialCompletionPiece A hA B β a z.1 z.2) := by
  classical
  let R :=
    (StructuralRamsey.Partite.Initial.picture B β).toRelStructure
  let b : I → Embedding B R :=
    fun i => StructuralRamsey.Partite.Initial.copyEmbedding B β i
  let Pouter : I → HypergraphPiece (I × VB) :=
    fun i => bSupportPiece A (b i)
  have hDisj :
      ∀ ⦃i k : I⦄, i ≠ k →
        Disjoint (Pouter i).carrier (Pouter k).carrier := by
    intro i k hik
    rw [Set.disjoint_left]
    intro x hxi hxk
    rcases hxi with ⟨u, hu⟩
    rcases hxk with ⟨v, hv⟩
    have hidx : i = k :=
      congrArg Prod.fst (hu.trans hv.symm)
    exact hik hidx
  have hInitLinear : ALinear A R :=
    initialPicture_aLinear A hA B β hBLinear
  have hLocal :
      ∀ i : I,
        ForestOfCopies
          (initialCompletionPiece A hA B β a i) := by
    intro i
    let Ji := {j : J // initialACopyOwner A hA B β (a j) = i}
    have hSub :
        ∀ j : Ji,
          copyCarrier (a j.1) ⊆ copyCarrier (b i) := by
      intro j x hx
      rcases hx with ⟨u, rfl⟩
      let aB :=
        initialACopyFactor A hA B β (a j.1)
      refine ⟨aB u, ?_⟩
      have hs :=
        initialACopy_factor_spec A hA B β (a j.1)
      have hu := congrArg (fun e : Embedding A R => e u) hs
      change a j.1 u = b (initialACopyOwner A hA B β (a j.1)) (aB u) at hu
      simpa [j.2, b, aB] using hu.symm
    have hDistinctLocal :
        ∀ ⦃j k : Ji⦄, j ≠ k →
          ¬ SameCopy (a j.1) (a k.1) := by
      intro j k hjk
      apply hDistinct
      intro hval
      apply hjk
      exact Subtype.ext hval
    have hFam :
        initialCompletionPiece A hA B β a i =
          centerWithEdgeLeaves
            (bSupportPiece A (b i))
            (fun j : Ji => copyCarrier (a j.1)) := by
      funext k
      cases k <;> rfl
    rw [hFam]
    exact
      forest_bSupport_with_aLeaves
        (A := A) (B := B)
        (b i)
        (fun j : Ji => a j.1)
        hInitLinear hSub hDistinctLocal
  have hContain :
      ∀ i (k : InitialCompletionLabel A hA B β a i),
        (initialCompletionPiece A hA B β a i k).carrier ⊆
          (Pouter i).carrier := by
    intro i k
    cases k with
    | none =>
        exact Set.Subset.rfl
    | some j =>
        intro x hx
        change x ∈ copyCarrier (a j.1) at hx
        rcases hx with ⟨u, rfl⟩
        let aB :=
          initialACopyFactor A hA B β (a j.1)
        refine ⟨aB u, ?_⟩
        have hs :=
          initialACopy_factor_spec A hA B β (a j.1)
        have hu := congrArg (fun e : Embedding A R => e u) hs
        change a j.1 u =
          b (initialACopyOwner A hA B β (a j.1)) (aB u) at hu
        simpa [j.2, Pouter, b, aB] using hu.symm
  letI (i : I) :
      Fintype (InitialCompletionLabel A hA B β a i) := by
    classical
    change Fintype
      (Option {j : J // initialACopyOwner A hA B β (a j) = i})
    infer_instance
  letI (i : I) :
      Nonempty (InitialCompletionLabel A hA B β a i) :=
    ⟨none⟩
  exact
    forestOfCopies_lift_disjoint
      hDisj hLocal hContain

end StructuralRamsey.Girth
