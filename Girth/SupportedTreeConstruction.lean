import Girth.SupportedTree
import PartiteConstruction.Iterated.FreeAmalgam

/-! # Concrete construction steps for A-supported tree amalgams

This file packages the free-amalgam moves used when converting a forest of
copies into an A-supported tree amalgam.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {U V W : Type v}

/-- The one-vertex relational structure with the relation pattern of the
vertex `a` in `A`. -/
def pointAt
    (A : RelStructure L U) (a : U) :
    RelStructure L PUnit where
  rel R _ := A.rel R (fun _ => a)

/-- A point at position `a` embeds into any copy of `A` by sending its
unique vertex to that position. -/
def pointAtEmbedding
    (A : RelStructure L U)
    {T : RelStructure L W}
    (alpha : Embedding A T) (a : U) :
    Embedding (pointAt A a) T where
  toFun := fun _ => alpha a
  injective := by
    intro x y _
    exact Subsingleton.elim x y
  map_rel_iff := by
    intro R x
    change
      T.rel R ((fun _ : PUnit => alpha a) ∘ x) ↔
        A.rel R (fun _ => a)
    have htuple :
        ((fun _ : PUnit => alpha a) ∘ x) =
          (alpha.toFun ∘ (fun _ : Fin (L.arity R) => a)) := by
      funext k
      rfl
    rw [htuple]
    exact alpha.map_rel_iff R (fun _ => a)

/-- The canonical free amalgam over an A-copy is again an A-supported tree
amalgam. -/
theorem ASupportedTreeAmalgam.exists_freeGlueA
    {A : RelStructure L U} {B : RelStructure L V}
    {T : RelStructure L W}
    (hT : ASupportedTreeAmalgam A B W T)
    (fT : Embedding A T) (fB : Embedding A B) :
    ∃ (X : Type v) (S : RelStructure L X),
      ASupportedTreeAmalgam A B X S ∧
      ∃ iT : Embedding T S, ∃ iB : Embedding B S,
        IsFreeAmalgam fT fB iT iB := by
  let X := FreeAmalgam.Vertex A T B fT fB
  let S : RelStructure L X :=
    FreeAmalgam.amalgam A T B fT fB
  let iT : Embedding T S :=
    FreeAmalgam.leftEmbedding A T B fT fB
  let iB : Embedding B S :=
    FreeAmalgam.rightEmbedding A T B fT fB
  have hfree : IsFreeAmalgam fT fB iT iB :=
    FreeAmalgam.isFreeAmalgam A T B fT fB
  exact
    ⟨X, S,
      ASupportedTreeAmalgam.glueA hT fT fB iT iB hfree,
      iT, iB, hfree⟩

/-- The canonical free amalgam over a supported singleton is again an
A-supported tree amalgam. -/
theorem ASupportedTreeAmalgam.exists_freeGluePoint
    {A : RelStructure L U} {B : RelStructure L V}
    {T : RelStructure L W}
    {D : RelStructure L PUnit}
    (hT : ASupportedTreeAmalgam A B W T)
    (fT : Embedding D T) (fB : Embedding D B)
    (supportT : ∃ alpha : Embedding A T,
      ∀ d, ∃ a, fT d = alpha a)
    (supportB : ∃ alpha : Embedding A B,
      ∀ d, ∃ a, fB d = alpha a) :
    ∃ (X : Type v) (S : RelStructure L X),
      ASupportedTreeAmalgam A B X S ∧
      ∃ iT : Embedding T S, ∃ iB : Embedding B S,
        IsFreeAmalgam fT fB iT iB := by
  let X := FreeAmalgam.Vertex D T B fT fB
  let S : RelStructure L X :=
    FreeAmalgam.amalgam D T B fT fB
  let iT : Embedding T S :=
    FreeAmalgam.leftEmbedding D T B fT fB
  let iB : Embedding B S :=
    FreeAmalgam.rightEmbedding D T B fT fB
  have hfree : IsFreeAmalgam fT fB iT iB :=
    FreeAmalgam.isFreeAmalgam D T B fT fB
  exact
    ⟨X, S,
      ASupportedTreeAmalgam.gluePoint
        hT fT fB supportT supportB iT iB hfree,
      iT, iB, hfree⟩

/-- Special case of singleton gluing when the common point is the same
position `a` in two chosen A-copies. -/
theorem ASupportedTreeAmalgam.exists_freeGluePointAt
    {A : RelStructure L U} {B : RelStructure L V}
    {T : RelStructure L W}
    (hT : ASupportedTreeAmalgam A B W T)
    (alphaT : Embedding A T) (alphaB : Embedding A B)
    (a : U) :
    ∃ (X : Type v) (S : RelStructure L X),
      ASupportedTreeAmalgam A B X S ∧
      ∃ iT : Embedding T S, ∃ iB : Embedding B S,
        IsFreeAmalgam
          (pointAtEmbedding A alphaT a)
          (pointAtEmbedding A alphaB a)
          iT iB := by
  apply hT.exists_freeGluePoint
    (pointAtEmbedding A alphaT a)
    (pointAtEmbedding A alphaB a)
  · exact ⟨alphaT, fun _ => ⟨a, rfl⟩⟩
  · exact ⟨alphaB, fun _ => ⟨a, rfl⟩⟩


/-- Attach a completely disjoint fresh B-copy by inserting two bridge
B-copies.  The three singleton gluings use positions a0, a1, a0; the
inequality a0 != a1 ensures that the old target and the final B-copy remain
vertex-disjoint. -/
theorem ASupportedTreeAmalgam.exists_disjointCopyExtension
    {A : RelStructure L U} {B : RelStructure L V}
    {T : RelStructure L W}
    (hT : ASupportedTreeAmalgam A B W T)
    (alphaT : Embedding A T) (alphaB : Embedding A B)
    (a0 a1 : U) (hne : a0 ≠ a1) :
    ∃ (X : Type v) (S : RelStructure L X),
      ASupportedTreeAmalgam A B X S ∧
      ∃ iT : Embedding T S, ∃ iB : Embedding B S,
        Disjoint (Set.range iT) (Set.range iB) := by
  obtain ⟨X0, S0, hS0, iT0, iB0, _hfree0⟩ :=
    hT.exists_freeGluePointAt alphaT alphaB a0
  let alpha0 : Embedding A S0 := iB0.comp alphaB
  obtain ⟨X1, S1, hS1, iS01, iB1, hfree1⟩ :=
    hS0.exists_freeGluePointAt alpha0 alphaB a1
  let alpha1 : Embedding A S1 := iB1.comp alphaB
  obtain ⟨X2, S2, hS2, iS12, iB2, hfree2⟩ :=
    hS1.exists_freeGluePointAt alpha1 alphaB a0
  let iT : Embedding T S2 := iS12.comp (iS01.comp iT0)
  have hDisj : Disjoint (Set.range iT) (Set.range iB2) := by
    rw [Set.disjoint_left]
    intro z hzT hzB
    rcases hzT with ⟨t, ht⟩
    rcases hzB with ⟨b, hb⟩
    have heq2 :
        iS12 (iS01 (iT0 t)) = iB2 b := by
      change iT t = iB2 b
      exact ht.trans hb.symm
    obtain ⟨d2, hleft2, _hright2⟩ :=
      (hfree2.overlap (iS01 (iT0 t)) b).mp heq2
    have heq1 :
        iS01 (iT0 t) = iB1 (alphaB a0) := by
      calc
        iS01 (iT0 t) =
            pointAtEmbedding A alpha1 a0 d2 := hleft2
        _ = alpha1 a0 := rfl
        _ = iB1 (alphaB a0) := rfl
    obtain ⟨d1, _hleft1, hright1⟩ :=
      (hfree1.overlap (iT0 t) (alphaB a0)).mp heq1
    have hpos : alphaB a0 = alphaB a1 := by
      calc
        alphaB a0 =
            pointAtEmbedding A alphaB a1 d1 := hright1
        _ = alphaB a1 := rfl
    exact hne (alphaB.injective hpos)
  exact ⟨X2, S2, hS2, iT, iB2, hDisj⟩

/-- No relation tuple supported on the two indicated images mixes the two
sides.  This is the exact condition needed to embed a disjoint relational
union into a larger supported tree amalgam. -/
def RelationsSplitBetweenImages
    {B : RelStructure L V} {T : RelStructure L W}
    {X : Type v} {S : RelStructure L X}
    (iT : Embedding T S) (iB : Embedding B S) : Prop :=
  ∀ sym z, S.rel sym z →
    (∀ k, z k ∈ Set.range iT ∪ Set.range iB) →
      (∀ k, z k ∈ Set.range iT) ∨
        (∀ k, z k ∈ Set.range iB)

/-- The three-point bridge construction does more than make the old target
and the final B-copy vertex-disjoint: every relation whose vertices lie in
their union is wholly contained in one side. -/
theorem ASupportedTreeAmalgam.exists_disjointCopyExtension_split
    {A : RelStructure L U} {B : RelStructure L V}
    {T : RelStructure L W}
    (hT : ASupportedTreeAmalgam A B W T)
    (alphaT : Embedding A T) (alphaB : Embedding A B)
    (a0 a1 : U) (hne : a0 ≠ a1) :
    ∃ (X : Type v) (S : RelStructure L X),
      ASupportedTreeAmalgam A B X S ∧
      ∃ iT : Embedding T S, ∃ iB : Embedding B S,
        Disjoint (Set.range iT) (Set.range iB) ∧
          RelationsSplitBetweenImages iT iB := by
  obtain ⟨X0, S0, hS0, iT0, iB0, hfree0⟩ :=
    hT.exists_freeGluePointAt alphaT alphaB a0
  let alpha0 : Embedding A S0 := iB0.comp alphaB
  obtain ⟨X1, S1, hS1, iS01, iB1, hfree1⟩ :=
    hS0.exists_freeGluePointAt alpha0 alphaB a1
  let alpha1 : Embedding A S1 := iB1.comp alphaB
  obtain ⟨X2, S2, hS2, iS12, iB2, hfree2⟩ :=
    hS1.exists_freeGluePointAt alpha1 alphaB a0
  let iT : Embedding T S2 := iS12.comp (iS01.comp iT0)
  have hDisj : Disjoint (Set.range iT) (Set.range iB2) := by
    rw [Set.disjoint_left]
    intro z hzT hzB
    rcases hzT with ⟨t, ht⟩
    rcases hzB with ⟨b, hb⟩
    have heq2 :
        iS12 (iS01 (iT0 t)) = iB2 b := by
      change iT t = iB2 b
      exact ht.trans hb.symm
    obtain ⟨d2, hleft2, _hright2⟩ :=
      (hfree2.overlap (iS01 (iT0 t)) b).mp heq2
    have heq1 :
        iS01 (iT0 t) = iB1 (alphaB a0) := by
      calc
        iS01 (iT0 t) =
            pointAtEmbedding A alpha1 a0 d2 := hleft2
        _ = alpha1 a0 := rfl
        _ = iB1 (alphaB a0) := rfl
    obtain ⟨d1, _hleft1, hright1⟩ :=
      (hfree1.overlap (iT0 t) (alphaB a0)).mp heq1
    have hpos : alphaB a0 = alphaB a1 := by
      calc
        alphaB a0 =
            pointAtEmbedding A alphaB a1 d1 := hright1
        _ = alphaB a1 := rfl
    exact hne (alphaB.injective hpos)
  have hSplit : RelationsSplitBetweenImages iT iB2 := by
    intro sym z hz hUnion
    rcases (hfree2.rel_iff sym z).mp hz with hOld2 | hFresh2
    · rcases hOld2 with ⟨y, hy, hzy⟩
      rcases (hfree1.rel_iff sym y).mp hy with hOld1 | hFresh1
      · rcases hOld1 with ⟨w, _hw, hyw⟩
        left
        intro k
        rcases hUnion k with hTk | hBk
        · exact hTk
        · rcases hBk with ⟨b, hb⟩
          exfalso
          have hzOld :
              iS12 (iS01 (w k)) = z k := by
            calc
              iS12 (iS01 (w k)) = iS12 (y k) := by
                rw [congrFun hyw k]
              _ = z k := (congrFun hzy k).symm
          have heq2 :
              iS12 (iS01 (w k)) = iB2 b :=
            hzOld.trans hb.symm
          obtain ⟨d2, hleft2, _hright2⟩ :=
            (hfree2.overlap (iS01 (w k)) b).mp heq2
          have heq1 :
              iS01 (w k) = iB1 (alphaB a0) := by
            calc
              iS01 (w k) =
                  pointAtEmbedding A alpha1 a0 d2 := hleft2
              _ = alpha1 a0 := rfl
              _ = iB1 (alphaB a0) := rfl
          obtain ⟨d1, _hleft1, hright1⟩ :=
            (hfree1.overlap (w k) (alphaB a0)).mp heq1
          have hpos : alphaB a0 = alphaB a1 := by
            calc
              alphaB a0 =
                  pointAtEmbedding A alphaB a1 d1 := hright1
              _ = alphaB a1 := rfl
          exact hne (alphaB.injective hpos)
      · rcases hFresh1 with ⟨w, _hw, hyw⟩
        right
        intro k
        rcases hUnion k with hTk | hBk
        · rcases hTk with ⟨t, ht⟩
          exfalso
          have heq1 :
              iS01 (iT0 t) = iB1 (w k) := by
            apply iS12.injective
            calc
              iS12 (iS01 (iT0 t)) = iT t := rfl
              _ = z k := ht
              _ = iS12 (y k) := congrFun hzy k
              _ = iS12 (iB1 (w k)) := by
                rw [congrFun hyw k]
          obtain ⟨d1, hleft1, _hright1⟩ :=
            (hfree1.overlap (iT0 t) (w k)).mp heq1
          have heq0 :
              iT0 t = iB0 (alphaB a1) := by
            calc
              iT0 t =
                  pointAtEmbedding A alpha0 a1 d1 := hleft1
              _ = alpha0 a1 := rfl
              _ = iB0 (alphaB a1) := rfl
          obtain ⟨d0, _hleft0, hright0⟩ :=
            (hfree0.overlap t (alphaB a1)).mp heq0
          have hpos : alphaB a1 = alphaB a0 := by
            calc
              alphaB a1 =
                  pointAtEmbedding A alphaB a0 d0 := hright0
              _ = alphaB a0 := rfl
          exact hne (alphaB.injective hpos).symm
        · exact hBk
    · rcases hFresh2 with ⟨w, _hw, hzw⟩
      right
      intro k
      exact ⟨w k, (congrFun hzw k).symm⟩
  exact ⟨X2, S2, hS2, iT, iB2, hDisj, hSplit⟩

end StructuralRamsey.Girth
