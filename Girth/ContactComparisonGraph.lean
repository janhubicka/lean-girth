import Girth.ContactSimplicial
import PartiteConstruction.Iterated.Ordered

/-! The comparison graph records exactly the existing order tuples.
No transitive or linear completion of the distinguished relation is taken. -/

namespace StructuralRamsey.Girth
open StructuralRamsey.RelStructure
universe u v
variable {L : RelLanguage.{u}} {U V W : Type v}

def contactComparisonGraph (C : RelStructure L.withOrder W) : SimpleGraph W where
  Adj x y := x ≠ y ∧ (C.rel (.inr ()) ![x,y] ∨ C.rel (.inr ()) ![y,x])
  symm := ⟨fun _ _ h => ⟨h.1.symm,h.2.symm⟩⟩
  loopless := {irrefl := fun _ h => h.1 rfl}

theorem contactComparisonGraph_embedding
    {C : RelStructure L.withOrder V} {D : RelStructure L.withOrder W}
    (f : Embedding C D) (x y : V) :
    (contactComparisonGraph D).Adj (f x) (f y) ↔
      (contactComparisonGraph C).Adj x y := by
  have ht (a b : V) : D.rel (.inr ()) ![f a,f b] ↔ C.rel (.inr ()) ![a,b] := by
    have he : f ∘ ![a,b] = ![f a,f b] := by
      funext i
      fin_cases i <;> rfl
    rw [← he]
    exact f.map_rel_iff (.inr ()) ![a,b]
  change (f x ≠ f y ∧ _) ↔ (x ≠ y ∧ _)
  rw [ht x y,ht y x]
  exact and_congr (not_congr f.injective.eq_iff) Iff.rfl

theorem contactComparisonGraph_ordered_adj (B : RelStructure L V) [LinearOrder V]
    (x y : V) : (contactComparisonGraph B.ordered).Adj x y ↔ x ≠ y := by
  change (x ≠ y ∧ (x < y ∨ y < x)) ↔ x ≠ y
  exact ⟨And.left,fun h => ⟨h,lt_or_gt_of_ne h⟩⟩

theorem contactComparisonGraph_embedding_ordered
    {B : RelStructure L V} [LinearOrder V] {C : RelStructure L.withOrder W}
    (b : Embedding B.ordered C) :
    ContactClique (contactComparisonGraph C) (Set.range b) := by
  rintro _ ⟨x,rfl⟩ _ ⟨y,rfl⟩ hne
  exact (contactComparisonGraph_embedding b x y).mpr
    ((contactComparisonGraph_ordered_adj B x y).mpr (fun h => hne (congrArg b h)))

theorem contactComparisonGraph_chordal_of_embedding
    {C : RelStructure L.withOrder V} {D : RelStructure L.withOrder W}
    (f : Embedding C D) (hD : ContactChordal (contactComparisonGraph D)) :
    ContactChordal (contactComparisonGraph C) := by
  intro n z hn hi hs
  obtain ⟨i,j,hij,hij',hji',hadj⟩ :=
    hD n (fun i => f (z i)) hn (f.injective.comp hi)
      (fun i => (contactComparisonGraph_embedding f _ _).mpr (hs i))
  exact ⟨i,j,hij,hij',hji',(contactComparisonGraph_embedding f _ _).mp hadj⟩

end StructuralRamsey.Girth
