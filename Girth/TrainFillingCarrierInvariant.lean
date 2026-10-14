import Girth.Berge

/-!
# Circulation Section 13: carrier geometry of a filling

A filling H of N specifies, for every actual new edge, a unique old
cover and requires (i) containment in that cover and (ii) coverage of
the complete old cover by new edges below it. Neither a Ramsey arrow
nor an appendix theorem is used.

The vertex carrier of a filled old edge (the corresponding first
wagon) is therefore EXACTLY the old edge. Hence wagon linearity
transfers without any cycle arguments, and strong inducedness of a
designated old copy transfers to the preimage of its old edges.

These are the two direct geometric reductions at the start of the
circulation "Filling preserves system girth" proof. The acceptable
big-cycle projection, A1--A3 and supreme lifting remain separate.
-/

namespace StructuralRamsey.Girth

universe v
variable {V : Type v}

/-- The concrete filling data: every actual edge has one specified old
cover, lies inside it, and the new edges assigned to each old cover
jointly cover all of its vertices. -/
structure TrainFilling (V : Type v) where
  oldEdges : Set (Set V)
  newEdges : Set (Set V)
  cover : {e : Set V // e ∈ newEdges} →
    {f : Set V // f ∈ oldEdges}
  contained : ∀ e, e.1 ⊆ (cover e).1
  covering : ∀ f, ∀ x ∈ f.1,
    ∃ e : {e : Set V // e ∈ newEdges},
      cover e = f ∧ x ∈ e.1

namespace TrainFilling

variable (F : TrainFilling V)

/-- The full vertex carrier of the wagon replacing an original edge. -/
def filledCarrier (f : {f : Set V // f ∈ F.oldEdges}) : Set V :=
  {x | ∃ e : {e : Set V // e ∈ F.newEdges},
    F.cover e = f ∧ x ∈ e.1}

/-- The replacement wagon has EXACTLY the old edge's vertex set. -/
theorem filledCarrier_eq (f : {f : Set V // f ∈ F.oldEdges}) :
    F.filledCarrier f = f.1 := by
  ext x
  constructor
  · rintro ⟨e, hparent, hx⟩
    have hxCover : x ∈ (F.cover e).1 := F.contained e hx
    simpa [hparent] using hxCover
  · intro hx
    exact F.covering f x hx

/-- Distinct original edges with linear intersection give distinct
filled wagon carriers with the same linear intersection parameter. -/
theorem filledCarrier_pairwise_subsingleton
    (hLinear : ∀ f g : {f : Set V // f ∈ F.oldEdges},
      f ≠ g → (f.1 ∩ g.1).Subsingleton) :
    ∀ f g : {f : Set V // f ∈ F.oldEdges},
      f ≠ g → (F.filledCarrier f ∩ F.filledCarrier g).Subsingleton := by
  intro f g hne
  rw [F.filledCarrier_eq f, F.filledCarrier_eq g]
  exact hLinear f g hne

/-- The designated target is the preimage of the old target edges
under the prescribed edge-cover map, as in the circulation filling. -/
def filledTargetEdges (oldTarget : Set (Set V)) :
    Set {e : Set V // e ∈ F.newEdges} :=
  {e | (F.cover e).1 ∈ oldTarget}

/-- Strong-inducedness as used by the circulation proof:
every ambient edge with two different vertices of X belongs to the
designated edge family. -/
def strongInduced (E target : Set (Set V)) (X : Set V) : Prop :=
  ∀ f : Set V, f ∈ E →
    (∃ x y : V, x ≠ y ∧ x ∈ f ∧ y ∈ f ∧ x ∈ X ∧ y ∈ X) →
    f ∈ target

/-- Strong inducedness survives a filling by containment:
a new edge meeting X twice has an old cover meeting X twice and
therefore belongs to the inverse-image designated target. -/
theorem filledTarget_strongInduced
    (oldTarget : Set (Set V)) (X : Set V)
    (hOld : strongInduced F.oldEdges oldTarget X) :
    ∀ e : {e : Set V // e ∈ F.newEdges},
      (∃ x y : V, x ≠ y ∧ x ∈ e.1 ∧ y ∈ e.1 ∧
        x ∈ X ∧ y ∈ X) →
      e ∈ F.filledTargetEdges oldTarget := by
  intro e ⟨x, y, hxy, hxe, hye, hxX, hyX⟩
  exact hOld (F.cover e).1 (F.cover e).2
    ⟨x, y, hxy, F.contained e hxe, F.contained e hye, hxX, hyX⟩

end TrainFilling
end StructuralRamsey.Girth
