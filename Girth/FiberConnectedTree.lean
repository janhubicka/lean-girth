import Girth.ForestDeletionGeometry

/-! # Trees preserving fibres of a finite labelling

The one-edge deletion argument eventually reduces to reconnecting the connected
components of a forest. Components carrying the same attachment label must
remain connected. This file isolates the finite graph lemma needed for that
step.

Let the auxiliary graph connect exactly pairs with the same label. Mathlib's
maximal-acyclic theorem extends the empty graph to a spanning forest with the
same reachability as this auxiliary graph. Extending that forest once more to a
spanning tree preserves the fibre connections.
-/

namespace StructuralRamsey.Girth

universe v
variable {C A : Type v}

/-- The graph whose connected components are exactly the nonempty fibres of
`label`. -/
def fiberCliqueGraph (label : C → A) : SimpleGraph C where
  Adj u v := u ≠ v ∧ label u = label v
  symm := {
    symm := by
      intro u v h
      exact ⟨h.1.symm, h.2.symm⟩ }
  loopless := {
    irrefl := by
      intro u h
      exact h.1 rfl }

/-- A walk in the fibre graph never changes its label. -/
theorem fiberCliqueGraph_walk_support_label
    (label : C → A)
    {u v : C}
    (p : (fiberCliqueGraph label).Walk u v)
    {x : C}
    (hx : x ∈ p.support) :
    label x = label u := by
  induction p with
  | nil =>
      simpa using hx
  | @cons u w v huw p ih =>
      simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at hx
      rcases hx with rfl | hx
      · rfl
      · have hwu : label w = label u := huw.2.symm
        exact (ih hx).trans hwu

/-- Equal labels are reachable in the fibre graph. -/
theorem fiberCliqueGraph_reachable_of_label_eq
    (label : C → A)
    {u v : C}
    (h : label u = label v) :
    (fiberCliqueGraph label).Reachable u v := by
  by_cases huv : u = v
  · subst v
    exact SimpleGraph.Reachable.refl _
  · exact (show (fiberCliqueGraph label).Adj u v from ⟨huv, h⟩).reachable

/-- Every finite nonempty labelled set admits a tree in which every label fibre
is preconnected. -/
theorem exists_tree_fibers_preconnected
    [Finite C] [Nonempty C]
    (label : C → A) :
    ∃ T : SimpleGraph C, T.IsTree ∧
      ∀ a : A, (T.induce {c : C | label c = a}).Preconnected := by
  classical
  let K : SimpleGraph C := fiberCliqueGraph label
  obtain ⟨F, _hBotF, hFK, hFacyc, hReach⟩ :=
    K.exists_isAcyclic_reachable_eq_le_of_le_of_isAcyclic
      (H := (⊥ : SimpleGraph C)) bot_le SimpleGraph.isAcyclic_bot
  have hTop : (⊤ : SimpleGraph C).Connected :=
    SimpleGraph.connected_top
  obtain ⟨T, hFT, _hTTop, hT⟩ :=
    hTop.exists_isTree_le_of_le_of_isAcyclic
      (H := F) le_top hFacyc
  refine ⟨T, hT, ?_⟩
  intro a c d
  have hKreach :
      K.Reachable c.1 d.1 := by
    exact fiberCliqueGraph_reachable_of_label_eq
      label (c.2.trans d.2.symm)
  have hFreach : F.Reachable c.1 d.1 := by
    rw [hReach]
    exact hKreach
  rcases hFreach with ⟨p⟩
  let pK := p.mapLe hFK
  let pT := p.mapLe hFT
  have hpLabel :
      ∀ x ∈ p.support, label x = a := by
    intro x hx
    have hxK : x ∈ pK.support := by
      simpa [pK] using hx
    exact
      (fiberCliqueGraph_walk_support_label label pK hxK).trans c.2
  have hpTLabel :
      ∀ x ∈ pT.support, x ∈ {z : C | label z = a} := by
    intro x hx
    have hxP : x ∈ p.support := by
      simpa [pT] using hx
    exact hpLabel x hxP
  let q := pT.induce {z : C | label z = a} hpTLabel
  have hq := q.reachable
  convert hq using 1 <;> apply Subtype.ext <;> rfl

end StructuralRamsey.Girth
