import Girth.ForestDeletionGeometry

/-! # Trees preserving fibres of a finite labelling

The one-edge deletion argument eventually reduces to reconnecting the connected
components of a forest. Components carrying the same attachment label must
remain connected. This file isolates the finite graph lemma needed for that
step: every finite nonempty labelled set admits a tree in which each label
fibre induces a preconnected subgraph.

The proof starts with the disjoint union of stars inside the fibres and extends
that acyclic graph to a spanning tree.
-/

namespace StructuralRamsey.Girth

universe v
variable {C A : Type v}

/-- The disjoint union of stars selected by a fibrewise centre map. -/
def fiberStarGraph (label : C → A) (center : C → C) : SimpleGraph C where
  Adj u v :=
    u ≠ v ∧ label u = label v ∧
      (u = center u ∨ v = center v)
  symm := by
    intro u v h
    rcases h with ⟨hne, hlab, hu | hv⟩
    · exact ⟨hne.symm, hlab.symm, Or.inr hu⟩
    · exact ⟨hne.symm, hlab.symm, Or.inl hv⟩
  loopless := by
    intro u h
    exact h.1 rfl

theorem fiberCenter_fixed
    (label : C → A) (center : C → C)
    (hlabel : ∀ c, label (center c) = label c)
    (hconst : ∀ a b, label a = label b → center a = center b)
    (c : C) :
    center (center c) = center c :=
  hconst (center c) c (hlabel c)

/-- Every non-centre vertex is adjacent to the selected centre of its fibre. -/
theorem fiberStarGraph_adj_center
    (label : C → A) (center : C → C)
    (hlabel : ∀ c, label (center c) = label c)
    (hconst : ∀ a b, label a = label b → center a = center b)
    {c : C} (hc : c ≠ center c) :
    (fiberStarGraph label center).Adj c (center c) := by
  refine ⟨hc, (hlabel c).symm, Or.inr ?_⟩
  exact (fiberCenter_fixed label center hlabel hconst c).symm

/-- A non-centre vertex has only its fibre centre as a neighbour. -/
theorem eq_center_of_fiberStarGraph_adj_of_ne_center
    (label : C → A) (center : C → C)
    (hconst : ∀ a b, label a = label b → center a = center b)
    {u v : C} (hu : u ≠ center u)
    (huv : (fiberStarGraph label center).Adj u v) :
    v = center u := by
  rcases huv with ⟨_hne, hlab, hu' | hv⟩
  · exact (hu hu').elim
  · exact hv.trans (hconst u v hlab).symm

/-- A disjoint union of fibre stars is acyclic. -/
theorem fiberStarGraph_isAcyclic
    (label : C → A) (center : C → C)
    (hlabel : ∀ c, label (center c) = label c)
    (hconst : ∀ a b, label a = label b → center a = center b) :
    (fiberStarGraph label center).IsAcyclic := by
  intro v c hc
  have noCycleAtNoncenter :
      ∀ {u : C} (p : (fiberStarGraph label center).Walk u u),
        p.IsCycle → u ≠ center u → False := by
    intro u p hp hu
    have hsnd :
        p.snd = center u :=
      eq_center_of_fiberStarGraph_adj_of_ne_center
        label center hconst hu (p.adj_snd hp.not_nil)
    have hpen :
        p.penultimate = center u :=
      eq_center_of_fiberStarGraph_adj_of_ne_center
        label center hconst hu (p.adj_penultimate hp.not_nil).symm
    exact hp.snd_ne_penultimate (hsnd.trans hpen.symm)
  by_cases hv : v = center v
  · have hadj := c.adj_snd hc.not_nil
    have hsndNon : c.snd ≠ center c.snd := by
      intro hsndFixed
      have hlab : label v = label c.snd := hadj.2.1
      have hvc : center v = center c.snd :=
        hconst v c.snd hlab
      apply hadj.ne
      exact hv.trans (hvc.trans hsndFixed.symm)
    have hsndMem : c.snd ∈ c.support :=
      List.mem_of_mem_tail (c.snd_mem_tail_support hc.not_nil)
    exact noCycleAtNoncenter
      (c.rotate c.snd hsndMem) (hc.rotate hsndMem) hsndNon
  · exact noCycleAtNoncenter c hc hv

/-- A canonical representative of a value in the range of a labelling. -/
noncomputable def fiberRepresentative
    (label : C → A) (a : Set.range label) : C :=
  Classical.choose a.property

theorem fiberRepresentative_spec
    (label : C → A) (a : Set.range label) :
    label (fiberRepresentative label a) = a.1 :=
  Classical.choose_spec a.property

/-- The range-valued label of a vertex. -/
def fiberKey (label : C → A) (c : C) : Set.range label :=
  ⟨label c, ⟨c, rfl⟩⟩

/-- The chosen representative of the fibre containing a vertex. -/
noncomputable def fiberCenter (label : C → A) (c : C) : C :=
  fiberRepresentative label (fiberKey label c)

theorem fiberCenter_label (label : C → A) (c : C) :
    label (fiberCenter label c) = label c := by
  exact fiberRepresentative_spec label (fiberKey label c)

theorem fiberCenter_eq_of_label_eq
    (label : C → A) {a b : C} (h : label a = label b) :
    fiberCenter label a = fiberCenter label b := by
  unfold fiberCenter
  congr 1
  exact Subtype.ext h

/-- Every finite nonempty labelled set admits a tree in which every label fibre
is preconnected. -/
theorem exists_tree_fibers_preconnected
    [Finite C] [Nonempty C]
    (label : C → A) :
    ∃ T : SimpleGraph C, T.IsTree ∧
      ∀ a : A, (T.induce {c : C | label c = a}).Preconnected := by
  classical
  let center : C → C := fiberCenter label
  let H : SimpleGraph C := fiberStarGraph label center
  have hlabel : ∀ c : C, label (center c) = label c := by
    intro c
    exact fiberCenter_label label c
  have hconst :
      ∀ a b : C, label a = label b → center a = center b := by
    intro a b h
    exact fiberCenter_eq_of_label_eq label h
  have hH : H.IsAcyclic := by
    exact fiberStarGraph_isAcyclic label center hlabel hconst
  have hTop : (⊤ : SimpleGraph C).Connected :=
    SimpleGraph.connected_top
  obtain ⟨T, hHT, _hTTop, hT⟩ :=
    hTop.exists_isTree_le_of_le_of_isAcyclic
      (H := H) le_top hH
  refine ⟨T, hT, ?_⟩
  intro a c d
  let r : C := center c.1
  have hrlabel : label r = a := by
    exact (hlabel c.1).trans c.2
  let rr : {z : C | label z = a} := ⟨r, hrlabel⟩
  have hcenterD : center d.1 = r := by
    exact hconst d.1 c.1 (d.2.trans c.2.symm)
  have reachRoot :
      ∀ z : {z : C | label z = a},
        (T.induce {z : C | label z = a}).Reachable z rr := by
    intro z
    by_cases hz : z.1 = r
    · have hzr : z = rr := Subtype.ext hz
      rw [hzr]
      exact SimpleGraph.Reachable.refl _
    · have hcenterZ : center z.1 = r := by
        exact hconst z.1 c.1 (z.2.trans c.2.symm)
      have hzCenter : z.1 ≠ center z.1 := by
        intro h
        apply hz
        exact h.trans hcenterZ
      have hadjH :
          H.Adj z.1 r := by
        have h :=
          fiberStarGraph_adj_center
            label center hlabel hconst hzCenter
        rw [hcenterZ] at h
        exact h
      have hadjT : T.Adj z.1 r :=
        hHT hadjH
      have hadjInd :
          (T.induce {z : C | label z = a}).Adj z rr :=
        hadjT
      exact hadjInd.reachable
  exact (reachRoot c).trans (reachRoot d).symm

end StructuralRamsey.Girth
