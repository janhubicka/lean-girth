import Girth.ForestToSupremeLeaf
import Girth.ForestCyclicSwitching
import Girth.ForestLeafDeletion
import Girth.ForestBottomSupremePullback

/-!
# Forest ownership during bottom-cycle leaf elimination

The owner of an edge occurrence can change when a forest leaf is removed.
Designated labels cannot: their owner is their original labelled member.
Every retained member has an actual occurrence of its own label.  This last
condition prevents an absent designated member being selected as supreme.
-/

namespace StructuralRamsey.Girth.OrderOneData

universe v
variable {V E I P K : Type v} (D : OrderOneData V E I P)

/-- Physical ownership invariant for a cycle supported on a forest. -/
structure BottomForestOwnership {n : ℕ} (C : D.BigCycle n)
    (member : K → I ⊕ E) where
  owner : Fin n → K
  carrier_subset : ∀ j, D.carrier (C.label j) ⊆ D.carrier (member (owner j))
  edges_subset : ∀ j, D.edges (C.label j) ⊆ D.edges (member (owner j))
  designated_eq : ∀ j, D.designated (C.label j) → C.label j = member (owner j)
  member_occurs : ∀ a, ∃ j, owner j = a ∧ C.label j = member a

variable {D} {n : ℕ} {C : D.BigCycle n} {member : K → I ⊕ E}

theorem BottomForestOwnership.incident_left
    (O : D.BottomForestOwnership C member) (j : Fin n) :
    D.Incident (member (O.owner j)) (C.connector j) :=
  D.incident_of_carrier_edges_subset (O.carrier_subset j) (O.edges_subset j)
    (C.left_incident j)

theorem BottomForestOwnership.incident_right
    (O : D.BottomForestOwnership C member) (j : Fin n) :
    D.Incident (member (O.owner (cyclicSucc j))) (C.connector j) :=
  D.incident_of_carrier_edges_subset (O.carrier_subset (cyclicSucc j))
    (O.edges_subset (cyclicSucc j)) (C.right_incident j)

/-- Every edge occurrence assigned to a one-edge member has that actual
edge's label. A designated occurrence cannot be assigned to an edge member. -/
theorem BottomForestOwnership.label_eq_of_edge_owner
    (O : D.BottomForestOwnership C member) {j : Fin n} {e : E}
    (he : member (O.owner j) = .inr e) : C.label j = .inr e := by
  cases hl : C.label j with
  | inl i =>
      have hd : D.designated (C.label j) := by simp [hl, designated]
      simpa only [hl] using (O.designated_eq j hd).trans he
  | inr f =>
      have hf : f ∈ D.edges (C.label j) := by simp [hl, edges]
      have hfe := O.edges_subset j hf
      have h : f = e := by simpa [he, edges] using hfe
      simpa only [hl] using hl.trans (congrArg Sum.inr h)

/-- A common owner which is designated and actually occurs is supreme:
every differently labelled occurrence is an edge of that member. -/
theorem BottomForestOwnership.supreme_of_constant_owner
    (O : D.BottomForestOwnership C member) (hAccept : C.Acceptable)
    (a : K) (hOwner : ∀ j, O.owner j = a)
    (hDesignated : D.designated (member a)) : C.HasSimultaneousSupreme := by
  obtain ⟨k, _, hk⟩ := O.member_occurs a
  apply C.hasSimultaneousSupreme_of_all_shortValid D hAccept k
    (by simpa [hk] using hDesignated)
  intro j hne
  cases hl : C.label j with
  | inl i =>
      have hd : D.designated (C.label j) := by simp [hl, designated]
      exact (hne ((O.designated_eq j hd).trans (by rw [hOwner j, hk]))).elim
  | inr e =>
      have he : e ∈ D.edges (C.label k) := by
        rw [hk]
        simpa [hOwner j] using O.edges_subset j (show e ∈ D.edges (C.label j) by
          simp [hl, edges])
      refine ⟨e, he, ?_, ?_⟩
      · have h := C.right_incident (trainCyclicPred j)
        rw [cyclicSucc_trainCyclicPred_of_two_le C.length_ge_two, hl] at h
        exact h
      · simpa [hl] using C.left_incident j

/-- A constant owner must be designated, since a genuine cycle has adjacent
different labels. -/
theorem BottomForestOwnership.constant_owner_designated
    (O : D.BottomForestOwnership C member) (a : K)
    (hOwner : ∀ j, O.owner j = a) : D.designated (member a) := by
  cases ha : member a with
  | inl i => trivial
  | inr e =>
      let j : Fin n := ⟨0, by have := C.length_ge_two; omega⟩
      have hj : C.label j = .inr e := O.label_eq_of_edge_owner (by rw [hOwner, ha])
      have hs : C.label (cyclicSucc j) = .inr e :=
        O.label_eq_of_edge_owner (by rw [hOwner, ha])
      exact (C.adjacent_ne j (hj.trans hs.symm)).elim

/-- The Boolean side of a leaf has both values whenever another member has
an occurrence. -/
theorem BottomForestOwnership.leaf_side_mixed
    (O : D.BottomForestOwnership C member) [DecidableEq K]
    {leaf other : K} (hOther : other ≠ leaf) :
    ∃ i j : Fin n, decide (O.owner i = leaf) ≠ decide (O.owner j = leaf) := by
  obtain ⟨i, hi, _⟩ := O.member_occurs leaf
  obtain ⟨j, hj, _⟩ := O.member_occurs other
  exact ⟨i, j, by simp [hi, hj, hOther]⟩

/-- A switch in the leaf/rest binary word has one incident leaf member and
one incident member different from the leaf, in either cyclic orientation. -/
theorem BottomForestOwnership.leaf_switch_members
    (O : D.BottomForestOwnership C member) [DecidableEq K]
    (leaf : K) (j : Fin n)
    (hSwitch : decide (O.owner j = leaf) ≠
      decide (O.owner (cyclicSucc j) = leaf)) :
    ∃ other : K, other ≠ leaf ∧
      D.Incident (member leaf) (C.connector j) ∧
      D.Incident (member other) (C.connector j) := by
  by_cases hj : O.owner j = leaf
  · have hs : O.owner (cyclicSucc j) ≠ leaf := by
      intro hs
      simp [hj, hs] at hSwitch
    exact ⟨O.owner (cyclicSucc j), hs, by simpa [hj] using O.incident_left j,
      O.incident_right j⟩
  · have hs : O.owner (cyclicSucc j) = leaf := by
      by_contra hs
      simp [hj, hs] at hSwitch
    exact ⟨O.owner j, hj, by simpa [hs] using O.incident_right j,
      O.incident_left j⟩

/-- A leaf used by a genuine cycle cannot have a singleton attachment to the
rest: the cyclic word switches twice at distinct physical connectors. -/
theorem BottomForestOwnership.leaf_separator
    (O : D.BottomForestOwnership C member)
    (H : D.BottomForestGeometry)
    (J : JoinTree (fun k => D.bottomForestPiece H (member k)))
    (hAllowed : PairwiseAllowed (fun k => D.bottomForestPiece H (member k)))
    {leaf parent : K}
    (hAdj : J.tree.Adj leaf parent)
    (hUnique : ∀ k, J.tree.Adj leaf k → k = parent) :
    ∃ e : E, e ∈ D.edges (member leaf) ∧ e ∈ D.edges (member parent) ∧
      D.carrier (member leaf) ∩ D.carrier (member parent) = D.edgeCarrier e := by
  classical
  rcases hAllowed hAdj.ne with hs | ⟨s, hsL, hsP, hInter⟩
  · have hVertex (j : Fin n)
        (hj : decide (O.owner j = leaf) ≠ decide (O.owner (cyclicSucc j) = leaf)) :
        ∃ x : V, C.connector j = .inl x ∧
          x ∈ D.carrier (member leaf) ∩ D.carrier (member parent) := by
      obtain ⟨other, hOther, hl, ho⟩ := O.leaf_switch_members leaf j hj
      cases hq : C.connector j with
      | inl x =>
          have hxl : x ∈ D.carrier (member leaf) := by simpa [hq, Incident] using hl
          have hxo : x ∈ D.carrier (member other) := by simpa [hq, Incident] using ho
          exact ⟨x, rfl, hxl,
            J.mem_parent_of_mem_leaf_and_other hAdj hUnique hOther hxl hxo⟩
      | inr p =>
          obtain ⟨e, hel, heo, _⟩ := H.common_edge_of_meets D
            (by simpa [hq, Incident] using hl) (by simpa [hq, Incident] using ho)
          have hSub : D.edgeCarrier e ⊆ D.carrier (member leaf) ∩
              D.carrier (member parent) := fun x hx =>
            ⟨H.edge_subset (member leaf) e hel hx,
              H.leaf_shared_edge_mem_parent D member J hAdj hUnique hOther hel heo hx⟩
          obtain ⟨x, hx, y, hy, hxy⟩ := H.edge_nontrivial e
          exact (hxy (hs (hSub hx) (hSub hy))).elim
    obtain ⟨i, j, hij, hi, hj⟩ := cyclicBool_exists_two_distinct_switches
      C.length_ge_two (fun j => decide (O.owner j = leaf))
      (O.leaf_side_mixed hAdj.ne.symm)
    obtain ⟨x, hix, hx⟩ := hVertex i hi
    obtain ⟨y, hjy, hy⟩ := hVertex j hj
    exact (hij (C.connector_injective (hix.trans
      ((congrArg Sum.inl (hs hx hy)).trans hjy.symm)))).elim
  · obtain ⟨e, he, hes⟩ := hsL
    obtain ⟨f, hf, hfs⟩ := hsP
    have hef : e = f := H.edge_eq_of_subset D (by rw [hes, hfs])
    subst f
    exact ⟨e, he, hf, by simpa [bottomForestPiece, hes] using hInter⟩

/-- There is a single occurrence on one side of every used leaf separation.
This is the actual cyclic switching argument, including repeated labels. -/
theorem BottomForestOwnership.leaf_singleton_side
    (O : D.BottomForestOwnership C member)
    (H : D.BottomForestGeometry) (hAccept : C.Acceptable)
    (J : JoinTree (fun k => D.bottomForestPiece H (member k)))
    {leaf parent : K}
    (hAdj : J.tree.Adj leaf parent)
    (hUnique : ∀ k, J.tree.Adj leaf k → k = parent)
    {e : E}
    (hInter : D.carrier (member leaf) ∩ D.carrier (member parent) = D.edgeCarrier e) :
    ∃ k : Fin n, (∀ j, O.owner j = leaf ↔ j = k) ∨
      (∀ j, O.owner j ≠ leaf ↔ j = k) := by
  classical
  obtain ⟨p, hp⟩ := C.edge_incident_positions_consecutive D hAccept e
  have hCuts : ∀ j : Fin n, decide (O.owner j = leaf) ≠
      decide (O.owner (cyclicSucc j) = leaf) → j = p ∨ j = cyclicSucc p := by
    intro j hj
    obtain ⟨other, hOther, hl, ho⟩ := O.leaf_switch_members leaf j hj
    exact hp j (H.leaf_switch_incident D member J hAdj hUnique hOther hInter hl ho)
  obtain ⟨k, hk⟩ := cyclicBool_has_singleton_side_of_consecutive_cuts
    C.length_ge_two (fun j => decide (O.owner j = leaf))
    (O.leaf_side_mixed hAdj.ne.symm) ⟨p, hCuts⟩
  exact ⟨k, by simpa using hk⟩

/-- The same physical separator works at each actual switching connector. -/
theorem BottomForestOwnership.separator_incident_at_switch
    (O : D.BottomForestOwnership C member)
    (H : D.BottomForestGeometry)
    (J : JoinTree (fun k => D.bottomForestPiece H (member k)))
    {leaf parent : K}
    (hAdj : J.tree.Adj leaf parent)
    (hUnique : ∀ k, J.tree.Adj leaf k → k = parent)
    {e : E}
    (hInter : D.carrier (member leaf) ∩ D.carrier (member parent) = D.edgeCarrier e)
    (j : Fin n)
    (hSwitch : (O.owner j = leaf ∧ O.owner (cyclicSucc j) ≠ leaf) ∨
      (O.owner j ≠ leaf ∧ O.owner (cyclicSucc j) = leaf)) :
    D.Incident (.inr e) (C.connector j) := by
  classical
  have hBool : decide (O.owner j = leaf) ≠ decide (O.owner (cyclicSucc j) = leaf) := by
    rcases hSwitch with ⟨hl, hr⟩ | ⟨hl, hr⟩ <;> simp [hl, hr]
  obtain ⟨other, hOther, hl, ho⟩ := O.leaf_switch_members leaf j hBool
  exact H.leaf_switch_incident D member J hAdj hUnique hOther hInter hl ho

/-- When all but one occurrence belong to a leaf, that leaf is itself a
designated supreme member.  Edge occurrences within the leaf are replaced by
their own physical edges; only the complementary singleton uses the separator. -/
theorem BottomForestOwnership.supreme_of_complement_singleton
    (O : D.BottomForestOwnership C member)
    (H : D.BottomForestGeometry) (hAccept : C.Acceptable) (hn : 3 ≤ n)
    (J : JoinTree (fun k => D.bottomForestPiece H (member k)))
    {leaf parent : K}
    (hAdj : J.tree.Adj leaf parent)
    (hUnique : ∀ k, J.tree.Adj leaf k → k = parent)
    {e : E} (hel : e ∈ D.edges (member leaf))
    (hInter : D.carrier (member leaf) ∩ D.carrier (member parent) = D.edgeCarrier e)
    (k : Fin n) (hSide : ∀ j, O.owner j ≠ leaf ↔ j = k) :
    C.HasSimultaneousSupreme := by
  classical
  have hk : O.owner k ≠ leaf := (hSide k).mpr rfl
  have hPred : trainCyclicPred k ≠ k := by
    intro h
    have hs := cyclicSucc_trainCyclicPred_of_two_le C.length_ge_two k
    rw [h] at hs
    exact C.adjacent_ne k (congrArg C.label hs.symm)
  have hSucc : cyclicSucc k ≠ k := by
    intro h
    exact C.adjacent_ne k (congrArg C.label h.symm)
  have hOff (j : Fin n) (hj : j ≠ k) : O.owner j = leaf := by
    by_contra h
    exact hj ((hSide j).mp h)
  have hSS : cyclicSucc (cyclicSucc k) ≠ k := by
    intro h
    have h' := congrArg trainCyclicPred h
    rw [trainCyclicPred_cyclicSucc_of_two_le C.length_ge_two] at h'
    exact trainCyclicPred_ne_cyclicSucc_of_three_le hn k h'.symm
  have hDesignated : D.designated (member leaf) := by
    cases hm : member leaf with
    | inl i => trivial
    | inr f =>
        have h1 : C.label (cyclicSucc k) = .inr f :=
          O.label_eq_of_edge_owner (by rw [hOff _ hSucc, hm])
        have h2 : C.label (cyclicSucc (cyclicSucc k)) = .inr f :=
          O.label_eq_of_edge_owner (by rw [hOff _ hSS, hm])
        exact (C.adjacent_ne (cyclicSucc k) (h1.trans h2.symm)).elim
  have hePred : D.Incident (.inr e) (C.connector (trainCyclicPred k)) :=
    O.separator_incident_at_switch H J hAdj hUnique hInter (trainCyclicPred k)
      (Or.inl ⟨hOff _ hPred, by
        rw [cyclicSucc_trainCyclicPred_of_two_le C.length_ge_two]
        exact hk⟩)
  have heHere : D.Incident (.inr e) (C.connector k) :=
    O.separator_incident_at_switch H J hAdj hUnique hInter k
      (Or.inr ⟨hk, hOff _ hSucc⟩)
  obtain ⟨r, _, hr⟩ := O.member_occurs leaf
  apply C.hasSimultaneousSupreme_of_all_shortValid D hAccept r
    (by simpa [hr] using hDesignated)
  intro j hj
  by_cases hLeaf : O.owner j = leaf
  · cases hl : C.label j with
    | inl i =>
        have hd : D.designated (C.label j) := by simp [hl, designated]
        exact (hj ((O.designated_eq j hd).trans (by rw [hLeaf, hr]))).elim
    | inr f =>
        have hf : f ∈ D.edges (C.label r) := by
          rw [hr]
          simpa [hLeaf] using O.edges_subset j (show f ∈ D.edges (C.label j) by
            simp [hl, edges])
        refine ⟨f, hf, ?_, ?_⟩
        · have h := C.right_incident (trainCyclicPred j)
          rw [cyclicSucc_trainCyclicPred_of_two_le C.length_ge_two, hl] at h
          exact h
        · simpa [hl] using C.left_incident j
  · have hjk := (hSide j).mp hLeaf
    subst j
    exact ⟨e, by simpa [hr] using hel, hePred, heHere⟩

/-- Delete a singleton leaf occurrence by an actual short replacement and
reassign that edge to the parent.  Every remaining forest member keeps its
own original occurrence. -/
theorem BottomForestOwnership.erase_singleton_leaf
    (O : D.BottomForestOwnership C member)
    (H : D.BottomForestGeometry) (hAccept : C.Acceptable) (hn : 3 ≤ n)
    (J : JoinTree (fun k => D.bottomForestPiece H (member k)))
    {leaf parent : K}
    (hAdj : J.tree.Adj leaf parent)
    (hUnique : ∀ k, J.tree.Adj leaf k → k = parent)
    {e : E} (hep : e ∈ D.edges (member parent))
    (hInter : D.carrier (member leaf) ∩ D.carrier (member parent) = D.edgeCarrier e)
    (k : Fin n) (hSide : ∀ j, O.owner j = leaf ↔ j = k) :
    ∃ B : D.BigCycle n, B.Acceptable ∧
      Nonempty (D.BottomForestOwnership B (fun a : {a : K // a ≠ leaf} => member a.1)) ∧
      (∀ j, B.connector j = C.connector j) ∧
      (∀ j, D.designated (B.label j) → C.label j = B.label j) := by
  classical
  have hk : O.owner k = leaf := (hSide k).mpr rfl
  have hPred : trainCyclicPred k ≠ k := by
    intro h
    have hs := cyclicSucc_trainCyclicPred_of_two_le C.length_ge_two k
    rw [h] at hs
    exact C.adjacent_ne k (congrArg C.label hs.symm)
  have hSucc : cyclicSucc k ≠ k := by
    intro h
    exact C.adjacent_ne k (congrArg C.label h.symm)
  have hOff (j : Fin n) (hj : j ≠ k) : O.owner j ≠ leaf :=
    fun h => hj ((hSide j).mp h)
  have hePred : D.Incident (.inr e) (C.connector (trainCyclicPred k)) :=
    O.separator_incident_at_switch H J hAdj hUnique hInter (trainCyclicPred k)
      (Or.inr ⟨hOff _ hPred, by
        rw [cyclicSucc_trainCyclicPred_of_two_le C.length_ge_two]
        exact hk⟩)
  have heHere : D.Incident (.inr e) (C.connector k) :=
    O.separator_incident_at_switch H J hAdj hUnique hInter k
      (Or.inl ⟨hk, hOff _ hSucc⟩)
  have hNeighbors := C.shortEdge_ne_neighbors D hAccept hn k e hePred heHere
  let B := C.replaceOne D k (.inr e) hNeighbors.1 hNeighbors.2 heHere hePred
  have hBAt : B.label k = .inr e := by
    simp [B, BigCycle.replaceOne, BigCycle.relabelSameConnectors, BigCycle.replaceLabelAt]
  have hBOff (j : Fin n) (hj : j ≠ k) : B.label j = C.label j := by
    simp [B, BigCycle.replaceOne, BigCycle.relabelSameConnectors, BigCycle.replaceLabelAt, hj]
  let owner' : Fin n → {a : K // a ≠ leaf} := fun j =>
    if hj : j = k then ⟨parent, hAdj.ne.symm⟩ else ⟨O.owner j, hOff j hj⟩
  have hOwnerAt : (owner' k).1 = parent := by simp [owner']
  have hOwnerOff (j : Fin n) (hj : j ≠ k) : (owner' j).1 = O.owner j := by
    simp [owner', hj]
  let O' : D.BottomForestOwnership B (fun a : {a : K // a ≠ leaf} => member a.1) := {
    owner := owner'
    carrier_subset := by
      intro j
      by_cases hj : j = k
      · subst j
        rw [hOwnerAt, hBAt]
        exact H.edge_subset (member parent) e hep
      · rw [hOwnerOff j hj, hBOff j hj]
        exact O.carrier_subset j
    edges_subset := by
      intro j
      by_cases hj : j = k
      · subst j
        rw [hOwnerAt, hBAt]
        intro f hf
        have hfe : f = e := hf
        simpa [hfe] using hep
      · rw [hOwnerOff j hj, hBOff j hj]
        exact O.edges_subset j
    designated_eq := by
      intro j hjDes
      by_cases hj : j = k
      · subst j
        simp [hBAt, designated] at hjDes
      · rw [hBOff j hj, hOwnerOff j hj]
        exact O.designated_eq j (by simpa [hBOff j hj] using hjDes)
    member_occurs := by
      intro a
      obtain ⟨j, hja, hjLabel⟩ := O.member_occurs a.1
      have hjk : j ≠ k := by
        intro hj
        exact a.2 (hja.symm.trans (by simpa [hj] using hk))
      refine ⟨j, ?_, ?_⟩
      · apply Subtype.ext
        exact (hOwnerOff j hjk).trans hja
      · exact (hBOff j hjk).trans hjLabel }
  refine ⟨B, C.replaceOne_acceptable_of_three_le_length D k (.inr e) hn
    hNeighbors.1 hNeighbors.2 heHere hePred hAccept, ⟨O'⟩, ?_, ?_⟩
  · intro j
    rfl
  · intro j hjDes
    by_cases hj : j = k
    · subst j
      simp [hBAt, designated] at hjDes
    · exact (hBOff j hj).symm

/-- A bottom acceptable cycle supported on a finite forest has a genuine
simultaneous supreme copy.  The proof removes only actual join-tree leaves,
constructs the short replacements, and decreases the number of members. -/
theorem BigCycle.hasSimultaneousSupreme_of_owned_bottom_joinTree
    {K : Type v} [Fintype K] {n : ℕ} (C : D.BigCycle n)
    (H : D.BottomForestGeometry) (hAccept : C.Acceptable) (hn : 3 ≤ n)
    (member : K → I ⊕ E)
    (J : JoinTree (fun k => D.bottomForestPiece H (member k)))
    (hAllowed : PairwiseAllowed (fun k => D.bottomForestPiece H (member k)))
    (O : D.BottomForestOwnership C member) : C.HasSimultaneousSupreme := by
  classical
  let j0 : Fin n := ⟨0, by omega⟩
  letI : Nonempty K := ⟨O.owner j0⟩
  by_cases hSub : Subsingleton K
  · letI : Subsingleton K := hSub
    let a : K := O.owner j0
    have hOwner : ∀ j, O.owner j = a := fun _ => Subsingleton.elim _ _
    exact O.supreme_of_constant_owner hAccept a hOwner
      (O.constant_owner_designated a hOwner)
  · letI : Nontrivial K := not_subsingleton_iff_nontrivial.mp hSub
    obtain ⟨leaf, parent, hAdj, hUnique, _⟩ := J.exists_leaf_attachment
    obtain ⟨e, hel, hep, hInter⟩ := O.leaf_separator H J hAllowed hAdj hUnique
    obtain ⟨k, hSingleton | hComplement⟩ :=
      O.leaf_singleton_side H hAccept J hAdj hUnique hInter
    · obtain ⟨B, hBAccept, ⟨OB⟩, hConn, hDes⟩ :=
        O.erase_singleton_leaf H hAccept hn J hAdj hUnique hep hInter k hSingleton
      let reindexRest : {a : K // a ≠ leaf} ≃
          {a : K // a ∈ (({leaf} : Set K)ᶜ)} :=
        Equiv.subtypeEquivRight (fun a => by
          simp only [Set.mem_compl_iff, Set.mem_singleton_iff])
      let JRest : JoinTree (fun a : {a : K // a ≠ leaf} =>
          D.bottomForestPiece H (member a.1)) := by
        simpa [erasePiece, reindexRest] using (J.eraseLeaf hAdj hUnique).reindex reindexRest
      have hAllowedRest : PairwiseAllowed (fun a : {a : K // a ≠ leaf} =>
          D.bottomForestPiece H (member a.1)) := by
        intro a b hab
        apply hAllowed
        exact fun heq => hab (Subtype.ext heq)
      have hcard : Fintype.card {a : K // a ≠ leaf} < Fintype.card K := by
        apply Fintype.card_lt_of_injective_not_surjective Subtype.val Subtype.val_injective
        intro hSurj
        obtain ⟨a, ha⟩ := hSurj leaf
        exact a.2 ha
      have hBSupreme := B.hasSimultaneousSupreme_of_owned_bottom_joinTree
        H hBAccept hn (fun a : {a : K // a ≠ leaf} => member a.1) JRest hAllowedRest OB
      exact C.bottom_hasSimultaneousSupreme_pullback_sameConnectors
        D H.parent_injective B hAccept hConn hDes hBSupreme
    · exact O.supreme_of_complement_singleton H hAccept hn J hAdj hUnique
        hel hInter k hComplement
termination_by Fintype.card K
decreasing_by exact hcard

end StructuralRamsey.Girth.OrderOneData
