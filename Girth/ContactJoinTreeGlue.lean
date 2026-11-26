import Girth.ContactJoinTree
import Mathlib.Combinatorics.SimpleGraph.Sum
import Mathlib.Combinatorics.SimpleGraph.Finite

/-! Pure join-tree construction and reindexing extracted from the
verified old join-tree library. These lemmas are useful both for
the converse acyclicity proof and for the local forest increment. -/

namespace StructuralRamsey.Girth
universe v
variable {W I J : Type v}

theorem contact_isTree_of_connected_ncard_edgeSet
    {V : Type v} [Finite V]
    (G : SimpleGraph V)
    (hconn : G.Connected)
    (hcard : G.edgeSet.ncard + 1 = Nat.card V) :
    G.IsTree := by
  classical
  letI := Fintype.ofFinite V
  obtain ⟨T, hTG, hTtree⟩ := hconn.exists_isTree_le
  have hTedge :
      Finset.card T.edgeFinset = T.edgeSet.ncard := by
    calc
      Finset.card T.edgeFinset = Fintype.card T.edgeSet :=
        T.edgeFinset_card
      _ = T.edgeSet.ncard :=
        Set.fintypeCard_eq_ncard T.edgeSet
  have hTcard : T.edgeSet.ncard + 1 = Nat.card V := by
    calc
      T.edgeSet.ncard + 1 =
          Finset.card T.edgeFinset + 1 :=
        congrArg (· + 1) hTedge.symm
      _ = Fintype.card V := hTtree.card_edgeFinset
      _ = Nat.card V := by simp
  have hcards : T.edgeSet.ncard = G.edgeSet.ncard := by
    omega
  have hsub : T.edgeSet ⊆ G.edgeSet :=
    SimpleGraph.edgeSet_mono hTG
  have hedge : T.edgeSet = G.edgeSet :=
    Set.eq_of_subset_of_ncard_le hsub (by omega) (Set.toFinite G.edgeSet)
  have hEq : T = G :=
    SimpleGraph.edgeSet_injective hedge
  simpa [hEq] using hTtree



/-- Family obtained by placing two labelled families on the two summands. -/
def contactSumSets
    (F : I → Set W)
    (G : J → Set W) :
    I ⊕ J → Set W
  | .inl i => F i
  | .inr j => G j

/-- The disjoint sum of two finite trees, joined by one cross edge, is a tree. -/
theorem contact_isTree_sum_sup_edge
    [Fintype I] [Fintype J]
    (G : SimpleGraph I) (H : SimpleGraph J)
    (hG : G.IsTree) (hH : H.IsTree)
    (i0 : I) (j0 : J) :
    (G.sum H ⊔ SimpleGraph.edge (Sum.inl i0) (Sum.inr j0)).IsTree := by
  classical
  let K :=
    G.sum H ⊔ SimpleGraph.edge (Sum.inl i0) (Sum.inr j0)
  have hConn : K.Connected := by
    dsimp [K]
    exact hG.connected.sum_sup_edge hH.connected
  apply contact_isTree_of_connected_ncard_edgeSet K hConn
  have hEdgeSet :
      K.edgeSet =
        insert s(Sum.inl i0, Sum.inr j0) (G.sum H).edgeSet := by
    dsimp [K]
    ext e
    by_cases heq :
        e = s(Sum.inl i0, Sum.inr j0)
    · subst e
      simp [SimpleGraph.edgeSet_sup, Sym2.mk_isDiag_iff]
    · simp [SimpleGraph.edgeSet_sup, heq]
  have hNot :
      s(Sum.inl i0, Sum.inr j0) ∉ (G.sum H).edgeSet := by
    simp
  have hBridge :
      K.edgeSet.ncard =
        (G.sum H).edgeSet.ncard + 1 := by
    rw [hEdgeSet, Set.ncard_insert_of_notMem hNot]
  have hSum :
      (G.sum H).edgeSet.ncard =
        G.edgeSet.ncard + H.edgeSet.ncard := by
    calc
      (G.sum H).edgeSet.ncard =
          Fintype.card (G.sum H).edgeSet := by
        rw [Set.fintypeCard_eq_ncard]
      _ = Fintype.card (G.edgeSet ⊕ H.edgeSet) :=
        Fintype.card_congr SimpleGraph.edgeSetSumEquiv
      _ = Fintype.card G.edgeSet + Fintype.card H.edgeSet := by
        rw [Fintype.card_sum]
      _ = G.edgeSet.ncard + H.edgeSet.ncard := by
        rw [Set.fintypeCard_eq_ncard, Set.fintypeCard_eq_ncard]
  have hGc :
      G.edgeSet.ncard + 1 = Nat.card I := by
    calc
      G.edgeSet.ncard + 1 =
          Fintype.card G.edgeSet + 1 := by
        rw [Set.fintypeCard_eq_ncard]
      _ = Finset.card G.edgeFinset + 1 := by
        rw [← G.edgeFinset_card]
      _ = Fintype.card I := hG.card_edgeFinset
      _ = Nat.card I := by
        rw [Nat.card_eq_fintype_card]
  have hHc :
      H.edgeSet.ncard + 1 = Nat.card J := by
    calc
      H.edgeSet.ncard + 1 =
          Fintype.card H.edgeSet + 1 := by
        rw [Set.fintypeCard_eq_ncard]
      _ = Finset.card H.edgeFinset + 1 := by
        rw [← H.edgeFinset_card]
      _ = Fintype.card J := hH.card_edgeFinset
      _ = Nat.card J := by
        rw [Nat.card_eq_fintype_card]
  calc
    K.edgeSet.ncard + 1 =
        ((G.sum H).edgeSet.ncard + 1) + 1 :=
      congrArg (fun n => n + 1) hBridge
    _ = (G.edgeSet.ncard + H.edgeSet.ncard + 1) + 1 := by
      rw [hSum]
    _ = Nat.card I + Nat.card J := by
      omega
    _ = Nat.card (I ⊕ J) := by
      rw [Nat.card_sum]

/-- Glue two join trees by a single bridge.  The cross-occurrence hypothesis
says that whenever an ambient vertex occurs on both sides, it occurs in the
chosen connector member on each side. -/
def ContactJoinTree.sumBridge
    [Fintype I] [Fintype J]
    {F : I → Set W}
    {G : J → Set W}
    (JF : ContactJoinTree F) (JG : ContactJoinTree G)
    (i0 : I) (j0 : J)
    (hCross :
      ∀ (x : W) (i : I) (j : J),
        x ∈ F i →
        x ∈ G j →
          x ∈ F i0 ∧ x ∈ G j0) :
    ContactJoinTree (contactSumSets F G) := by
  classical
  let K :=
    JF.tree.sum JG.tree ⊔
      SimpleGraph.edge (Sum.inl i0) (Sum.inr j0)
  refine
    { tree := K
      isTree := contact_isTree_sum_sup_edge
        JF.tree JG.tree JF.isTree JG.isTree i0 j0
      running := ?_ }
  intro x
  let occF : Set I := {i | x ∈ F i}
  let occG : Set J := {j | x ∈ G j}
  let occ : Set (I ⊕ J) :=
    {s | x ∈ contactSumSets F G s}
  let phiF :
      (JF.tree.induce occF) →g (K.induce occ) :=
    { toFun := fun z => ⟨Sum.inl z.1, by
          change x ∈ F z.1
          exact z.2⟩
      map_rel' := by
        intro a b hab
        change K.Adj (Sum.inl a.1) (Sum.inl b.1)
        have hbase :
            JF.tree.sum JG.tree ≤ K := by
          dsimp [K]
          exact le_sup_left
        apply hbase
        simpa using hab }
  let phiG :
      (JG.tree.induce occG) →g (K.induce occ) :=
    { toFun := fun z => ⟨Sum.inr z.1, by
          change x ∈ G z.1
          exact z.2⟩
      map_rel' := by
        intro a b hab
        change K.Adj (Sum.inr a.1) (Sum.inr b.1)
        have hbase :
            JF.tree.sum JG.tree ≤ K := by
          dsimp [K]
          exact le_sup_left
        apply hbase
        simpa using hab }
  intro a b
  rcases a with ⟨a, ha⟩
  rcases b with ⟨b, hb⟩
  cases a with
  | inl i =>
      cases b with
      | inl k =>
          let ai : occF := ⟨i, ha⟩
          let bk : occF := ⟨k, hb⟩
          have h :=
            (JF.running x ai bk).map phiF
          convert h using 1 <;> apply Subtype.ext <;> rfl
      | inr j =>
          have hc := hCross x i j ha hb
          let ai : occF := ⟨i, ha⟩
          let ci : occF := ⟨i0, hc.1⟩
          let cj : occG := ⟨j0, hc.2⟩
          let bj : occG := ⟨j, hb⟩
          have hL :
              (K.induce occ).Reachable
                (phiF ai) (phiF ci) :=
            (JF.running x ai ci).map phiF
          have hB :
              (K.induce occ).Adj (phiF ci) (phiG cj) := by
            change K.Adj (Sum.inl i0) (Sum.inr j0)
            have hedge :
                SimpleGraph.edge (Sum.inl i0) (Sum.inr j0) ≤ K := by
              dsimp [K]
              exact le_sup_right
            apply hedge
            simp [SimpleGraph.edge]
          have hR :
              (K.induce occ).Reachable
                (phiG cj) (phiG bj) :=
            (JG.running x cj bj).map phiG
          have h := hL.trans (hB.reachable.trans hR)
          convert h using 1 <;> apply Subtype.ext <;> rfl
  | inr j =>
      cases b with
      | inl i =>
          have hc := hCross x i j hb ha
          let aj : occG := ⟨j, ha⟩
          let cj : occG := ⟨j0, hc.2⟩
          let ci : occF := ⟨i0, hc.1⟩
          let bi : occF := ⟨i, hb⟩
          have hR :
              (K.induce occ).Reachable
                (phiG aj) (phiG cj) :=
            (JG.running x aj cj).map phiG
          have hB :
              (K.induce occ).Adj (phiF ci) (phiG cj) := by
            change K.Adj (Sum.inl i0) (Sum.inr j0)
            have hedge :
                SimpleGraph.edge (Sum.inl i0) (Sum.inr j0) ≤ K := by
              dsimp [K]
              exact le_sup_right
            apply hedge
            simp [SimpleGraph.edge]
          have hL :
              (K.induce occ).Reachable
                (phiF ci) (phiF bi) :=
            (JF.running x ci bi).map phiF
          have h := hR.trans (hB.reachable.symm.trans hL)
          convert h using 1 <;> apply Subtype.ext <;> rfl
      | inr k =>
          let aj : occG := ⟨j, ha⟩
          let bk : occG := ⟨k, hb⟩
          have h :=
            (JG.running x aj bk).map phiG
          convert h using 1 <;> apply Subtype.ext <;> rfl


/-- Relabel a join tree along an equivalence of its index type. -/
def ContactJoinTree.reindex
    {κ : Type v} {F : ι → Set W}
    (J : ContactJoinTree F) (e : κ ≃ ι) :
    ContactJoinTree (fun k => F (e k)) where
  tree := J.tree.comap e
  isTree :=
    (SimpleGraph.Iso.comap e J.tree).isTree_iff.mpr J.isTree
  running := by
    intro x
    let oldOcc : Set ι := {i | x ∈ F i}
    let newOcc : Set κ := {k | x ∈ F (e k)}
    have hOld : (J.tree.induce oldOcc).Preconnected := by
      simpa [oldOcc] using J.running x
    let phi :
        (J.tree.induce oldOcc) →g
          ((J.tree.comap e).induce newOcc) :=
      { toFun := fun z =>
          ⟨e.symm z.1, by
            have hz := z.2
            change x ∈ F z.1 at hz
            change x ∈ F (e (e.symm z.1))
            simpa only [e.apply_symm_apply] using hz⟩
        map_rel' := by
          intro a b hab
          change J.tree.Adj (e (e.symm a.1)) (e (e.symm b.1))
          simpa using hab }
    have hphi : Function.Surjective phi := by
      intro y
      have hy := y.2
      change x ∈ F (e y.1) at hy
      let z : oldOcc := ⟨e y.1, hy⟩
      refine ⟨z, ?_⟩
      apply Subtype.ext
      change e.symm (e y.1) = y.1
      exact e.symm_apply_apply y.1
    exact hOld.map phi hphi


end StructuralRamsey.Girth
