import Girth.ForestTreeRewire
import Mathlib.Combinatorics.SimpleGraph.Sum

/-! # Binary gluing of join trees

This is the graph-theoretic core of the manuscript's join-tree lifting lemma.
Two finite join trees may be connected by one bridge between chosen connector
members.  If every vertex occurring on both sides occurs in both connectors,
the resulting tree again satisfies running intersections.
-/

namespace StructuralRamsey.Girth

universe v
variable {W I J : Type v}

/-- Family obtained by placing two labelled families on the two summands. -/
def sumPieces
    (F : I → HypergraphPiece W)
    (G : J → HypergraphPiece W) :
    I ⊕ J → HypergraphPiece W
  | .inl i => F i
  | .inr j => G j

/-- The disjoint sum of two finite trees, joined by one cross edge, is a tree. -/
theorem isTree_sum_sup_edge
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
  apply isTree_of_connected_ncard_edgeSet K hConn
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
def JoinTree.sumBridge
    [Fintype I] [Fintype J]
    {F : I → HypergraphPiece W}
    {G : J → HypergraphPiece W}
    (JF : JoinTree F) (JG : JoinTree G)
    (i0 : I) (j0 : J)
    (hCross :
      ∀ (x : W) (i : I) (j : J),
        x ∈ (F i).carrier →
        x ∈ (G j).carrier →
          x ∈ (F i0).carrier ∧ x ∈ (G j0).carrier) :
    JoinTree (sumPieces F G) := by
  classical
  let K :=
    JF.tree.sum JG.tree ⊔
      SimpleGraph.edge (Sum.inl i0) (Sum.inr j0)
  refine
    { tree := K
      isTree := isTree_sum_sup_edge
        JF.tree JG.tree JF.isTree JG.isTree i0 j0
      running := ?_ }
  intro x
  let occF : Set I := {i | x ∈ (F i).carrier}
  let occG : Set J := {j | x ∈ (G j).carrier}
  let occ : Set (I ⊕ J) :=
    {s | x ∈ (sumPieces F G s).carrier}
  let phiF :
      (JF.tree.induce occF) →g (K.induce occ) :=
    { toFun := fun z => ⟨Sum.inl z.1, by
          change x ∈ (F z.1).carrier
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
          change x ∈ (G z.1).carrier
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

/-- Pairwise allowed intersections are inherited by a disjoint sum once all
cross-side pairs have allowed intersections. -/
theorem pairwiseAllowed_sumPieces
    {F : I → HypergraphPiece W}
    {G : J → HypergraphPiece W}
    (hF : PairwiseAllowed F)
    (hG : PairwiseAllowed G)
    (hCross : ∀ i j, AllowedIntersection (F i) (G j)) :
    PairwiseAllowed (sumPieces F G) := by
  intro a b hab
  cases a with
  | inl i =>
      cases b with
      | inl k =>
          apply hF
          intro hik
          apply hab
          simpa [hik]
      | inr j =>
          exact hCross i j
  | inr j =>
      cases b with
      | inl i =>
          exact allowedIntersection_symm (hCross i j)
      | inr k =>
          apply hG
          intro hjk
          apply hab
          simpa [hjk]

/-- Binary forest gluing along one connector edge. -/
theorem forestOfCopies_sumBridge
    [Fintype I] [Fintype J]
    {F : I → HypergraphPiece W}
    {G : J → HypergraphPiece W}
    (JF : JoinTree F) (JG : JoinTree G)
    (hF : PairwiseAllowed F)
    (hG : PairwiseAllowed G)
    (i0 : I) (j0 : J)
    (hCrossOcc :
      ∀ (x : W) (i : I) (j : J),
        x ∈ (F i).carrier →
        x ∈ (G j).carrier →
          x ∈ (F i0).carrier ∧ x ∈ (G j0).carrier)
    (hCrossAllowed :
      ∀ i j, AllowedIntersection (F i) (G j)) :
    ForestOfCopies (sumPieces F G) :=
  ⟨pairwiseAllowed_sumPieces hF hG hCrossAllowed,
    Or.inr ⟨JF.sumBridge JG i0 j0 hCrossOcc⟩⟩

end StructuralRamsey.Girth
