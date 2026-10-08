import Girth.ForestCompletionKeepPieces

/-! # Assembly of compatible local forest-completion witnesses

A finite family of selected pieces is assigned to its standard-copy owners.
At every owner we ask the old completion invariant to cover the selected
pieces assigned to that owner and one connector for every outer join-tree
neighbour.  Once these local completed families are supplied, their forest
property and designated classification suffice to assemble a global
designated-only completion.

This theorem keeps the geometric side-conditions (support containment and
separator coverage) explicit.  They must be discharged by the actual
standard-picture construction in the circulation argument.
-/

namespace StructuralRamsey.Girth

universe v
variable {W Q N : Type v}

/-- Compatible local completion witnesses on an outer join tree combine into
a completion of the original selected family; local duplicate labels are
handled by equality of their actual support pieces. -/
theorem forestCompletion_witness_of_compatible_local_completions
    [Fintype Q] [Nonempty Q] [DecidableEq Q] [Fintype N]
    {P : Q → HypergraphPiece W}
    (hOuter : PairwiseAllowed P)
    (JOuter : JoinTree P)
    [DecidableRel JOuter.tree.Adj]
    {H : Set (Set W)}
    (hEdges :
      ∀ q : Q, ∀ ⦃e : Set W⦄, e ∈ (P q).edges → e ∈ H)
    (hGirth : GirthGT H 2)
    (owner : N → Q)
    (hSurj : Function.Surjective owner)
    (m : ℕ) (hCard : Fintype.card N ≤ m)
    (selectedGlobal : N → HypergraphPiece W)
    (requested :
      (q : Q) →
        ({n : N // owner n = q} ⊕
          JOuter.tree.neighborSet q) → HypergraphPiece W)
    (hSelectedRequest :
      ∀ q (n : {n : N // owner n = q}),
        requested q (.inl n) = selectedGlobal n.1)
    (hRequestContained :
      ∀ q (r : {n : N // owner n = q} ⊕
          JOuter.tree.neighborSet q),
        (requested q r).carrier ⊆ (P q).carrier)
    (hConnectorOneEdge :
      ∀ q (r : JOuter.tree.neighborSet q),
        (requested q (.inr r)).IsOneEdge)
    (hSeparator :
      ∀ ⦃q r : Q⦄ (hadj : JOuter.tree.Adj q r),
        (P q).carrier ∩ (P r).carrier ⊆
          (requested q (.inr ⟨r, hadj⟩)).carrier)
    (hSeparatorExact :
      ∀ ⦃q r : Q⦄ (hadj : JOuter.tree.Adj q r),
        ¬((P q).carrier ∩ (P r).carrier).Subsingleton →
          (requested q (.inr ⟨r, hadj⟩)).carrier =
            (P q).carrier ∩ (P r).carrier)
    (designatedLocal : Q → HypergraphPiece W → Prop)
    (designated : HypergraphPiece W → Prop)
    (hDesignatedContained :
      ∀ q (R : HypergraphPiece W),
        designatedLocal q R → R.carrier ⊆ (P q).carrier)
    (hDesignatedGlobal :
      ∀ q (R : HypergraphPiece W),
        designatedLocal q R → designated R)
    {K : Q → Type v} [∀ q, Fintype (K q)]
    (family : (q : Q) → K q → HypergraphPiece W)
    (hLocal :
      ∀ q,
        ForestCompletionWitness
          (requested q) (designatedLocal q) (family q))
    (label :
      (q : Q) →
        ({n : N // owner n = q} ⊕ JOuter.tree.neighborSet q) → K q)
    (hLabel :
      ∀ q (r : {n : N // owner n = q} ⊕
          JOuter.tree.neighborSet q),
        family q (label q r) = requested q r) :
    ∃ keep : Finset (Sigma K),
      ForestCompletionWitness selectedGlobal designated
        (fun z : {z : Sigma K // z ∈ keep} =>
          family z.1.1 z.1.2) := by
  classical
  let anchor : (q : Q) → {n : N // owner n = q} :=
    fun q => ⟨Classical.choose (hSurj q),
      Classical.choose_spec (hSurj q)⟩
  letI : ∀ q : Q, Nonempty (K q) :=
    fun q => ⟨label q (.inl (anchor q))⟩
  have hLocalAllowed : ∀ q, PairwiseAllowed (family q) := by
    intro q
    exact (hLocal q).1.1
  let JLocal : ∀ q, JoinTree (family q) :=
    fun q => Classical.choice ((hLocal q).1.joinTree_of_nonempty)
  have hContain : ∀ q (k : K q),
      (family q k).carrier ⊆ (P q).carrier := by
    intro q k
    rcases (hLocal q).2.2 k with ⟨r, hr⟩ | hDesignated
    · rw [hr]
      exact hRequestContained q r
    · exact hDesignatedContained q (family q k) hDesignated
  let selectedLabel : N → Sigma K :=
    fun n => ⟨owner n, label (owner n) (.inl ⟨n, rfl⟩)⟩
  have hSelectedOwner : ∀ n : N,
      (selectedLabel n).1 = owner n := by
    intro n
    rfl
  have hSelectedPiece : ∀ n : N,
      family (selectedLabel n).1 (selectedLabel n).2 =
        selectedGlobal n := by
    intro n
    change family (owner n)
      (label (owner n) (.inl ⟨n, rfl⟩)) = selectedGlobal n
    calc
      family (owner n)
          (label (owner n) (.inl ⟨n, rfl⟩)) =
        requested (owner n) (.inl ⟨n, rfl⟩) :=
          hLabel (owner n) (.inl ⟨n, rfl⟩)
      _ = selectedGlobal n :=
          hSelectedRequest (owner n) ⟨n, rfl⟩
  let connector : (q r : Q) → K q :=
    fun q r =>
      if hadj : JOuter.tree.Adj q r
      then label q (.inr ⟨r, hadj⟩)
      else label q (.inl (anchor q))
  have hConnector :
      ∀ ⦃q r : Q⦄, JOuter.tree.Adj q r →
        (P q).carrier ∩ (P r).carrier ⊆
          (family q (connector q r)).carrier := by
    intro q r hadj
    have hEq :
        family q (connector q r) =
          requested q (.inr ⟨r, hadj⟩) := by
      simp only [connector, dif_pos hadj]
      exact hLabel q (.inr ⟨r, hadj⟩)
    rw [hEq]
    exact hSeparator hadj
  have hConnectorEdge :
      ∀ ⦃q r : Q⦄ (hadj : JOuter.tree.Adj q r),
        ¬((P q).carrier ∩ (P r).carrier).Subsingleton →
          (family q (connector q r)).IsOneEdge ∧
          (family q (connector q r)).carrier =
            (P q).carrier ∩ (P r).carrier := by
    intro q r hadj hBig
    have hEq :
        family q (connector q r) =
          requested q (.inr ⟨r, hadj⟩) := by
      simp only [connector, dif_pos hadj]
      exact hLabel q (.inr ⟨r, hadj⟩)
    rw [hEq]
    exact ⟨hConnectorOneEdge q ⟨r, hadj⟩,
      hSeparatorExact hadj hBig⟩
  have hClassification :
      ∀ z : Sigma K,
        (∃ n : N,
          family z.1 z.2 =
            family (selectedLabel n).1 (selectedLabel n).2) ∨
        designated (family z.1 z.2) ∨
        (family z.1 z.2).IsOneEdge := by
    intro z
    rcases (hLocal z.1).2.2 z.2 with ⟨r, hr⟩ | hd
    · cases r with
      | inl n =>
          left
          refine ⟨n.1, ?_⟩
          calc
            family z.1 z.2 = requested z.1 (.inl n) := hr
            _ = selectedGlobal n.1 :=
              hSelectedRequest z.1 n
            _ = family (selectedLabel n.1).1
                (selectedLabel n.1).2 :=
              (hSelectedPiece n.1).symm
      | inr r =>
          right
          right
          rw [hr]
          exact hConnectorOneEdge z.1 r
    · exact Or.inr (Or.inl
        (hDesignatedGlobal z.1 (family z.1 z.2) hd))
  obtain ⟨keep, hDone⟩ :=
    forestCompletion_witness_of_local_piece_classification
      hOuter JOuter hEdges hGirth
      hLocalAllowed JLocal hContain
      connector hConnector hConnectorEdge
      owner hSurj m hCard selectedLabel
      hSelectedOwner designated hClassification
  have hSelectedEq :
      (fun n : N =>
        family (selectedLabel n).1 (selectedLabel n).2) =
        selectedGlobal := by
    funext n
    exact hSelectedPiece n
  rw [hSelectedEq] at hDone
  exact ⟨keep, hDone⟩

end StructuralRamsey.Girth
