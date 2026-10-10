import Girth.ForestOwnerMixedRequests
import Girth.ForestJoinLiftLinear
import Girth.ForestAuxiliaryDeletion

/-!
# Lift forests on DISTINCT owner-local request sets

The checked outer join-tree lift does not require injective connector
labels. Consequently multiple neighbouring owners can use the SAME
one-edge connector label in one local forest. We therefore use one
local index per DISTINCT requested support piece, avoiding insertion
of duplicate one-edge requests entirely.

After lifting, discard precisely those local request pieces which
were not originally selected. Such a member must be a one-edge
separator, so checked one-edge deletion applies. Original selected
pieces are reindexed from their exact owner-dependent locations.

This is the structural direct forest-increment repeated-owner kernel.
The old mixed-set q-bound supplies the local hypotheses separately.
-/

namespace StructuralRamsey.Girth

universe v
variable {W Q N : Type v}

/-- Local forests on distinct request images, containing every
selected piece and the one-edge separators for all outer-tree
neighbours, assemble into exactly the original selected forest.
No duplicated separator labels or arbitrary subfamily restrictions. -/
theorem selectedForest_of_distinctOwnerRequestImages
    [Fintype Q] [Nonempty Q] [Fintype N]
    {P : Q → HypergraphPiece W}
    (hOuter : PairwiseAllowed P)
    (JOuter : JoinTree P)
    (hLinear : OuterEdgesLinear P)
    (owner : N → Q) (hSurj : Function.Surjective owner)
    (selected : N → HypergraphPiece W)
    (hSelectedInj : Function.Injective selected)
    (separator : (q : Q) → JOuter.tree.neighborSet q → HypergraphPiece W)
    (hLocal :
      ∀ q : Q, ForestOfCopies
        (fun z : {x : HypergraphPiece W //
          x ∈ finitePieceImage
            (fun t : {n : N // owner n = q} ⊕
                JOuter.tree.neighborSet q =>
              match t with
              | .inl n => selected n.1
              | .inr r => separator q r)} => z.1))
    (hSelectedContain :
      ∀ n, (selected n).carrier ⊆ (P (owner n)).carrier)
    (hSeparatorContain :
      ∀ q r, (separator q r).carrier ⊆ (P q).carrier)
    (hSeparatorOneEdge :
      ∀ q r, (separator q r).IsOneEdge)
    (hSeparatorCover :
      ∀ ⦃q r : Q⦄ (hadj : JOuter.tree.Adj q r),
        (P q).carrier ∩ (P r).carrier ⊆
          (separator q ⟨r, hadj⟩).carrier)
    (hSeparatorExact :
      ∀ ⦃q r : Q⦄ (hadj : JOuter.tree.Adj q r),
        ¬((P q).carrier ∩ (P r).carrier).Subsingleton →
          (separator q ⟨r, hadj⟩).carrier =
            (P q).carrier ∩ (P r).carrier) :
    ForestOfCopies selected := by
  classical
  let L : Q → Type v :=
    fun q => {n : N // owner n = q} ⊕ JOuter.tree.neighborSet q
  let R : (q : Q) → L q → HypergraphPiece W :=
    fun q t => match t with
      | .inl n => selected n.1
      | .inr r => separator q r
  let K : Q → Type v :=
    fun q => {x : HypergraphPiece W // x ∈ finitePieceImage (R q)}
  let F : (q : Q) → K q → HypergraphPiece W :=
    fun _ k => k.1
  letI : ∀ q : Q, Fintype (K q) := fun q => inferInstance
  have hRequestMem (q : Q) (t : L q) :
      R q t ∈ finitePieceImage (R q) := by
    change R q t ∈ Finset.univ.image (R q)
    exact Finset.mem_image.mpr ⟨t, Finset.mem_univ _, rfl⟩
  have hKNonempty (q : Q) : Nonempty (K q) := by
    obtain ⟨n, hn⟩ := hSurj q
    exact ⟨⟨selected n, hRequestMem q (.inl ⟨n, hn⟩)⟩⟩
  letI : ∀ q : Q, Nonempty (K q) := hKNonempty
  have hLocalForest : ∀ q : Q, ForestOfCopies (F q) := by
    intro q
    exact hLocal q
  let JLocal : ∀ q : Q, JoinTree (F q) :=
    fun q => Classical.choice ((hLocalForest q).joinTree_of_nonempty)
  have hLocalAllowed : ∀ q, PairwiseAllowed (F q) :=
    fun q => (hLocalForest q).pairwiseAllowed
  have hContain : ∀ q (k : K q),
      (F q k).carrier ⊆ (P q).carrier := by
    intro q k
    have hk : (k.1 : HypergraphPiece W) ∈
        Finset.univ.image (R q) := by
      simpa [K, finitePieceImage] using k.2
    obtain ⟨t, _, ht⟩ := Finset.mem_image.mp hk
    change (k.1 : HypergraphPiece W).carrier ⊆ (P q).carrier
    rw [← ht]
    cases t with
    | inl n =>
        change (selected n.1).carrier ⊆ (P q).carrier
        have hh := hSelectedContain n.1
        rw [n.2] at hh
        exact hh
    | inr r =>
        exact hSeparatorContain q r
  let defaultMember (q : Q) : K q := by
    obtain ⟨n, hn⟩ := hSurj q
    exact ⟨selected n, hRequestMem q (.inl ⟨n, hn⟩)⟩
  let connector (q r : Q) : K q :=
    if hadj : JOuter.tree.Adj q r then
      ⟨separator q ⟨r, hadj⟩,
        hRequestMem q (.inr ⟨r, hadj⟩)⟩
    else defaultMember q
  have hConnector :
      ∀ ⦃q r : Q⦄, JOuter.tree.Adj q r →
        (P q).carrier ∩ (P r).carrier ⊆
          (F q (connector q r)).carrier := by
    intro q r hadj
    simpa [F, connector, hadj] using hSeparatorCover hadj
  have hConnectorEdge :
      ∀ ⦃q r : Q⦄ (hadj : JOuter.tree.Adj q r),
        ¬((P q).carrier ∩ (P r).carrier).Subsingleton →
          (F q (connector q r)).IsOneEdge ∧
          (F q (connector q r)).carrier =
            (P q).carrier ∩ (P r).carrier := by
    intro q r hadj hBig
    simpa [F, connector, hadj] using
      (show (separator q ⟨r, hadj⟩).IsOneEdge ∧
          (separator q ⟨r, hadj⟩).carrier =
            (P q).carrier ∩ (P r).carrier from
        ⟨hSeparatorOneEdge q ⟨r, hadj⟩,
          hSeparatorExact hadj hBig⟩)
  have hJoined :
      ForestOfCopies (fun z : Sigma K => F z.1 z.2) :=
    forestOfCopies_lift_local_of_linear
      hOuter JOuter hLinear hLocalAllowed JLocal
      hContain connector hConnector hConnectorEdge
  let selectedLabel (n : N) : Sigma K :=
    ⟨owner n, ⟨selected n,
      hRequestMem (owner n) (.inl ⟨n, rfl⟩)⟩⟩
  have hLabelInj : Function.Injective selectedLabel := by
    intro n m heq
    apply hSelectedInj
    exact congrArg (fun z : Sigma K => (z.2.1 : HypergraphPiece W)) heq
  let keep : Finset (Sigma K) :=
    Finset.univ.image selectedLabel
  have hKeep (n : N) : selectedLabel n ∈ keep := by
    exact Finset.mem_image.mpr ⟨n, Finset.mem_univ _, rfl⟩
  have hAux :
      ∀ z : Sigma K, z ∉ keep →
        (F z.1 z.2).IsOneEdge := by
    intro z hz
    rcases z with ⟨q, k⟩
    have hk : (k.1 : HypergraphPiece W) ∈
        Finset.univ.image (R q) := by
      simpa [K, finitePieceImage] using k.2
    obtain ⟨t, _, ht⟩ := Finset.mem_image.mp hk
    cases t with
    | inl n =>
        obtain ⟨idx, hi⟩ := n
        have hkPiece : (k.1 : HypergraphPiece W) = selected idx := by
          simpa [R] using ht.symm
        subst q
        have hzLabel : (⟨owner idx, k⟩ : Sigma K) =
            selectedLabel idx := by
          apply congrArg (Sigma.mk (owner idx))
          exact Subtype.ext hkPiece
        exact (hz (hzLabel ▸ hKeep idx)).elim
    | inr r =>
        have hkPiece : (k.1 : HypergraphPiece W) = separator q r := by
          simpa [R] using ht.symm
        change (k.1 : HypergraphPiece W).IsOneEdge
        rw [hkPiece]
        exact hSeparatorOneEdge q r
  have hKept :
      ForestOfCopies
        (fun z : {z : Sigma K // z ∈ keep} =>
          F z.1.1 z.1.2) :=
    hJoined.restrict_of_oneEdge_outside keep hAux
  let label : N → {z : Sigma K // z ∈ keep} :=
    fun n => ⟨selectedLabel n, hKeep n⟩
  have hLabelBij : Function.Bijective label := by
    constructor
    · intro n m heq
      apply hLabelInj
      exact congrArg Subtype.val heq
    · intro z
      have hz : z.1 ∈ Finset.univ.image selectedLabel := by
        simpa [keep] using z.2
      obtain ⟨n, _, hn⟩ := Finset.mem_image.mp hz
      refine ⟨n, ?_⟩
      exact Subtype.ext hn
  let e : N ≃ {z : Sigma K // z ∈ keep} :=
    Equiv.ofBijective label hLabelBij
  have hResult := hKept.reindex e
  simpa [e, label, selectedLabel, F] using hResult

end StructuralRamsey.Girth
