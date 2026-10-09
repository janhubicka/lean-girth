import Girth.ForestFactoredStandardCompletion
import Girth.ForestUsedOwnerLocalForest

/-!
# Quantified completion using exactly the distinct selected standard owners

The local forest Ramsey witness can contain very many designated gluing
copies and need not itself be one forest. The circulation completion
argument uses only the set of distinct gluing copies that actually own
the selected finite family N. This family has size at most |N|.

Here the support-piece forest is obtained from the local partite lemma's
BOUNDED-SUBFAMILY invariant, without asserting that arbitrary deletions
from a forest preserve foresthood. The standard-copy completion assembly
is then applied with precisely this finite owner subtype; its owner map
is surjective by construction. No unrelated standard copy is requested
to be part of the outer join tree.

The empty selected family is handled separately by
emptySelected_hasForestCompletion in ForestUsedOwners.  The true
remaining inputs to apply this theorem to the actual picture step are
the existence of the local Ramsey witness with its bounded-subfamily
forest property, concrete selected-piece ownership, factorization,
and designated transport.
-/

namespace StructuralRamsey.Girth

universe v
variable {Src Old W I N : Type v}

/-- One old completion invariant gives a completion of every nonempty
selected family of size <=m in a picture, using only the distinct
standard-copy owners that occur in the selected family.

No global forest of ALL local witness copies is assumed. -/
theorem ForestCompletionProperty.assemble_on_used_owners
    [Fintype N] [Nonempty N]
    {H : Set (Set Src)} {K Ambient : Set (Set W)}
    (hSourceNonempty : H.Nonempty)
    (hSourceCover :
      ∀ x : Src, ∃ e : Set Src, e ∈ H ∧ x ∈ e)
    (outer : I → StrongSupportEmbedding H K)
    (oldFull : HypergraphPiece Old)
    (hFullCarrier : oldFull.carrier = Set.univ)
    (standard : I → Old ↪ W)
    (active : I → Src ↪ Old)
    (hFactor : ∀ i (x : Src),
      outer i x = standard i (active i x))
    (hActiveEdges :
      ∀ i (e : Set Src), e ∈ H →
        (active i) '' e ∈ oldFull.edges)
    (hAmbientEdges :
      ∀ i (e : Set Old), e ∈ oldFull.edges →
        (standard i) '' e ∈ Ambient)
    (m : ℕ)
    (hLocalForest :
      LocalForestThrough (fun i : I => (outer i).supportPiece) m)
    (hPair :
      ∀ ⦃i j : I⦄, i ≠ j →
        (oldFull.map (standard i)).carrier ∩
          (oldFull.map (standard j)).carrier =
        (outer i).supportPiece.carrier ∩
          (outer j).supportPiece.carrier)
    (hAmbientGirth : GirthGT Ambient 2)
    (owner : N → I)
    (hCard : Fintype.card N ≤ m)
    (selectedGlobal : N → HypergraphPiece W)
    (testedOld designatedOld : HypergraphPiece Old → Prop)
    (hOld : ForestCompletionProperty testedOld designatedOld m)
    (hTestSelected :
      ∀ n : N, TransportedPiece testedOld
        (standard (owner n)) (selectedGlobal n))
    (hTestActiveEdge :
      ∀ i (e : Set Src), e ∈ H →
        testedOld (HypergraphPiece.oneEdge ((active i) '' e)))
    (designated : HypergraphPiece W → Prop)
    (hDesignatedGlobal :
      ∀ i (S : HypergraphPiece Old), designatedOld S →
        designated (S.map (standard i))) :
    ∃ (T : UsedOwner owner → Type v),
      ∃ (finite : ∀ q, Fintype (T q)),
        letI : ∀ q, Fintype (T q) := finite
        ∃ (family : (q : UsedOwner owner) →
          T q → HypergraphPiece W),
        ∃ keep : Finset (Sigma T),
          ForestCompletionWitness selectedGlobal designated
            (fun z : {z : Sigma T // z ∈ keep} =>
              family z.1.1 z.1.2) := by
  classical
  letI : Fintype (UsedOwner owner) := usedOwnerFintype owner
  letI : Nonempty (UsedOwner owner) := usedOwner_nonempty owner
  letI : DecidableEq (UsedOwner owner) := Classical.decEq _
  let actualOuter : UsedOwner owner → StrongSupportEmbedding H K :=
    fun q => outer q.1
  let actualStandard : UsedOwner owner → Old ↪ W :=
    fun q => standard q.1
  let actualActive : UsedOwner owner → Src ↪ Old :=
    fun q => active q.1
  have hForest :
      ForestOfCopies
        (fun q : UsedOwner owner => (actualOuter q).supportPiece) :=
    localForest_usedOwners owner
      (fun i : I => (outer i).supportPiece) m hLocalForest hCard
  have hPairs :
      ∀ ⦃q r : UsedOwner owner⦄, q ≠ r →
        (oldFull.map (actualStandard q)).carrier ∩
          (oldFull.map (actualStandard r)).carrier =
        (actualOuter q).supportPiece.carrier ∩
          (actualOuter r).supportPiece.carrier := by
    intro q r hne
    have hval : q.1 ≠ r.1 := by
      intro heq
      exact hne (Subtype.ext heq)
    exact hPair hval
  exact ForestCompletionProperty.assemble_factored_full_standards
    hSourceNonempty hSourceCover
    actualOuter oldFull hFullCarrier
    actualStandard actualActive
    (fun q => hFactor q.1)
    (fun q => hActiveEdges q.1)
    (fun q => hAmbientEdges q.1)
    hForest hPairs hAmbientGirth
    (usedOwnerMap owner) (usedOwnerMap_surjective owner)
    m hCard selectedGlobal testedOld designatedOld hOld
    hTestSelected
    (fun q => hTestActiveEdge q.1)
    designated
    (fun q => hDesignatedGlobal q.1)

end StructuralRamsey.Girth
