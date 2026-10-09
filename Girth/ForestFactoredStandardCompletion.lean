import Girth.ForestCanonicalFullRange
import Girth.ForestStandardSupportFactor

/-!
# Forest completion for factored full standard-picture support

The generic two-carrier completion lemma expects several image-containment
and transport hypotheses. In the circulation construction all standard
pictures are full images of ONE old picture, while each local gluing
embedding factors through the corresponding full standard embedding.

This theorem discharges the following assumptions directly:
* small gluing carrier contained in its full standard carrier;
* small gluing edges are edges of the full standard support;
* full standard support edges belong to the ambient support;
* all selected/designated piece carriers are inside their standard image;
* every gluing one-A-edge separator is a transported old tested A-edge.

The remaining nonformalised application obligations are explicitly visible:
the actual designated owner of each selected A/B-piece, a forest of local
gluing copies, and exact pair intersections of DISTINCT full standard
pictures. This is not an end-to-end proof of the circulation proposition.
-/

namespace StructuralRamsey.Girth

universe v

variable {Src Old W Q N : Type v}

/-- A single old finite completion property gives completed forests after
the standard partite step, provided the concrete gluing maps, old support
and designated pieces satisfy the stated geometric conditions.

Unlike the abstract assembly theorem, the full standard pieces are
defined as the images of the same old full support piece under each
standard embedding. The five separate image/edge-containment inputs
are proved, not assumed. -/
theorem ForestCompletionProperty.assemble_factored_full_standards
    [Fintype Q] [Nonempty Q] [DecidableEq Q] [Fintype N]
    {H : Set (Set Src)} {K Ambient : Set (Set W)}
    (hSourceNonempty : H.Nonempty)
    (hSourceCover :
      ∀ x : Src, ∃ e : Set Src, e ∈ H ∧ x ∈ e)
    (outer : Q → StrongSupportEmbedding H K)
    (oldFull : HypergraphPiece Old)
    (hFullCarrier : oldFull.carrier = Set.univ)
    (standard : Q → Old ↪ W)
    (active : Q → Src ↪ Old)
    (hFactor : ∀ q (x : Src),
      outer q x = standard q (active q x))
    (hActiveEdges :
      ∀ q (e : Set Src), e ∈ H →
        (active q) '' e ∈ oldFull.edges)
    (hAmbientEdges :
      ∀ q (e : Set Old), e ∈ oldFull.edges →
        (standard q) '' e ∈ Ambient)
    (hInnerForest :
      ForestOfCopies (fun q : Q => (outer q).supportPiece))
    (hPair :
      ∀ ⦃q r : Q⦄, q ≠ r →
        (oldFull.map (standard q)).carrier ∩
          (oldFull.map (standard r)).carrier =
        (outer q).supportPiece.carrier ∩
          (outer r).supportPiece.carrier)
    (hAmbientGirth : GirthGT Ambient 2)
    (owner : N → Q)
    (hSurj : Function.Surjective owner)
    (m : ℕ)
    (hCard : Fintype.card N ≤ m)
    (selectedGlobal : N → HypergraphPiece W)
    (testedOld designatedOld : HypergraphPiece Old → Prop)
    (hOld : ForestCompletionProperty testedOld designatedOld m)
    (hTestSelected :
      ∀ n : N,
        TransportedPiece testedOld (standard (owner n))
          (selectedGlobal n))
    (hTestActiveEdge :
      ∀ q (e : Set Src), e ∈ H →
        testedOld (HypergraphPiece.oneEdge ((active q) '' e)))
    (designated : HypergraphPiece W → Prop)
    (hDesignatedGlobal :
      ∀ q (S : HypergraphPiece Old), designatedOld S →
        designated (S.map (standard q))) :
    ∃ (T : Q → Type v),
      ∃ (finite : ∀ q, Fintype (T q)),
        letI : ∀ q, Fintype (T q) := finite
        ∃ (family : (q : Q) → T q → HypergraphPiece W),
        ∃ keep : Finset (Sigma T),
          ForestCompletionWitness selectedGlobal designated
            (fun z : {z : Sigma T // z ∈ keep} =>
              family z.1.1 z.1.2) := by
  classical
  let full : Q → HypergraphPiece W :=
    fun q => oldFull.map (standard q)
  have hFullRange (q : Q) :
      Set.range (standard q) ⊆ (full q).carrier := by
    intro y hy
    obtain ⟨x, rfl⟩ := hy
    change standard q x ∈ (standard q) '' oldFull.carrier
    exact ⟨x, by rw [hFullCarrier]; trivial, rfl⟩
  have hSmallSub (q : Q) :
      (outer q).supportPiece.carrier ⊆ (full q).carrier := by
    exact (outer q).supportPiece_carrier_subset_standard
      (active q) (standard q) (hFactor q) oldFull
      (fun x => by rw [hFullCarrier]; trivial)
  have hSmallEdges (q : Q) :
      (outer q).supportPiece.edges ⊆ (full q).edges := by
    exact (outer q).supportPiece_edges_subset_standard
      (active q) (standard q) (hFactor q) oldFull
      (hActiveEdges q)
  have hFullEdges (q : Q) :
      (full q).edges ⊆ Ambient := by
    exact oldFull.map_edges_subset_ambient
      (standard q) oldFull.edges Ambient
      Set.Subset.rfl (hAmbientEdges q)
  have hTestOneEdge :
      ∀ q (e : Set W), e ∈ (outer q).supportPiece.edges →
        TransportedPiece testedOld (standard q)
          (HypergraphPiece.oneEdge e) :=
    allGluingOneEdges_transported_of_factor
      outer active standard hFactor testedOld hTestActiveEdge
  exact ForestCompletionProperty.assemble_canonical_full_range
    hSourceNonempty hSourceCover outer full
    hInnerForest hSmallSub hPair hSmallEdges
    (fun q e he => hFullEdges q he) hAmbientGirth
    owner hSurj m hCard selectedGlobal
    testedOld designatedOld hOld standard
    hFullRange hTestSelected hTestOneEdge
    designated hDesignatedGlobal

end StructuralRamsey.Girth
