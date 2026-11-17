import Girth.Track1FullSelectedSupportPieces
import Girth.LocalForestPieces
import Girth.ForestMixedLocalForestBridge

namespace StructuralRamsey.Girth

universe v

variable {V I W : Type v} {H : ColouredEdgeOwnerSplit V I}

/-- The actual selected owner split is a strong support embedding in the
interface used by the partite picture construction. -/
noncomputable def ColouredOwnerSelectedCopy.toStrongSupportEmbedding
    (S : ColouredOwnerSelectedCopy (W := W) H)
    (hStrong : ∀ f : H.OldEdge, ∀ x y : H.Vertex,
      x ≠ y → x ∈ H.splitEdge f → y ∈ H.splitEdge f →
      x ∈ Set.range S.lift → y ∈ Set.range S.lift →
      ∃ a : S.SourceEdge, S.physicalEdge a = f) :
    StrongSupportEmbedding S.sourceEdges H.splitPhysicalEdges where
  toFun := S.lift
  injective := S.lift_injective
  map_edge e he := by
    let a : S.SourceEdge := ⟨e, he⟩
    exact ⟨H.splitEdge (S.physicalEdge a), ⟨S.physicalEdge a, rfl⟩,
      (S.lift_source_edge a).symm⟩
  reflect_edge E hE hMeet := by
    obtain ⟨f, rfl⟩ := hE
    obtain ⟨x, hx, y, hy, hDifferent⟩ := Set.not_subsingleton_iff.mp hMeet
    obtain ⟨a, rfl⟩ := hStrong f x y hDifferent hx.1 hy.1 hx.2 hy.2
    exact ⟨a.1, a.2, (S.lift_source_edge a).symm⟩

/-- The partite strong-support adapter carries exactly the existing lifted
piece. Thus it preserves the already established mixed forest invariant. -/
theorem ColouredOwnerSelectedCopy.toStrongSupportEmbedding_supportPiece
    (S : ColouredOwnerSelectedCopy (W := W) H)
    (hStrong : ∀ f : H.OldEdge, ∀ x y : H.Vertex,
      x ≠ y → x ∈ H.splitEdge f → y ∈ H.splitEdge f →
      x ∈ Set.range S.lift → y ∈ Set.range S.lift →
      ∃ a : S.SourceEdge, S.physicalEdge a = f) :
    (S.toStrongSupportEmbedding hStrong).supportPiece = S.selectedLiftSupportPiece := by
  have hEdges : (S.toStrongSupportEmbedding hStrong).supportPiece.edges =
      S.selectedLiftSupportPiece.edges := by
    ext e
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ⟨⟨a, ha⟩, S.lift_source_edge ⟨a, ha⟩⟩
    · rintro ⟨a, rfl⟩
      exact ⟨a.1, a.2, (S.lift_source_edge a).symm⟩
  have hCarrier : (S.toStrongSupportEmbedding hStrong).supportPiece.carrier =
      S.selectedLiftSupportPiece.carrier := rfl
  generalize (S.toStrongSupportEmbedding hStrong).supportPiece = F at *
  generalize S.selectedLiftSupportPiece = G at *
  cases F
  cases G
  simp_all

/-- Exact owner-split coverage transports transversality from the selected
source to every ambient split edge. -/
theorem ColouredEdgeOwnerSplit.edgeTransversal_of_selected
    {J : Type v} (selected : J → ColouredOwnerSelectedCopy (W := W) H)
    (E : Set (Set W)) (part : W → I) (hTrans : EdgeTransversal E part)
    (hSource : ∀ j, (selected j).sourceEdges = E)
    (hPart : ∀ j x, H.newPredicate ((selected j).lift x) = part x)
    (hOwned : ∀ f : H.OldEdge, ∃ j, ∃ a : (selected j).SourceEdge,
      (selected j).physicalEdge a = f) :
    EdgeTransversal H.splitPhysicalEdges H.newPredicate := by
  intro e he p
  obtain ⟨f, rfl⟩ := he
  obtain ⟨j, a, rfl⟩ := hOwned f
  have ha : a.1 ∈ E := hSource j ▸ a.2
  obtain ⟨x, hx, hUnique⟩ := hTrans a.1 ha p
  rw [← (selected j).lift_source_edge a]
  refine ⟨(selected j).lift x, ⟨⟨x, hx.1, rfl⟩, (hPart j x).trans hx.2⟩, ?_⟩
  rintro z ⟨⟨y, hy, rfl⟩, hz⟩
  exact congrArg (selected j).lift (hUnique y ⟨hy, (hPart j y).symm.trans hz⟩)

/-- The indexed local forest bound applies to finite sets of actual pieces.
Choosing one label per piece is injective on the chosen finite set. -/
theorem LocalForestThrough.toFiniteMixedForestThrough_of_representatives
    {X Q : Type v} {pieces : Q → HypergraphPiece X} {m : ℕ}
    {tested : HypergraphPiece X → Prop}
    (hLocal : LocalForestThrough pieces m)
    (hRepresent : ∀ P, tested P → P ∈ Set.range pieces) :
    FiniteMixedForestThrough tested m := by
  classical
  intro s hTest hCard
  let K := {P : HypergraphPiece X // P ∈ s}
  letI : Fintype K := Finset.fintypeCoeSort s
  have hRep (P : K) : ∃ q, pieces q = P.1 := hRepresent P.1 (hTest P.1 P.2)
  let rep : K → Q := fun P => Classical.choose (hRep P)
  have hRepEq (P : K) : pieces (rep P) = P.1 := Classical.choose_spec (hRep P)
  let index : K ↪ Q := ⟨rep, fun P R h => Subtype.ext
    ((hRepEq P).symm.trans ((congrArg pieces h).trans (hRepEq R)))⟩
  have hSize : Fintype.card K ≤ m := by
    simpa [K] using hCard
  have hForest := hLocal K index hSize
  have hFamilies : (fun P : K => pieces (index P)) = fun P : K => P.1 :=
    funext hRepEq
  rw [hFamilies] at hForest
  exact hForest

/-- If the edge source has a positive tuple listing all its vertices, a
decorated witness has exactly the prescribed support, even with unused
vertices outside its support edges. -/
theorem decorateSupport_supportCopies_of_fullTuple
    {L : RelLanguage} {U X : Type v} [Finite U]
    (A : RelStructure L U) (E : Set (Set X)) (part : X → U)
    (hTrans : EdgeTransversal E part) (R : L.Symbol)
    (tuple : Fin (L.arity R) → U) (hRel : A.rel R tuple)
    (hFull : Function.Surjective tuple) :
    supportCopies A (decorateSupport A E part) = E := by
  apply supportCopies_eq_of_decorated_cover
  · intro e he
    exact ⟨decorateSupport_edgeEmbedding A hTrans he,
      decorateSupport_edgeCarrier A hTrans he⟩
  · intro a
    obtain ⟨e, he, hPoints, _⟩ := (a.map_rel_iff R tuple).mpr hRel
    refine ⟨e, he, ?_⟩
    rintro _ ⟨x, rfl⟩
    obtain ⟨i, rfl⟩ := hFull x
    exact hPoints i

#print axioms StructuralRamsey.Girth.ColouredOwnerSelectedCopy.toStrongSupportEmbedding
#print axioms StructuralRamsey.Girth.ColouredOwnerSelectedCopy.toStrongSupportEmbedding_supportPiece
#print axioms StructuralRamsey.Girth.ColouredEdgeOwnerSplit.edgeTransversal_of_selected
#print axioms StructuralRamsey.Girth.LocalForestThrough.toFiniteMixedForestThrough_of_representatives
#print axioms StructuralRamsey.Girth.decorateSupport_supportCopies_of_fullTuple

end StructuralRamsey.Girth
