import Girth.ALinearRamsey
import Girth.ForestActualRecursiveSupport
import Girth.DesignatedBCopyTransportExact
import Girth.LinearityGirthTwo

/-!
# A concrete finite mixed Ramsey family at cutoff two

The existing functional EHN theorem returns a closed-target Ramsey family.
Its actual relational copies are strong, any two physically distinct target
copies have a controlled intersection, and the whole reduct is A-linear.
These facts give the full mixed forest bound through two, with every ambient
A-edge included. No covering assumption or deletion of ambient edges is used.

The final existence theorem retains the selected Ramsey family and its
strong images in one finite ambient structure. This supplies the Ramsey and
mixed-forest geometry of the base case. It does not assert ambient support
coverage, a prescribed partite projection, or a prescribed train parameter;
those additional fields are not consequences of the EHN endpoint used here.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}} {UA VB W I : Type v}

private theorem baseTwo_forest_of_pairwise
    {J : Type v} [Fintype J] (F : J → HypergraphPiece W)
    (hCard : Fintype.card J ≤ 2) (hPair : PairwiseAllowed F) :
    ForestOfCopies F := by
  classical
  by_cases hN : Nonempty J
  · obtain ⟨root⟩ := hN
    let K := {j : J // j ≠ root}
    have hKCard : Fintype.card K ≤ 1 := by
      have hEq := Fintype.card_congr (Equiv.optionSubtypeNe root)
      simp only [Fintype.card_option] at hEq
      change Fintype.card K + 1 = Fintype.card J at hEq
      omega
    letI : Subsingleton K := Fintype.card_le_one_iff_subsingleton.mp hKCard
    refine ⟨hPair, Or.inr ⟨{
      tree := SimpleGraph.starGraph root
      isTree := SimpleGraph.isTree_starGraph root
      running := ?_ }⟩⟩
    intro x
    by_cases hx : x ∈ (F root).carrier
    · exact starGraph_induce_preconnected_of_mem_center root hx
    · have hNonroot : ∀ j : {j : J | x ∈ (F j).carrier}, j.1 ≠ root := by
        intro j hEq
        have hj : x ∈ (F j.1).carrier := j.2
        exact hx (by simpa only [hEq] using hj)
      letI : Subsingleton {j : J | x ∈ (F j).carrier} := ⟨by
        intro a b
        apply Subtype.ext
        exact congrArg (fun k : K => k.1)
          (Subsingleton.elim (⟨a.1, hNonroot a⟩ : K) (⟨b.1, hNonroot b⟩ : K))⟩
      exact SimpleGraph.Preconnected.of_subsingleton
  · letI : IsEmpty J := ⟨fun j => hN ⟨j⟩⟩
    exact ⟨hPair, Or.inl inferInstance⟩

private theorem baseTwo_allowed_with_edge
    (A : RelStructure L UA) {B : RelStructure L VB} {D : RelStructure L W}
    (b : Embedding B D) (hStrong : AStrong A D (copyCarrier b))
    (a : Embedding A D) :
    AllowedIntersection (bSupportPiece A b)
      (HypergraphPiece.oneEdge (copyCarrier a)) := by
  by_cases hSmall : (copyCarrier b ∩ copyCarrier a).Subsingleton
  · exact Or.inl hSmall
  · have hSub : copyCarrier a ⊆ copyCarrier b :=
      hStrong a (by simpa only [Set.inter_comm] using hSmall)
    exact Or.inr ⟨copyCarrier a, ⟨a, rfl, hSub⟩, rfl, Set.inter_eq_right.mpr hSub⟩

/-- Actual strong relational copies with controlled pair intersections,
together with all ambient A-edges, satisfy the mixed forest bound through two.
The statement concerns a finite set of pieces and needs no injectivity of
the embedding labels or any normalization of duplicate physical copies. -/
theorem mixedForestThrough_two_of_strong_controlledFamily
    (A : RelStructure L UA) {B : RelStructure L VB} {D : RelStructure L W}
    (f : I → Embedding B D) (hLinear : ALinear A D)
    (hStrong : ∀ i, AStrong A D (copyCarrier (f i)))
    (hControlled : ∀ i j, ¬ SameCopy (f i) (f j) →
      (copyCarrier (f i) ∩ copyCarrier (f j)).Subsingleton ∨
        ∃ a : Embedding A D, copyCarrier (f i) ∩ copyCarrier (f j) = copyCarrier a) :
    FiniteMixedForestThrough (RelationalMixedSupportTest A f) 2 := by
  classical
  intro s hTest hCard
  apply baseTwo_forest_of_pairwise
  · simpa only [Fintype.card_coe] using hCard
  · intro P Q hPQ
    change AllowedIntersection P.1 Q.1
    have hNe : P.1 ≠ Q.1 := fun h => hPQ (Subtype.ext h)
    rcases hTest P.1 P.2 with ⟨i, hP⟩ | ⟨a, hP⟩
    · rcases hTest Q.1 Q.2 with ⟨j, hQ⟩ | ⟨a, hQ⟩
      · rw [hP, hQ]
        have hCopies : ¬ SameCopy (f i) (f j) := by
          intro h
          exact hNe (hP.trans ((bSupportPiece_eq_of_sameCopy A (f i) (f j) h).trans hQ.symm))
        rcases hControlled i j hCopies with hSmall | ⟨a, hInter⟩
        · exact Or.inl hSmall
        · right
          refine ⟨copyCarrier a, ⟨a, rfl, ?_⟩, ⟨a, rfl, ?_⟩, hInter⟩
          · rw [← hInter]
            exact Set.inter_subset_left
          · rw [← hInter]
            exact Set.inter_subset_right
      · rw [hP, hQ]
        exact baseTwo_allowed_with_edge A (f i) (hStrong i) a
    · rcases hTest Q.1 Q.2 with ⟨j, hQ⟩ | ⟨b, hQ⟩
      · rw [hP, hQ]
        exact allowedIntersection_symm (baseTwo_allowed_with_edge A (f j) (hStrong j) a)
      · rw [hP, hQ]
        left
        apply hLinear a b
        intro h
        exact hNe (hP.trans ((congrArg HypergraphPiece.oneEdge h).trans hQ.symm))

/-- The genuine full target embeddings supplied by EHN satisfy the mixed
two-forest invariant on the complete ambient A-support. -/
theorem closedTarget_mixedForest_two
    (A : RelStructure L UA) (B : RelStructure L VB) [Finite VB]
    (C : StructuralRamsey.Structure (closureLanguage L) W)
    (hB : ALinear A B) (hC : ElementaryCAClass A C) :
    FiniteMixedForestThrough
      (RelationalMixedSupportTest A
        (fun b : StructuralRamsey.Structure.Embedding
          (targetClosureExpansion A B) C => targetEmbeddingRel b)) 2 := by
  apply mixedForestThrough_two_of_strong_controlledFamily A _ hC.1
  · intro b
    exact targetEmbedding_range_aStrong hC.2 b
  · intro b c hNe
    exact targetEmbeddings_controlledIntersection hB b c hNe

/-- A finite selected Ramsey family with the complete mixed forest bound
through two. The auxiliary source and target orders need only be respected
by A-embeddings into B, as in the existing fixed-target EHN endpoint. -/
theorem baseTwoRamseyFamily_of_monotone_embeddings
    (A : RelStructure L UA) (B : RelStructure L VB)
    [LinearOrder UA] [LinearOrder VB] [Finite UA] [Finite VB]
    (hA : A.Irreducible) (hB : ALinear A B)
    (hMono : ∀ a : Embedding A B, StrictMono a)
    (κ : Type*) [Fintype κ] [Nonempty κ] :
    ∃ (W : Type v) (_ : Finite W) (D : RelStructure L W)
      (family : Set (Embedding B D)),
      ALinear A D ∧ GirthGT (supportCopies A D) 2 ∧
      FiniteMixedForestThrough
        (RelationalMixedSupportTest A (fun b : family => b.1)) 2 ∧
      (∀ b : Embedding B D, b ∈ family →
        AStrong A D (copyCarrier b)) ∧
      (∀ χ : Embedding A D → κ,
        ∃ b : Embedding B D, b ∈ family ∧
          ∀ a₁ a₂ : Embedding A B,
            χ (b.comp a₁) = χ (b.comp a₂)) := by
  classical
  obtain ⟨W, hW, _, C, hC, hRamsey⟩ :=
    closedTargetRamseyFamily_of_monotone_embeddings A B hA hB hMono κ
  let D := closureRelReduct C
  let family : Set (Embedding B D) :=
    Set.range (fun b : StructuralRamsey.Structure.Embedding
      (targetClosureExpansion A B) C => targetEmbeddingRel b)
  refine ⟨W, hW, D, family, hC.1, girthGT_two_of_aLinear _ _ hC.1, ?_, ?_, ?_⟩
  · have hForest := closedTarget_mixedForest_two A B C hB hC
    intro s hTest hCard
    apply hForest s ?_ hCard
    intro P hP
    rcases hTest P hP with ⟨b, hb⟩ | ha
    · obtain ⟨c, hc⟩ := b.2
      exact Or.inl ⟨c, by simpa only [hc] using hb⟩
    · exact Or.inr ha
  · intro b hb
    obtain ⟨c, rfl⟩ := hb
    exact targetEmbedding_range_aStrong hC.2 c
  · intro χ
    obtain ⟨b, hb⟩ := hRamsey χ
    exact ⟨targetEmbeddingRel b, ⟨b, rfl⟩, hb⟩

/-- For finite ordered source and target structures, irreducibility and
auxiliary-order monotonicity are discharged by the distinguished order. -/
theorem baseTwoRamseyFamily_ordered_source
    (A₀ : RelStructure L UA) (B₀ : RelStructure L VB)
    [LinearOrder UA] [LinearOrder VB] [Finite UA] [Finite VB]
    (hB : ALinear A₀.ordered B₀.ordered)
    (κ : Type*) [Fintype κ] [Nonempty κ] :
    ∃ (W : Type v) (_ : Finite W) (D : RelStructure L.withOrder W)
      (family : Set (Embedding B₀.ordered D)),
      ALinear A₀.ordered D ∧ GirthGT (supportCopies A₀.ordered D) 2 ∧
      FiniteMixedForestThrough
        (RelationalMixedSupportTest A₀.ordered (fun b : family => b.1)) 2 ∧
      (∀ b : Embedding B₀.ordered D, b ∈ family →
        AStrong A₀.ordered D (copyCarrier b)) ∧
      (∀ χ : Embedding A₀.ordered D → κ,
        ∃ b : Embedding B₀.ordered D, b ∈ family ∧
          ∀ a₁ a₂ : Embedding A₀.ordered B₀.ordered,
            χ (b.comp a₁) = χ (b.comp a₂)) := by
  apply baseTwoRamseyFamily_of_monotone_embeddings A₀.ordered B₀.ordered
  · exact (RelStructure.ordered_hereditarilyIrreducible A₀).irreducible
  · exact hB
  · intro a
    exact RelStructure.Embedding.strictMono a

end StructuralRamsey.Girth
