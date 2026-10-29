import Girth.TrainRecursiveWitnessInitial
import Girth.InitialComponentForest
import Girth.ForestDisjoint
import Girth.ForestLocalEdgeGirth
import Girth.ForestUsedOwners
import Girth.ForestReindex
import Girth.ForestDesignatedBSupportTransport

/-!
# The complete initial mixed forest bound

The initial selected family consists of the literal disjoint B-components,
and the tested one-edge pieces include every ambient A-copy.  Irreducibility
places every such A-copy in one component.

For a selected finite family, only its used component owners are retained.
Inside one component, the actual selected B-centre gives the existing star
join tree.  When that centre is absent, all selected pieces are distinct
A-edges, so target support girth gives their forest directly.  The disjoint
component lifting theorem then combines these local forests.  In particular,
the proof never adds a B-centre and then deletes it from a join tree.

The target vertex type is finite, as required by the existing finite
one-edge forest theorem.  The full family of initial component indices need
not be finite.  No ordered rigidity or physical-label normalization is
needed: the tested family is a finite set of distinct complete pieces.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {UA VB W P I J : Type v}

/-- A finite selected family inside an embedded target is a forest: use its
actual B-centre if present, and otherwise use target girth for its A-edges. -/
theorem forest_selected_embeddedTarget_of_girthGT
    (A : RelStructure L UA) (B : RelStructure L VB) [Finite VB]
    {R : RelStructure L W} (b : RelStructure.Embedding B R)
    [Fintype J] (F : J → HypergraphPiece W) (hInj : Function.Injective F)
    (q : ℕ) (hq : 2 ≤ q) (hCard : Fintype.card J ≤ q)
    (hGirth : GirthGT (supportCopies A B) q)
    (hKind : ∀ j : J,
      F j = bSupportPiece A b ∨
        ∃ a : RelStructure.Embedding A B,
          F j = HypergraphPiece.oneEdge (copyCarrier (b.comp a))) :
    ForestOfCopies F := by
  classical
  letI : Fintype VB := Fintype.ofFinite VB
  by_cases hN : Nonempty J
  · letI : Nonempty J := hN
    by_cases hCentre : ∃ c : J, F c = bSupportPiece A b
    · obtain ⟨c, hc⟩ := hCentre
      let K := {j : J // j ≠ c}
      have hLeaves : ∀ k : K, ∃ a : RelStructure.Embedding A B,
          F k.1 = HypergraphPiece.oneEdge (copyCarrier (b.comp a)) := by
        intro k
        rcases hKind k.1 with hk | hk
        · exact (k.2 (hInj (hk.trans hc.symm))).elim
        · exact hk
      choose a ha using hLeaves
      have hDistinct : Function.Injective (fun k : K => copyCarrier (b.comp (a k))) := by
        intro k l h
        change copyCarrier (b.comp (a k)) = copyCarrier (b.comp (a l)) at h
        apply Subtype.ext
        apply hInj
        rw [ha k, ha l, h]
      have hMapped := girthGT_mappedSupportCopies A B R b hGirth
      have hPair : ∀ ⦃k l : K⦄, k ≠ l →
          (copyCarrier (b.comp (a k)) ∩ copyCarrier (b.comp (a l))).Subsingleton := by
        intro k l hkl
        exact pairwise_subsingleton_of_girthGT_two
          (girthGT_mono hMapped hq) ⟨a k, rfl⟩ ⟨a l, rfl⟩
          (fun h => hkl (hDistinct h))
      have hEdges : ∀ k : K,
          copyCarrier (b.comp (a k)) ∈ (bSupportPiece A b).edges := by
        intro k
        refine ⟨b.comp (a k), rfl, ?_⟩
        rintro x ⟨u, hu⟩
        exact ⟨a k u, hu⟩
      have hStar := forest_centerWithEdgeLeaves (bSupportPiece A b)
        (fun k : K => copyCarrier (b.comp (a k))) hEdges hPair
      let e : Option K ≃ J := Equiv.optionSubtypeNe c
      have hReindexed : ForestOfCopies (fun k : Option K => F (e k)) := by
        convert hStar using 1
        funext k
        cases k with
        | none => exact hc
        | some k => exact ha k
      simpa only [Equiv.apply_symm_apply] using hReindexed.reindex e.symm
    · have hEdges : ∀ j : J, ∃ a : RelStructure.Embedding A B,
          F j = HypergraphPiece.oneEdge (copyCarrier (b.comp a)) := by
        intro j
        rcases hKind j with h | h
        · exact (hCentre ⟨j, h⟩).elim
        · exact h
      choose a ha using hEdges
      have hSourceInj : Function.Injective (fun j : J => copyCarrier (a j)) := by
        intro j k h
        change copyCarrier (a j) = copyCarrier (a k) at h
        apply hInj
        rw [ha j, ha k, copyCarrier_comp_eq_image, copyCarrier_comp_eq_image, h]
      have hSourceGirth : GirthGT (Set.range (fun j : J => copyCarrier (a j))) q := by
        apply girthGT_of_subset _ hGirth
        rintro edge ⟨j, rfl⟩
        exact ⟨a j, rfl⟩
      have hForest := forest_oneEdge_family_of_girthGT
        (fun j : J => copyCarrier (a j)) hSourceInj q hq hCard hSourceGirth
      have hMappedForest := hForest.map b.toFunctionEmbedding
      convert hMappedForest using 1
      funext j
      rw [ha j, HypergraphPiece.oneEdge_map, copyCarrier_comp_eq_image]
  · letI : IsEmpty J := ⟨fun j => hN ⟨j⟩⟩
    exact ⟨fun j => isEmptyElim j, Or.inl inferInstance⟩

/-- All actual initial A-edges and precisely the literal B-component pieces
satisfy the mixed forest bound through the target's ordinary support girth. -/
theorem initialPicture_mixedForest_of_supportGirth
    (A : RelStructure L UA) (hA : A.Irreducible)
    (B : RelStructure L VB) [Finite VB]
    (β : I → VB ↪ P) [Nonempty I]
    (q : ℕ) (hq : 2 ≤ q) (hGirth : GirthGT (supportCopies A B) q) :
    FiniteMixedForestThrough
      (fun T : HypergraphPiece (I × VB) =>
        (∃ a : RelStructure.Embedding A
          (StructuralRamsey.Partite.Initial.picture B β).toRelStructure,
          T = HypergraphPiece.oneEdge (copyCarrier a)) ∨
        (∃ i : I, T = bSupportPiece A
          (StructuralRamsey.Partite.Initial.copyEmbedding B β i))) q := by
  classical
  intro s hTest hCard
  let N := {T : HypergraphPiece (I × VB) // T ∈ s}
  by_cases hN : Nonempty N
  · letI : Nonempty N := hN
    let copy (i : I) := StructuralRamsey.Partite.Initial.copyEmbedding B β i
    have hOwnership : ∀ n : N, ∃ i : I,
        n.1 = bSupportPiece A (copy i) ∨
          ∃ a : RelStructure.Embedding A B,
            n.1 = HypergraphPiece.oneEdge (copyCarrier ((copy i).comp a)) := by
      intro n
      rcases hTest n.1 n.2 with ⟨a, ha⟩ | ⟨i, hi⟩
      · obtain ⟨i, aB, hFactor⟩ := initialACopy_factors_component A hA B β a
        exact ⟨i, Or.inr ⟨aB, ha.trans (congrArg
          (fun e => HypergraphPiece.oneEdge (copyCarrier e)) hFactor)⟩⟩
      · exact ⟨i, Or.inl hi⟩
    choose owner hOwner using hOwnership
    let Q := UsedOwner owner
    letI : Fintype Q := usedOwnerFintype owner
    letI : Nonempty Q := usedOwner_nonempty owner
    let K : Q → Type v := fun i => {n : N // owner n = i.1}
    letI : ∀ i : Q, Fintype (K i) := fun i => inferInstance
    letI : ∀ i : Q, Nonempty (K i) := by
      intro i
      obtain ⟨n, hn⟩ := i.2
      exact ⟨⟨n, hn⟩⟩
    let outer : Q → HypergraphPiece (I × VB) :=
      fun i => bSupportPiece A (copy i.1)
    let localPiece : (i : Q) → K i → HypergraphPiece (I × VB) :=
      fun _ n => n.1.1
    have hLocal : ∀ i : Q, ForestOfCopies (localPiece i) := by
      intro i
      refine forest_selected_embeddedTarget_of_girthGT A B (copy i.1)
        (localPiece i) ?_ q hq ?_ hGirth ?_
      · intro n m h
        apply Subtype.ext
        exact Subtype.ext h
      · calc
          Fintype.card (K i) ≤ Fintype.card N := Fintype.card_subtype_le _
          _ = s.card := Fintype.card_coe _
          _ ≤ q := hCard
      · intro n
        simpa only [n.2] using hOwner n.1
    have hContain : ∀ (i : Q) (n : K i),
        (localPiece i n).carrier ⊆ (outer i).carrier := by
      intro i n
      have hKind := hOwner n.1
      rw [n.2] at hKind
      rcases hKind with hCentre | ⟨a, ha⟩
      · change n.1.1.carrier ⊆ (bSupportPiece A (copy i.1)).carrier
        rw [hCentre]
      · change n.1.1.carrier ⊆ (bSupportPiece A (copy i.1)).carrier
        rw [ha]
        rintro x ⟨u, hu⟩
        exact ⟨a u, hu⟩
    have hDisjoint : ∀ ⦃i j : Q⦄, i ≠ j →
        Disjoint (outer i).carrier (outer j).carrier := by
      intro i j hij
      rw [Set.disjoint_left]
      rintro x ⟨b, hb⟩ ⟨c, hc⟩
      apply hij
      apply Subtype.ext
      exact congrArg Prod.fst (hb.trans hc.symm)
    have hJoined := forestOfCopies_lift_disjoint hDisjoint hLocal hContain
    let e : N ≃ Sigma K := {
      toFun := fun n => ⟨usedOwnerMap owner n, ⟨n, rfl⟩⟩
      invFun := fun n => n.2.1
      left_inv := fun _ => rfl
      right_inv := by
        rintro ⟨⟨i, hi⟩, ⟨n, hn⟩⟩
        cases hn
        rfl
    }
    exact hJoined.reindex e
  · letI : IsEmpty N := ⟨fun n => hN ⟨n⟩⟩
    exact ⟨fun n => isEmptyElim n, Or.inl inferInstance⟩

namespace TrainRecursiveWitness

/-- The exact bottom-forest field for the literal selected initial picture.
The bound concerns a finite set of pieces, including every ambient A-edge. -/
theorem initialSelected_mixedForest
    (A : RelStructure L UA) (hA : A.Irreducible)
    (B : RelStructure L VB) [Finite VB]
    (D : RelStructure L P) (family : Set (RelStructure.Embedding B D))
    [Nonempty family]
    (q : ℕ) (hq : 2 ≤ q) (hGirth : GirthGT (supportCopies A B) q) :
    FiniteMixedForestThrough
      (testedAB A B D
        (StructuralRamsey.Partite.Initial.picture B
          (fun b : family => b.1.toFunctionEmbedding)) family
        (initialSelected B D family)) q := by
  intro s hTest hCard
  apply initialPicture_mixedForest_of_supportGirth A hA B
    (fun b : family => b.1.toFunctionEmbedding) q hq hGirth s ?_ hCard
  intro T hT
  rcases hTest T hT with ha | ⟨b, hb, hPiece⟩
  · exact Or.inl ha
  · obtain ⟨i, rfl⟩ := hb
    exact Or.inr ⟨i, hPiece⟩

end TrainRecursiveWitness
end StructuralRamsey.Girth
