import Girth.FiniteTraceChordalEndpoint
import Girth.MixedForestInduction

/-!
# Induced extraction from bounded internal forest completions

A trace-dominating selection preserves every positive-arity tuple whose
vertices lie in the tested set. After forest completion, a nonempty family
also preserves nullary relations. The embedding of its amalgamation union
then sends the tested induced structure into a supported tree amalgam.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}} {UA VB W ι : Type v}

/-- Exact extraction from a member-generated union. A member is needed
for every ambient tuple on Z of positive arity. A nonempty family
suffices for arity zero. -/
def inducedToMixedFamilyUnion
    {A : RelStructure L UA} {B : RelStructure L VB}
    (R : RelStructure L W) (m : ι → ABMember A B R) (Z : Set W)
    [Nonempty ι]
    (hVertices : ∀ x ∈ Z, ∃ i, x ∈ (m i).carrier)
    (hRelations : ∀ (r : L.Symbol), 0 < L.arity r →
      ∀ t : Fin (L.arity r) → Z, R.rel r (Subtype.val ∘ t) →
        ∃ i, ∀ j, (t j).val ∈ (m i).carrier) :
    Embedding (R.induce Z) (mixedFamilyUnionStructure R m) where
  toFun z := ⟨z.1, by
    obtain ⟨i, hz⟩ := hVertices z.1 z.2
    exact Set.mem_iUnion.mpr ⟨i, hz⟩⟩
  injective := fun _ _ h =>
    Subtype.ext (congrArg (fun z : mixedFamilyCarrier m => z.val) h)
  map_rel_iff := by
    intro r t
    change (R.rel r (Subtype.val ∘ t) ∧
      ∃ i, ∀ j, (t j).val ∈ (m i).carrier) ↔
        R.rel r (Subtype.val ∘ t)
    refine ⟨And.left, fun hr => ⟨hr, ?_⟩⟩
    rcases Nat.eq_zero_or_pos (L.arity r) with hArity | hArity
    · obtain ⟨i⟩ := (inferInstance : Nonempty ι)
      exact ⟨i, fun j => Fin.elim0 (hArity ▸ j)⟩
    · exact hRelations r hArity t hr

/-- Apply trace selection and actual internal forest completion, then
embed the resulting relational union into a supported tree amalgam.
Only the existence of forest completions and shared-vertex support
must come from the outer Ramsey construction. -/
theorem smallInducedStructure_embeds_supportedTree_of_forestCompletion
    [Fintype W] [Fintype ι] [Nonempty ι]
    {A : RelStructure L UA} {B : RelStructure L VB}
    (R : RelStructure L W) (m : ι → ABMember A B R) (Z : Set W) (q : ℕ)
    (hq : 1 ≤ q) (hBudget : Z.ncard ≤ q)
    (hVertices : ∀ x ∈ Z, ∃ i, x ∈ (m i).carrier)
    (hRelations : ∀ (r : L.Symbol), 0 < L.arity r →
      ∀ t : Fin (L.arity r) → Z, R.rel r (Subtype.val ∘ t) →
        ∃ i, ∀ j, (t j).val ∈ (m i).carrier)
    (hShared : PairwiseMixedSharedVerticesSupported A m)
    (hComplete : ∀ N : Finset ι, N.Nonempty → N.card ≤ q →
      ∃ S : Finset ι, N ⊆ S ∧
        ForestOfCopies (fun i : {j // j ∈ S} => (m i.val).supportPiece A))
    (alphaB : Embedding A B) (a0 a1 : UA) (hne : a0 ≠ a1) :
    ∃ (X : Type v) (T : RelStructure L X)
        (_ : Embedding (R.induce Z) T),
      ASupportedTreeAmalgam A B X T := by
  classical
  let F (i : ι) := (m i).carrier
  have hLocal : HasInternalJoinTreeCompletions F q := by
    intro N hN hCard
    obtain ⟨S, hSub, hForest⟩ := hComplete N hN hCard
    obtain ⟨i, hi⟩ := hN
    letI : Nonempty {j // j ∈ S} := ⟨⟨i, hSub hi⟩⟩
    obtain ⟨J⟩ := hForest.joinTree_of_nonempty
    refine ⟨S, hSub, ⟨⟨J.tree, J.isTree, ?_⟩⟩⟩
    intro x
    change (J.tree.induce {i : {j : ι // j ∈ S} | x ∈ (m i.val).carrier}).Preconnected
    have hOccurrences :
        {i : {j : ι // j ∈ S} | x ∈ ((m i.val).supportPiece A).carrier} =
          {i : {j : ι // j ∈ S} | x ∈ (m i.val).carrier} := by
      ext i
      change x ∈ ((m i.val).supportPiece A).carrier ↔ x ∈ (m i.val).carrier
      rw [ABMember.supportPiece_carrier]
    rw [← hOccurrences]
    exact J.running x
  have chooseRequest : ∃ N : Finset ι, N.Nonempty ∧ N.card ≤ q ∧
      CoversNonemptyTraces F Z (N : Set ι) := by
    by_cases hZ : Z.Nonempty
    · obtain ⟨selected, hSel, hCard⟩ :=
        smallTrace_selection_of_local_completions F Z q hVertices hLocal hBudget
      obtain ⟨x, hx⟩ := hZ
      obtain ⟨i, hi, _⟩ := hSel.vertex_coverage hVertices hx
      let hFinite := selected.toFinite
      refine ⟨hFinite.toFinset, hFinite.toFinset_nonempty.mpr ⟨i, hi⟩, ?_, ?_⟩
      · rw [← Set.ncard_eq_toFinset_card selected hFinite]
        exact hCard.trans hBudget
      · simpa only [hFinite.coe_toFinset] using hSel
    · let i : ι := Classical.choice inferInstance
      refine ⟨{i}, Finset.singleton_nonempty i, by simpa using hq, ?_⟩
      intro j hTrace
      obtain ⟨x, hx⟩ := hTrace
      exact (hZ ⟨x, hx.2⟩).elim
  obtain ⟨N, hN, hCard, hTrace⟩ := chooseRequest
  obtain ⟨S, hSub, hForest⟩ := hComplete N hN hCard
  obtain ⟨i0, hi0⟩ := hN
  letI : Nonempty {j // j ∈ S} := ⟨⟨i0, hSub hi0⟩⟩
  let m' (i : {j // j ∈ S}) := m i.val
  have hVertices' : ∀ x ∈ Z, ∃ i, x ∈ (m' i).carrier := by
    intro x hx
    obtain ⟨i, hi, hxi⟩ := hTrace.vertex_coverage hVertices hx
    exact ⟨⟨i, hSub hi⟩, hxi⟩
  have hRelations' : ∀ (r : L.Symbol), 0 < L.arity r →
      ∀ t : Fin (L.arity r) → Z, R.rel r (Subtype.val ∘ t) →
        ∃ i, ∀ j, (t j).val ∈ (m' i).carrier := by
    intro r hr t ht
    obtain ⟨i, hi, hti⟩ := hTrace.tuple_coverage hr (Subtype.val ∘ t)
      (fun j => (t j).property) (hRelations r hr t ht)
    exact ⟨⟨i, hSub hi⟩, hti⟩
  have hShared' : PairwiseMixedSharedVerticesSupported A m' := by
    intro i j hij
    exact hShared (i := i.val) (j := j.val) (fun h => hij (Subtype.ext h))
  let extract := inducedToMixedFamilyUnion R m' Z hVertices' hRelations'
  obtain ⟨X, T, embed, hTree⟩ :=
    mixedForest_embeds_supportedTree hForest hShared' alphaB a0 a1 hne
  exact ⟨X, T, embed.comp extract, hTree⟩

end StructuralRamsey.Girth
