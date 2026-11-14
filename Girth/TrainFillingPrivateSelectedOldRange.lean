import Girth.TrainFillingPrivateSelectedStageFilling

set_option Elab.async false

/-!
# Exact old selected support range, with no new strongness hypothesis

The canonical OrderStage filling theorem uses old copyEdges(i)
consisting of ALL ambient physical A-support edges wholly contained
in the selected parent vertex carrier. The indexed parentwise
realization naturally uses old copyEdges(i) = range(beta_i).

For a genuine induced relational embedding b : M -> N, these
two descriptions coincide. Any ambient A-copy whose carrier lies
in b(M) factors through b, so its carrier is an image of a genuine
A-support edge of M. This requires no extra "strong" hypothesis
because the complete carrier is already contained. The converse
is immediate from the exact image-carrier law.

Composing with the already proved exact contracted first-wagon
equivalence yields the same equality for the actual selected
shorter-stage map beta : (choice, first wagon) -> H.OldEdge.
No ambient edge deletion, output girth or fictitious edge label.
-/

namespace StructuralRamsey.Girth.UniformFillingData

open StructuralRamsey.RelStructure

universe u v

variable {L : RelLanguage.{u}}
variable {UA W V X : Type v}
variable (H : UniformFillingData V X)

/-- The image of the actual selected relational A-support embedding
is EXACTLY the set of complete ambient A-support edges contained in
the selected B-copy carrier. No extra A-strongness assumption. -/
theorem selectedSupportOldEdgeEmbedding_range_eq_contained
    (A : RelStructure L UA)
    (M : RelStructure L W) (N : RelStructure L V)
    (b : Embedding M N)
    (hOld : H.oldEdges = supportCopies A N) :
    Set.range (H.selectedSupportOldEdgeEmbedding A M N b hOld) =
      {f : H.OldEdge | f.1 ⊆ copyCarrier b} := by
  classical
  ext f
  constructor
  · rintro ⟨e, rfl⟩
    rw [H.selectedSupportOldEdgeEmbedding_carrier]
    rintro z ⟨x, hx, rfl⟩
    exact ⟨x, rfl⟩
  · intro hf
    have hSupport : f.1 ∈ supportCopies A N := by
      rw [← hOld]
      exact f.2
    obtain ⟨a, ha⟩ := hSupport
    have hFactor : ∀ u : UA, ∃ w : W, a u = b w := by
      intro u
      have hu : a u ∈ f.1 := by
        rw [ha]
        exact ⟨u, rfl⟩
      obtain ⟨w, hw⟩ := hf hu
      exact ⟨w, hw.symm⟩
    let q : Embedding A M := a.factorThroughRange b hFactor
    let e : {g : Set W // g ∈ supportCopies A M} :=
      ⟨copyCarrier q, ⟨q, rfl⟩⟩
    refine ⟨e, ?_⟩
    apply Subtype.ext
    have hbq : b.comp q = a := by
      apply Embedding.ext
      intro u
      exact (Classical.choose_spec (hFactor u)).symm
    calc
      (H.selectedSupportOldEdgeEmbedding A M N b hOld e).1 =
          b.toFunctionEmbedding '' copyCarrier q :=
        H.selectedSupportOldEdgeEmbedding_carrier A M N b hOld e
      _ = copyCarrier (b.comp q) :=
        UniformPrivateTemplate.image_copyCarrier_comp A M N b q
      _ = copyCarrier a := congrArg copyCarrier hbq
      _ = f.1 := ha.symm

end StructuralRamsey.Girth.UniformFillingData

namespace StructuralRamsey.Girth.IndexedPrivateChoice

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {C V P X UA : Type v}
variable (U : C → PrivateWagonInput V P X)

/-- The entire old support-edge image of a genuinely selected
shorter-stage M-copy equals the old A-support edges contained in
its true vertex carrier. This identifies the old copyEdges input
of the canonical all-cut OrderStage filling theorem with the
cover-pullback data used in the indexed parentwise realization. -/
theorem actualSelectedFilledOldEdgeEmbedding_range_eq_contained [Nontrivial X]
    (A : RelStructure L UA)
    (M : RelStructure L (Vertex U))
    {t : List ℕ} (T : EdgeTrainLevels P t.length) (hm : 0 < t.length)
    (hSupport : supportCopies A M = Set.range (contractedCarrier U))
    (hLinear : ∀ c : C, ∀ p q : P, p ≠ q →
      ((U c).oldCarrier p ∩ (U c).oldCarrier q).Subsingleton)
    {Base : Type v} (D : RelStructure L Base)
    (family : Set (Embedding M D))
    (allowed : Fin (t.length + 1) → Set Base)
    (S : TrainRecursiveWitness.ForestTailStage A M D family t
      (contractedPhysicalTrain U A M T hm hSupport hLinear) allowed)
    (b : DesignatedCopy M D S.system family)
    (H : UniformFillingData S.Vertex X)
    (hOld : H.oldEdges = supportCopies A S.system.toRelStructure) :
    Set.range (actualSelectedFilledOldEdgeEmbedding U A M T hm
      hSupport hLinear D family allowed S b H hOld) =
      {f : H.OldEdge | f.1 ⊆ copyCarrier b.embedding} := by
  let ψ := contractedPhysicalEdgeEquiv U A M hSupport hLinear
  let χ := H.selectedSupportOldEdgeEmbedding A M
    S.system.toRelStructure b.embedding hOld
  have hRange :
      Set.range (actualSelectedFilledOldEdgeEmbedding U A M T hm
        hSupport hLinear D family allowed S b H hOld) =
        Set.range χ := by
    ext f
    constructor
    · rintro ⟨cp, hcp⟩
      exact ⟨ψ cp, hcp⟩
    · rintro ⟨e, he⟩
      obtain ⟨cp, hcp⟩ := ψ.surjective e
      refine ⟨cp, ?_⟩
      change χ (ψ cp) = f
      rw [hcp]
      exact he
  exact hRange.trans
    (H.selectedSupportOldEdgeEmbedding_range_eq_contained A M
      S.system.toRelStructure b.embedding hOld)

end StructuralRamsey.Girth.IndexedPrivateChoice
