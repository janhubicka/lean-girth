import Girth.TrainWagonClassRestriction
import Girth.TrainAllAdjacentParameterPreservation

set_option autoImplicit false
set_option Elab.async false

/-!
# Adjacent train parameters under exact edge-label and vertex restriction

The q>2 lower recursion uses the TRUE active support, not a pruned
ambient system. Two honest changes of type are needed to transfer
the old stage's complete AdjacentParameters invariant:

1. keep only genuine active A-edge labels by an injective map to
   all old ambient A-edge labels, reflecting every train equivalence;
2. replace ambient vertices by the induced active subtype and each
   physical carrier by its literal preimage.

A surviving wagon CLASS embeds into its unique old class. Exact
parent compatibility is inherited by this embedding. Since the
new wagon carrier is a subset of its old carrier, the complete
sibling-intersection bound also descends. No distinct physical
wagons are identified because their carriers happen to coincide.

The second transport uses the SAME edge labels and train, but
changes the vertex type. Every new carrier point maps to an old
carrier point, so the old intersection bound pulls back. The
vertex map need not be injective for this elementary intersection
property; the actual true-active inclusion IS injective.

These are only parameter-preservation kernels, not a new
FirstWagonRefinement, initial global labelled girth, lower
forest witness or attached SupremeCycleBound. Circulation only.
-/

namespace StructuralRamsey.Girth

universe v
variable {E F W V : Type v}

/-- Exact parent compatibility for the injection of genuine
surviving quotient wagon labels into original wagon labels. -/
theorem EdgeTrainLevels.wagonClassEmbedding_parent
    {m : ℕ} (T : EdgeTrainLevels E m)
    (keep : F ↪ E) (μ ν : Fin (m + 1)) (hμν : μ ≤ ν)
    (a : Quotient ((T.restrict keep).wagonSetoid μ)) :
    T.wagonClassEmbedding keep ν
      ((T.restrict keep).wagonParent μ ν hμν a) =
    T.wagonParent μ ν hμν
      (T.wagonClassEmbedding keep μ a) := by
  induction a using Quotient.inductionOn with
  | h a => rfl

/-- All sibling-intersection parameters survive literal restriction
of the edge labels and shrinking of their physical vertex carriers.
The new labelled quotient wagon classes inject into the old ones. -/
theorem EdgeTrainLevels.adjacentParameters_restrict
    {m : ℕ} (T : EdgeTrainLevels E m)
    (oldEdges : E → Set W) (keep : F ↪ E)
    (newEdges : F → Set W)
    (hShrink : ∀ e : F, newEdges e ⊆ oldEdges (keep e))
    (allowed : Fin (m + 1) → Set W)
    (hOld : T.AdjacentParameters oldEdges allowed) :
    (T.restrict keep).AdjacentParameters newEdges allowed := by
  intro μ ν hμν hSucc a b hne hParent x hx
  let embedChild := T.wagonClassEmbedding keep μ
  let embedParent := T.wagonClassEmbedding keep ν
  have hOldNe : embedChild a ≠ embedChild b := by
    intro h
    exact hne (embedChild.injective h)
  have hOldParent :
      T.wagonParent μ ν hμν (embedChild a) =
      T.wagonParent μ ν hμν (embedChild b) := by
    calc
      T.wagonParent μ ν hμν (embedChild a) =
          embedParent ((T.restrict keep).wagonParent μ ν hμν a) :=
            (T.wagonClassEmbedding_parent keep μ ν hμν a).symm
      _ = embedParent ((T.restrict keep).wagonParent μ ν hμν b) :=
            congrArg embedParent hParent
      _ = T.wagonParent μ ν hμν (embedChild b) :=
            T.wagonClassEmbedding_parent keep μ ν hμν b
  have hOldX : x ∈
      T.wagonClassCarrier oldEdges μ (embedChild a) ∩
      T.wagonClassCarrier oldEdges μ (embedChild b) := by
    obtain ⟨ha, hb⟩ := hx
    exact ⟨
      T.wagonClassCarrier_restrict_subset
        oldEdges keep newEdges hShrink μ a ha,
      T.wagonClassCarrier_restrict_subset
        oldEdges keep newEdges hShrink μ b hb⟩
  exact hOld μ ν hμν hSucc hOldNe hOldParent hOldX

/-- If every new physical vertex in a particular edge maps into
its old carrier, any old sibling-intersection parameter pulls back
to the new vertex type. No quotient or edge-label change occurs. -/
theorem EdgeTrainLevels.adjacentParameters_vertexPullback
    {m : ℕ} (T : EdgeTrainLevels E m)
    (oldEdges : E → Set W) (newEdges : E → Set V)
    (vertexMap : V → W)
    (hMaps : ∀ e : E, ∀ x : V,
      x ∈ newEdges e → vertexMap x ∈ oldEdges e)
    (allowed : Fin (m + 1) → Set W)
    (hOld : T.AdjacentParameters oldEdges allowed) :
    T.AdjacentParameters newEdges
      (fun ν => vertexMap ⁻¹' allowed ν) := by
  have hCarrier : ∀ (μ : Fin (m + 1))
      (a : Quotient (T.wagonSetoid μ)) (x : V),
      x ∈ T.wagonClassCarrier newEdges μ a →
      vertexMap x ∈ T.wagonClassCarrier oldEdges μ a := by
    intro μ a x hx
    induction a using Quotient.inductionOn with
    | h e =>
        change x ∈ T.wagonCarrier newEdges μ e at hx
        change vertexMap x ∈ T.wagonCarrier oldEdges μ e
        obtain ⟨f, hef, hfx⟩ := hx
        exact ⟨f, hef, hMaps f x hfx⟩
  intro μ ν hμν hSucc a b hne hParent x hx
  exact hOld μ ν hμν hSucc hne hParent
    ⟨hCarrier μ a x hx.1, hCarrier μ b x hx.2⟩

end StructuralRamsey.Girth
