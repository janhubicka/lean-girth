import Girth.TrainFillingPrivateOriginalTrainInH

set_option Elab.async false

/-!
# Simultaneous selected train cuts for one physical target

The existing original-edge wagon theorem is valid at a single proper
cut. Its parentwise realization and quotient wagon type are indexed by
that cut. Applying it independently does not, without a coherence
condition, yield one selected physical copy of T across all levels.

Here we fix ONE physical edge map before quantifying over cuts.
Cutwise parentwise realizations are allowed to vary, but their actual
selected original edge maps must agree with that fixed map. The result
then proves preservation AND reflection at every proper cut on this
same physical target.

This is a conditional interface theorem, not the construction of the
canonical filled H nor the full cutoff-two Ramsey assertion. The
application must derive agreement from the canonical filling. The
bottom edge-equality and global top are intentionally separate.
-/

namespace StructuralRamsey.Girth.IndexedPrivateChoice

universe v
variable {C V P X GV GE I GQ : Type v}
variable (S : C → SummandPrivateTemplate V P X)

private abbrev U : C → PrivateWagonInput V P X :=
  fun c => (S c).toPrivateWagonInput

/-- A fixed original-target physical edge map and cutwise compatible
realizations of exactly that same map. The ambient edge carrier type
and selected pair (i,c) do not change with the cut. -/
theorem selectedOriginalEdge_allProperCuts_iff
    {m : ℕ} (T : EdgeTrainLevels P m)
    (D : Fin (m + 1) → OrderOneData GV GE I GQ)
    (R : (ν : Fin (m + 1)) →
      ParentwiseRealization (U S)
        (fun p : P => Quotient.mk (T.wagonSetoid ν) p) (D ν))
    (i : I) (c : C)
    (image : (S c).OriginalEdge → GE)
    (hImage : ∀ (ν : Fin (m + 1)) (e : (S c).OriginalEdge),
      (R ν).edge i (selectedTaggedOriginalEdge S c e) = image e) :
    ∀ (ν : Fin (m + 1)), ν.val < m →
      ∀ e f : (S c).OriginalEdge,
        T.rel ν e.1 f.1 ↔
          (D ν).parent (image e) = (D ν).parent (image f) := by
  intro ν hProper e f
  simpa only [hImage ν e, hImage ν f] using
    (ParentwiseRealization.selectedOriginalEdge_wagon_iff
      S T ν hProper (D ν) (R ν) i c e f)

/-- Equality on original physical edges is preserved and reflected
by a single selected edge map whenever it comes from one of the
injective parentwise realizations. This is the bottom-equality case
needed alongside the proper cuts above. -/
theorem selectedOriginalEdge_fixedMap_injective
    {m : ℕ} (T : EdgeTrainLevels P m)
    (D : Fin (m + 1) → OrderOneData GV GE I GQ)
    (R : (ν : Fin (m + 1)) →
      ParentwiseRealization (U S)
        (fun p : P => Quotient.mk (T.wagonSetoid ν) p) (D ν))
    (i : I) (c : C)
    (image : (S c).OriginalEdge → GE)
    (hImage : ∀ (ν : Fin (m + 1)) (e : (S c).OriginalEdge),
      (R ν).edge i (selectedTaggedOriginalEdge S c e) = image e)
    (ν : Fin (m + 1)) :
    Function.Injective image := by
  intro e f hef
  apply (R ν).originalTaggedEdge_injective S i c
  calc
    (R ν).edge i (selectedTaggedOriginalEdge S c e) = image e :=
      hImage ν e
    _ = image f := hef
    _ = (R ν).edge i (selectedTaggedOriginalEdge S c f) :=
      (hImage ν f).symm

end StructuralRamsey.Girth.IndexedPrivateChoice
