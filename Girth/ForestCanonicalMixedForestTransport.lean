import Girth.ForestMixedLocalForestBridge
import Girth.ForestCanonicalTransport
import Girth.ForestImage

/-!
# Canonically transported old mixed q-forests in every standard picture

The full direct forest increment assumes a finite mixed q-forest
property at EACH full-standard owner. In the actual partite
construction those tested pieces are not arbitrary: they are
precisely the images of old tested A/B support pieces under the
standard-picture embedding.

A finite SET of distinct canonical images has a finite SET of
chosen preimages. Those chosen preimages are injectively indexed:
equal preimages give equal images, hence equal physical pieces.
Apply the OLD finite mixed forest bound, transfer the resulting
labelled forest through the injective standard embedding, and
identify the transported members with the original image family.

This discharges the new-owner old-mixed-q hypothesis from the one
global previous-picture invariant. No arbitrary hereditary forest
assertion and no duplicate multi-edge labels are used.
-/

namespace StructuralRamsey.Girth

universe v
variable {Old W : Type v}

/-- One OLD q-forest condition automatically induces the genuine
FINITE SET-valued q-forest condition on all canonically transported
pieces inside a single full standard picture. -/
theorem FiniteMixedForestThrough.canonicalTransport
    (testedOld : HypergraphPiece Old → Prop)
    (φ : Old ↪ W)
    (m : ℕ)
    (hOld : FiniteMixedForestThrough testedOld m) :
    FiniteMixedForestThrough
      (TransportedPiece testedOld φ) m := by
  classical
  intro s hTest hBound
  let J := {T : HypergraphPiece W // T ∈ s}
  let hExists : ∀ t : J, ∃ R : HypergraphPiece Old,
      testedOld R ∧ t.1 = R.map φ :=
    fun t => hTest t.1 t.2
  let lift : J → HypergraphPiece Old :=
    fun t => Classical.choose (hExists t)
  have hLiftSpec (t : J) :
      testedOld (lift t) ∧ t.1 = (lift t).map φ :=
    Classical.choose_spec (hExists t)
  have hLiftInj : Function.Injective lift := by
    intro t u heq
    apply Subtype.ext
    calc
      t.1 = (lift t).map φ := (hLiftSpec t).2
      _ = (lift u).map φ :=
        congrArg (fun P : HypergraphPiece Old => P.map φ) heq
      _ = u.1 := (hLiftSpec u).2.symm
  have hOldLocal : LocalForestThrough lift m :=
    hOld.toLocalForestThrough
      lift hLiftInj testedOld m
      (fun t => (hLiftSpec t).1)
  have hCard : Fintype.card J ≤ m := by
    simpa [J] using hBound
  have hForest : ForestOfCopies lift := by
    let idx : J ↪ J := ⟨id, Function.injective_id⟩
    have h := hOldLocal J idx hCard
    simpa only [idx, Function.comp_id] using h
  have hMapped : ForestOfCopies
      (fun t : J => (lift t).map φ) :=
    hForest.map φ
  have hEq :
      (fun t : J => (lift t).map φ) = (fun t : J => t.1) := by
    funext t
    exact (hLiftSpec t).2.symm
  rw [hEq] at hMapped
  exact hMapped

/-- All standard pictures inherit the old mixed q-forest invariant;
the embeddings may be different at different owners. -/
theorem finiteMixedForestThrough_canonicalStandardFamily
    {Q : Type v}
    (testedOld : HypergraphPiece Old → Prop)
    (standard : Q → Old ↪ W)
    (m : ℕ)
    (hOld : FiniteMixedForestThrough testedOld m) :
    ∀ q : Q,
      FiniteMixedForestThrough
        (TransportedPiece testedOld (standard q)) m :=
  fun q => hOld.canonicalTransport testedOld (standard q) m

end StructuralRamsey.Girth
