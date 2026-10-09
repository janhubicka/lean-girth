import Girth.ForestTrueActiveQuantified
import Girth.SupportForestToTree

/-!
# Pointwise actual A/B piece ownership and finite selections

In the circulation invariant the TESTED support pieces are exactly:
* a one-edge piece on the carrier of an ambient A-copy;
* the full A-support piece of an actually designated B-copy.

For a quantified finite selected family, there is no further
combinatorial owner assignment problem once every single tested piece
has a standard-image owner. Classical finite choice supplies one owner
per selected piece, allowing repetitions; UsedOwner then eliminates
unused and repeated standard indices before forest completion.

The genuine remaining mathematics is to establish the pointwise
A-owner and designated B-owner properties in the actual partite
attachment and to obtain the local partite Ramsey witness. This
lemma does not assume foresthood of all local witness copies.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {UA VB Old W I : Type v}

/-- Exactly the two kinds of tested support piece used by the
circulation completion invariant: an ambient A-edge or a designated
B-copy with its COMPLETE ambient A-support family. -/
def SelectedABSupportPiece
    (A : RelStructure L UA)
    {B : RelStructure L VB} {R : RelStructure L W}
    (designated : Embedding B R → Prop)
    (T : HypergraphPiece W) : Prop :=
  (∃ a : Embedding A R,
      T = HypergraphPiece.oneEdge (copyCarrier a)) ∨
  (∃ b : Embedding B R,
      designated b ∧ T = bSupportPiece A b)

/-- Owners for single actual A-copy support pieces and for single
designated B-support pieces combine to cover EVERY tested A/B-piece.
Exact HypergraphPiece transport is preserved in both cases. -/
theorem selectedABSupportPiece_has_transport
    (A : RelStructure L UA)
    {B : RelStructure L VB} {R : RelStructure L W}
    (designated : Embedding B R → Prop)
    (testedOld : HypergraphPiece Old → Prop)
    (standard : I → Old ↪ W)
    (hA :
      ∀ a : Embedding A R,
        ∃ i : I, TransportedPiece testedOld (standard i)
          (HypergraphPiece.oneEdge (copyCarrier a)))
    (hB :
      ∀ b : Embedding B R, designated b →
        ∃ i : I, TransportedPiece testedOld (standard i)
          (bSupportPiece A b)) :
    ∀ T : HypergraphPiece W,
      SelectedABSupportPiece A designated T →
      ∃ i : I, TransportedPiece testedOld (standard i) T := by
  intro T hT
  rcases hT with ⟨a, hT⟩ | ⟨b, hb, hT⟩
  · rw [hT]
    exact hA a
  · rw [hT]
    exact hB b hb

/-- Pointwise exact ownership suffices to choose a standard-copy owner
for EVERY bounded finite selected family simultaneously. No global
surjectivity or arbitrary finite index family is required.

This is precisely the family-ownership hypothesis of the quantified
circulation completion theorem, discharged by pointwise geometry. -/
theorem selectedABSupportPiece_choose_family_owners
    (A : RelStructure L UA)
    {B : RelStructure L VB} {R : RelStructure L W}
    (designated : Embedding B R → Prop)
    (testedOld : HypergraphPiece Old → Prop)
    (standard : I → Old ↪ W)
    (hEach :
      ∀ T : HypergraphPiece W,
        SelectedABSupportPiece A designated T →
        ∃ i : I, TransportedPiece testedOld (standard i) T)
    (m : ℕ) :
    ∀ (N : Type v) [Fintype N]
      (selected : N → HypergraphPiece W),
      (∀ n, SelectedABSupportPiece A designated (selected n)) →
      Fintype.card N ≤ m →
        ∃ owner : N → I,
          ∀ n : N,
            TransportedPiece testedOld
              (standard (owner n)) (selected n) := by
  classical
  intro N hFintype selected hTest _hCard
  have hOwner (n : N) :
      ∃ i : I,
        TransportedPiece testedOld (standard i) (selected n) :=
    hEach (selected n) (hTest n)
  choose owner hSpec using hOwner
  exact ⟨owner, hSpec⟩

end StructuralRamsey.Girth
