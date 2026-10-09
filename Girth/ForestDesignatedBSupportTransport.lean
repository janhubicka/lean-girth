import Girth.SupportForestToTree
import Girth.ForestCanonicalTransport
import Mathlib.Tactic

/-!
# Exact support transport for designated B-copies

A designated B-copy is transported into the full image of an old
picture under a relational embedding. Its A-support piece must be
transported *exactly*, with both its carrier and its entire ambient
A-edge family, not just its vertex set.

Because an ambient A-copy in the new B-carrier factors through the
relational standard embedding, the support piece commutes with ANY
relational embedding. No additional strong-inducedness assumption on
the B-copy is necessary for this exact support identity.

This closes the old-preimage step for actual designated B-pieces
once their designation by transported old B-copies is established.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {UA VB Old W : Type v}

/-- Image carriers of composed relational embeddings are exactly the
image under the ambient embedding of the source copy carrier. -/
theorem copyCarrier_comp_eq_image
    {A : RelStructure L UA}
    {D : RelStructure L Old} {E : RelStructure L W}
    (std : Embedding D E) (a : Embedding A D) :
    copyCarrier (std.comp a) =
      (relationEmbeddingToFunction std) '' copyCarrier a := by
  ext z
  constructor
  · rintro ⟨u, rfl⟩
    exact ⟨a u, ⟨u, rfl⟩, rfl⟩
  · rintro ⟨x, ⟨u, rfl⟩, hx⟩
    exact ⟨u, hx⟩

/-- Equality of the actual hypergraph support-piece carrier and edges
is sufficient for equality of whole pieces. -/
private theorem supportPiece_eq_of_carrier_edges
    {F G : HypergraphPiece W}
    (hc : F.carrier = G.carrier)
    (he : F.edges = G.edges) : F = G := by
  cases F with
  | mk Fc Fe Fh =>
    cases G with
    | mk Gc Ge Gh =>
      dsimp at hc he
      cases hc
      cases he
      rfl

/-- For every ambient relational embedding, the support piece of a
transported B-copy is EXACTLY the image of the old B-support piece.
This includes all new ambient A-copy edges lying inside its carrier. -/
theorem bSupportPiece_map_exact
    (A : RelStructure L UA)
    {B : RelStructure L VB}
    {D : RelStructure L Old} {E : RelStructure L W}
    (b : Embedding B D)
    (std : Embedding D E) :
    (bSupportPiece A b).map (relationEmbeddingToFunction std) =
      bSupportPiece A (std.comp b) := by
  classical
  let φ := relationEmbeddingToFunction std
  apply supportPiece_eq_of_carrier_edges
  · change φ '' copyCarrier b = copyCarrier (std.comp b)
    exact (copyCarrier_comp_eq_image std b).symm
  · ext e
    constructor
    · rintro ⟨e₀, ⟨a, hEq, hSub⟩, rfl⟩
      refine ⟨std.comp a, ?_, ?_⟩
      · calc
          copyCarrier (std.comp a) = φ '' copyCarrier a :=
            copyCarrier_comp_eq_image std a
          _ = φ '' e₀ :=
            congrArg (fun T : Set Old => φ '' T) hEq
      · rw [copyCarrier_comp_eq_image std a,
          copyCarrier_comp_eq_image std b]
        exact Set.image_mono hSub
    · rintro ⟨aNew, hEq, hSub⟩
      have hInStd : ∀ u : UA, ∃ x : Old, aNew u = std x := by
        intro u
        have hInside : aNew u ∈ copyCarrier (std.comp b) :=
          hSub ⟨u, rfl⟩
        obtain ⟨v, hv⟩ := hInside
        exact ⟨b v, hv.symm⟩
      let aOld : Embedding A D :=
        aNew.factorThroughRange std hInStd
      have hSpec (u : UA) : aNew u = std (aOld u) :=
        Classical.choose_spec (hInStd u)
      have hCarrier :
          copyCarrier aNew = φ '' copyCarrier aOld := by
        ext z
        constructor
        · rintro ⟨u, rfl⟩
          exact ⟨aOld u, ⟨u, rfl⟩, (hSpec u).symm⟩
        · rintro ⟨x, ⟨u, rfl⟩, hx⟩
          exact ⟨u, (hSpec u).trans hx⟩
      have hOldSub : copyCarrier aOld ⊆ copyCarrier b := by
        rintro x ⟨u, rfl⟩
        have hInside : std (aOld u) ∈ copyCarrier (std.comp b) := by
          rw [← hSpec u]
          exact hSub ⟨u, rfl⟩
        obtain ⟨v, hv⟩ := hInside
        refine ⟨v, ?_⟩
        exact std.injective hv
      refine ⟨copyCarrier aOld, ⟨aOld, rfl, hOldSub⟩, ?_⟩
      exact hEq.symm.trans hCarrier

/-- An actual designated B-support piece has an exact tested old B-piece
preimage whenever it is the transport of an old tested B-copy. -/
theorem designated_bSupportPiece_transported
    (A : RelStructure L UA)
    {B : RelStructure L VB}
    {D : RelStructure L Old} {E : RelStructure L W}
    (std : Embedding D E)
    (b : Embedding B D)
    (testedOld : HypergraphPiece Old → Prop)
    (hTest : testedOld (bSupportPiece A b)) :
    TransportedPiece testedOld
      (relationEmbeddingToFunction std)
      (bSupportPiece A (std.comp b)) := by
  exact ⟨bSupportPiece A b, hTest,
    (bSupportPiece_map_exact A b std).symm⟩

end StructuralRamsey.Girth
