import Girth.SupportForestToTree
import Girth.ForestCanonicalTransport

/-!
# Exact transport of the A-support of an embedded designated B-copy

The circulation proof transports designated B-copies into full standard
pictures. The resulting B-support hypergraph must be the literal image
of the OLD B-support piece, including its complete set of A-edges.

This is stronger than equality of copy carriers or inclusion of some
designated edges. It uses inducedness of relational embeddings:
an ambient A-embedding whose range lies in a transported B-copy
factors through the standard embedding and becomes an old A-copy.
Thus no new internal A-support edges appear in a transported B-copy.

This is the exact bridge needed to interpret the explicitly transported
designated-support predicate as actual B-copy supports in certpres.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {UA VB Old W : Type v}

private theorem support_piece_ext
    {F G : HypergraphPiece W}
    (hCarrier : F.carrier = G.carrier)
    (hEdges : F.edges = G.edges) : F = G := by
  cases F with
  | mk FC FE Fh =>
    cases G with
    | mk GC GE Gh =>
      dsimp at hCarrier hEdges
      cases hCarrier
      cases hEdges
      rfl

/-- Exact carrier-image identity for compositions of relational
embeddings. No finiteness assumption on the source is needed. -/
theorem copyCarrier_relational_comp_image
    {A : RelStructure L UA}
    {B : RelStructure L Old}
    {C : RelStructure L W}
    (a : RelStructure.Embedding A B)
    (std : RelStructure.Embedding B C) :
    copyCarrier (std.comp a) =
      (relationEmbeddingToFunction std) '' copyCarrier a := by
  ext z
  constructor
  · rintro ⟨u, rfl⟩
    exact ⟨a u, ⟨u, rfl⟩, rfl⟩
  · rintro ⟨x, ⟨u, rfl⟩, rfl⟩
    exact ⟨u, rfl⟩

/-- Transport of a B-copy preserves its FULL A-support hypergraph,
including edges supplied by ambient A-embeddings lying inside B.

The reverse edge containment factors every such ambient A-copy through
the induced old standard-picture embedding. -/
theorem bSupportPiece_map_relational_standard
    (A : RelStructure L UA)
    {B : RelStructure L VB}
    {OldStruct : RelStructure L Old}
    {Whole : RelStructure L W}
    (b : RelStructure.Embedding B OldStruct)
    (std : RelStructure.Embedding OldStruct Whole) :
    (bSupportPiece A b).map (relationEmbeddingToFunction std) =
      bSupportPiece A (std.comp b) := by
  classical
  let φ : Old ↪ W := relationEmbeddingToFunction std
  have hCarrier :
      ((bSupportPiece A b).map φ).carrier =
        (bSupportPiece A (std.comp b)).carrier := by
    change φ '' copyCarrier b = copyCarrier (std.comp b)
    exact (copyCarrier_relational_comp_image b std).symm
  have hEdges :
      ((bSupportPiece A b).map φ).edges =
        (bSupportPiece A (std.comp b)).edges := by
    ext e
    constructor
    · rintro ⟨e₀, ⟨aOld, haEq, hSub⟩, rfl⟩
      refine ⟨std.comp aOld, ?_, ?_⟩
      · calc
          copyCarrier (std.comp aOld) = φ '' copyCarrier aOld :=
            copyCarrier_relational_comp_image aOld std
          _ = φ '' e₀ := congrArg (fun s : Set Old => φ '' s) haEq
      · rw [copyCarrier_relational_comp_image aOld std,
          copyCarrier_relational_comp_image b std]
        exact Set.image_mono hSub
    · rintro ⟨aWhole, haEq, hSub⟩
      have hFactor :
          ∀ u : UA, ∃ x : Old, aWhole u = std x := by
        intro u
        obtain ⟨v, hv⟩ := hSub ⟨u, rfl⟩
        exact ⟨b v, hv⟩
      let aOld : RelStructure.Embedding A OldStruct :=
        aWhole.factorThroughRange std hFactor
      have hSpec (u : UA) : aWhole u = std (aOld u) :=
        Classical.choose_spec (hFactor u)
      have hOldSub : copyCarrier aOld ⊆ copyCarrier b := by
        rintro x ⟨u, rfl⟩
        obtain ⟨v, hv⟩ := hSub ⟨u, rfl⟩
        refine ⟨v, std.injective ?_⟩
        exact (hSpec u).symm.trans hv
      have hComp : std.comp aOld = aWhole := by
        apply RelStructure.Embedding.ext
        intro u
        exact (hSpec u).symm
      have hImage : e = φ '' copyCarrier aOld := by
        calc
          e = copyCarrier aWhole := haEq.symm
          _ = copyCarrier (std.comp aOld) := congrArg copyCarrier hComp.symm
          _ = φ '' copyCarrier aOld :=
            copyCarrier_relational_comp_image aOld std
      exact ⟨copyCarrier aOld, ⟨aOld, rfl, hOldSub⟩, hImage⟩
  exact support_piece_ext hCarrier hEdges

end StructuralRamsey.Girth
