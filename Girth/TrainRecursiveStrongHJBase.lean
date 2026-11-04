import Girth.TrainRecursiveHJLineStrongness
import Girth.TrainRecursiveLargeBasePartiteInput
import Girth.TrainRecursivePartitePowerSupport
import Girth.TrainRecursivePartitePowerLinearity

set_option autoImplicit false
set_option Elab.async false

/-!
# A finite Hales--Jewett Ramsey base with the strong geometric properties

The larger-base repair of the nontrivial q>2 recursive step needs an
A-partite Ramsey base D that is A-linear, covered by ambient A-copies,
and whose prescribed B-base labels are genuinely A-strong. The
induced partite Hales--Jewett power is such a base, provided the
original A-partite target has A-linear support and every vertex
belongs to an actual A-copy.

This packages the EXACT HJ LINE family. In particular, strongness
is required of every selected-line label, not merely the eventual
monochromatic line. Ordered irreducibility discharges the rigidity
of all ambient A-copies in the power.

The power is NOT asserted to have girth higher than two; the lower
forest stage must still be built by the corresponding induction
and initial disjoint picture, with genuine train and forest bounds.
No output SupremeCycleBound is claimed.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure
universe u v w
variable {L : RelLanguage.{u}} {Q V : Type v}

/-- The canonical positive-coordinate Hales--Jewett base satisfies
all four base conditions simultaneously: A-partiteness, A-linearity,
A-support coverage, and strongness of each actual HJ line, with the
correct genuinely selected PARTITE Ramsey arrow. No family of
extra B-copies and no deduplication by equal carriers is introduced. -/
theorem exists_largeBase_HJLine_fullGeometry_ordered
    (A₀ : RelStructure L Q) [LinearOrder Q] [Finite Q]
    (B : StructuralRamsey.Partite.System L.withOrder Q V) [Finite V]
    (hB : B.IsPartiteOver A₀.ordered)
    (hLinear : ALinear A₀.ordered B.toRelStructure)
    (hSupportCovers : ∀ v : V,
      ∃ a : Embedding A₀.ordered B.toRelStructure,
        v ∈ copyCarrier a)
    (κ : Type w) [Fintype κ] [Nonempty κ] :
    ∃ (N : ℕ), 0 < N ∧
      let D := StructuralRamsey.Partite.Induced.power B N
      D.IsPartiteOver A₀.ordered ∧
      ALinear A₀.ordered D.toRelStructure ∧
      (∀ x : StructuralRamsey.Partite.NonInduced.Vertex B N,
        ∃ a : Embedding A₀.ordered D.toRelStructure,
          x ∈ copyCarrier a) ∧
      ∃ family : Set (Embedding B.toRelStructure D.toRelStructure),
        Nonempty family ∧
        (∀ b, b ∈ family → ∀ x : V,
          D.part (b x) = B.part x) ∧
        (∀ b, b ∈ family →
          AStrong A₀.ordered D.toRelStructure (copyCarrier b)) ∧
        (∀ χ : StructuralRamsey.Partite.Embedding
          (StructuralRamsey.Partite.transversal A₀.ordered) D → κ,
          ∃ W : HalesJewett.Line
            (StructuralRamsey.Partite.Induced.Letter A₀.ordered B) N,
            (StructuralRamsey.Partite.Induced.lineEmbedding hB W).toEmbedding ∈
              family ∧
            ∀ a₁ a₂ : StructuralRamsey.Partite.Embedding
              (StructuralRamsey.Partite.transversal A₀.ordered) B,
              χ ((StructuralRamsey.Partite.Induced.lineEmbedding hB W).comp a₁) =
                χ ((StructuralRamsey.Partite.Induced.lineEmbedding hB W).comp a₂)) := by
  classical
  letI : Fintype (StructuralRamsey.Partite.Induced.Letter A₀.ordered B) :=
    Fintype.ofFinite _
  obtain ⟨N, hN, hHJ⟩ :=
    HalesJewett.finite
      (α := StructuralRamsey.Partite.Induced.Letter A₀.ordered B) (κ := κ)
  let D := StructuralRamsey.Partite.Induced.power B N
  have hD : D.IsPartiteOver A₀.ordered :=
    StructuralRamsey.Partite.Induced.power_isPartiteOver hB hN
  have hA : A₀.ordered.Irreducible :=
    (RelStructure.ordered_hereditarilyIrreducible A₀).irreducible
  have hPowerParts :
      ∀ e : Embedding A₀.ordered D.toRelStructure, ∀ p : Q,
        D.part (e p) = p := by
    intro e p
    exact relationalA_embedding_preserves_parts_of_rigid
      A₀.ordered D hA hD
      (fun a => orderedA_self_embedding_is_id A₀ a) e p
  have hLinearity : ALinear A₀.ordered D.toRelStructure :=
    aLinear_inducedPower_of_Aparts
      A₀.ordered B hB N hLinear hPowerParts
  have hCoverPower : ∀ x : StructuralRamsey.Partite.NonInduced.Vertex B N,
      ∃ a : Embedding A₀.ordered D.toRelStructure,
        x ∈ copyCarrier a :=
    inducedPower_supportCovers_of_partiteACopies A₀.ordered B N hN
      hSupportCovers
      (fun a p => relationalA_embedding_preserves_parts_of_rigid
        A₀.ordered B hA hB
        (fun b => orderedA_self_embedding_is_id A₀ b) a p)
  let family : Set (Embedding B.toRelStructure D.toRelStructure) :=
    Set.range
      (fun W : HalesJewett.Line
        (StructuralRamsey.Partite.Induced.Letter A₀.ordered B) N =>
        (StructuralRamsey.Partite.Induced.lineEmbedding hB W).toEmbedding)
  refine ⟨N, hN, hD, hLinearity, hCoverPower, family, ?_, ?_, ?_, ?_⟩
  · let colour : κ := Classical.choice (inferInstance : Nonempty κ)
    obtain ⟨W, _hW⟩ := hHJ (fun _ => colour)
    exact ⟨(StructuralRamsey.Partite.Induced.lineEmbedding hB W).toEmbedding,
      ⟨W, rfl⟩⟩
  · intro b hb x
    obtain ⟨W, rfl⟩ := hb
    exact (StructuralRamsey.Partite.Induced.lineEmbedding hB W).map_part x
  · intro b hb
    obtain ⟨W, rfl⟩ := hb
    exact inducedHJLine_aStrong_ordered A₀ B hB hLinear N hN W
  · intro χ
    obtain ⟨W, hMono⟩ := hHJ
      (fun word => χ
        (StructuralRamsey.Partite.Induced.wordEmbedding hB hN word))
    refine ⟨W, ⟨W, rfl⟩, ?_⟩
    intro a₁ a₂
    simpa only [StructuralRamsey.Partite.Induced.lineEmbedding_comp_letter
      hB hN] using hMono a₁ a₂

end StructuralRamsey.Girth
