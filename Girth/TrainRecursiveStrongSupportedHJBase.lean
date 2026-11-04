import Girth.TrainRecursiveHJLineStrongness
import Girth.TrainRecursiveLargeBasePartiteInput
import Girth.TrainRecursivePartitePowerSupport

set_option autoImplicit false
set_option Elab.async false

/-!
# Joint large-base geometry for the actual ordered Track D recursion

For the true ordered active A-source, we need a single finite *large*
A-partite Ramsey base with all of the geometric properties actually used
by the recursive forest-tail argument. Merely saying that there exists
some part-preserving family of target copies does not imply its members
are A-strong. Here the designated family is exactly the range of the
genuine Hales--Jewett line embeddings.

The inputs are A-linearity and full physical A-support coverage of the
active source. The conclusions keep all vertices, physical A-support,
actual designated labels, part-preservation, A-linearity of the large
base, A-strongness of every designated line, and the literal partite
Ramsey arrow. This is only the LARGE-BASE package: it does not construct
the lower ForestTailStage or its train/girth certificates and does not
transfer attached-output SupremeCycleBound. Circulation only.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v w
variable {L : RelLanguage.{u}} {Q V : Type v}

/-- A common Hales--Jewett base for the full physical A-support,
actual strong designated B-copies, and the partite Ramsey arrow.

The ordered source discharges all A-part-preservation assumptions.
The base need not itself be of high ordinary girth; its A-linearity
and the A-strongness of its chosen line family suffice for this
particular input interface. -/
theorem exists_largeBase_strongSupportedHJLineRamseyFamily
    (A₀ : RelStructure L Q) [LinearOrder Q] [Finite Q]
    (B : StructuralRamsey.Partite.System L.withOrder Q V) [Finite V]
    (hB : B.IsPartiteOver A₀.ordered)
    (hLinear : ALinear A₀.ordered B.toRelStructure)
    (hCover : ∀ x : V, ∃ a : Embedding A₀.ordered B.toRelStructure,
      x ∈ copyCarrier a)
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
        (∀ b, b ∈ family → ∀ x : V, D.part (b x) = B.part x) ∧
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
  letI : Fintype
      (StructuralRamsey.Partite.Induced.Letter A₀.ordered B) :=
    Fintype.ofFinite _
  obtain ⟨N, hN, hHJ⟩ :=
    HalesJewett.finite
      (α := StructuralRamsey.Partite.Induced.Letter A₀.ordered B)
      (κ := κ)
  refine ⟨N, hN, ?_⟩
  let D := StructuralRamsey.Partite.Induced.power B N
  have hD : D.IsPartiteOver A₀.ordered :=
    StructuralRamsey.Partite.Induced.power_isPartiteOver hB hN
  have hIrr : A₀.ordered.Irreducible :=
    (RelStructure.ordered_hereditarilyIrreducible A₀).irreducible
  have hRigid : ∀ a : Embedding A₀.ordered A₀.ordered,
      a = Embedding.id A₀.ordered :=
    fun a => orderedA_self_embedding_is_id A₀ a
  have hSourceParts :
      ∀ a : Embedding A₀.ordered B.toRelStructure,
        ∀ p : Q, B.part (a p) = p :=
    fun a p =>
      relationalA_embedding_preserves_parts_of_rigid
        A₀.ordered B hIrr hB hRigid a p
  have hPowerParts :
      ∀ a : Embedding A₀.ordered D.toRelStructure,
        ∀ p : Q, D.part (a p) = p :=
    fun a p =>
      relationalA_embedding_preserves_parts_of_rigid
        A₀.ordered D hIrr hD hRigid a p
  have hLinearD : ALinear A₀.ordered D.toRelStructure :=
    aLinear_inducedPower_of_Aparts
      A₀.ordered B hB N hLinear hPowerParts
  have hCoverD :
      ∀ x : StructuralRamsey.Partite.NonInduced.Vertex B N,
        ∃ a : Embedding A₀.ordered D.toRelStructure,
          x ∈ copyCarrier a :=
    inducedPower_supportCovers_of_partiteACopies
      A₀.ordered B N hN hCover hSourceParts
  let family : Set (Embedding B.toRelStructure D.toRelStructure) :=
    Set.range (fun W : HalesJewett.Line
      (StructuralRamsey.Partite.Induced.Letter A₀.ordered B) N =>
      (StructuralRamsey.Partite.Induced.lineEmbedding hB W).toEmbedding)
  refine ⟨hD, hLinearD, hCoverD, family, ?_, ?_, ?_, ?_⟩
  · let colour : κ := Classical.choice (inferInstance : Nonempty κ)
    obtain ⟨W, _⟩ := hHJ (fun _ => colour)
    exact ⟨_, ⟨W, rfl⟩⟩
  · rintro b ⟨W, rfl⟩ x
    exact (StructuralRamsey.Partite.Induced.lineEmbedding hB W).map_part x
  · rintro b ⟨W, rfl⟩
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
