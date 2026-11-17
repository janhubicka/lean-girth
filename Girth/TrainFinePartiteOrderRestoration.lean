import Girth.ForestActualRecursiveSupport
import Girth.ForestRecursiveOutputGirth
import Girth.PartiteOrderCompatibility
import PartiteConstruction.Iterated.LocalTreeLike

set_option autoImplicit false
set_option Elab.async false

namespace StructuralRamsey.Girth.TrainRecursiveWitness.CoverageFree.Physical

open StructuralRamsey.RelStructure
open StructuralRamsey.Partite (System)

universe u v
variable {L : RelLanguage.{u}} {U X Y I : Type v}

section Restoration

variable (Original Source : System L.withOrder U X) (Core : System L.withOrder U Y)
variable (f : I → StructuralRamsey.Partite.Embedding Source Core)
variable (hPart : ∀ x, Original.part x = Source.part x)

local notation "RF" => (fun (i : I) => StructuralRamsey.Partite.Embedding.toEmbedding (f i))
local notation "ord" => (Sum.inr () : L.withOrder.Symbol)

/-- Fill comparisons from the original target along the designated lifts
of its supported order reduct. The hyperedge language is unchanged. -/
def restoreSelectedOrder (hPart : ∀ x, Original.part x = Source.part x) :
    System L.withOrder U Y where
  toRelStructure := {
    rel := fun r => match r with
      | .inl s => Core.rel (.inl s)
      | .inr _ => fun (z : Fin 2 → Y) => Core.rel ord z ∨ ∃ (i : I) (w : Fin 2 → X),
          Original.rel ord w ∧ (f i).toEmbedding ∘ w = z }
  part := Core.part
  transversal := by
    intro r z hz i j hij
    cases r with
    | inl s => exact Core.transversal (.inl s) z hz i j hij
    | inr s =>
        cases s
        change Core.rel ord z ∨ ∃ (k : I) (w : Fin 2 → X),
          Original.rel ord w ∧ (f k).toEmbedding ∘ w = z at hz
        rcases hz with hz | ⟨k, w, hw, rfl⟩
        · exact Core.transversal ord z hz i j hij
        · have hEq : Original.part (w i) = Original.part (w j) := by
            calc
              Original.part (w i) = Source.part (w i) := hPart _
              _ = Core.part (f k (w i)) := ((f k).map_part _).symm
              _ = Core.part (f k (w j)) := hij
              _ = Source.part (w j) := (f k).map_part _
              _ = Original.part (w j) := (hPart _).symm
          exact congrArg (f k).toEmbedding (Original.transversal ord w hw i j hEq)

variable (A : RelStructure L.withOrder U)
variable {q : ℕ}

local notation "Restored" => restoreSelectedOrder Original Source Core f hPart

/-- A comparison supported by any entire shared A-edge was already
present in the core before restoration. -/
private theorem selectedOrder_of_sharedEdge
    (hSupports : ∀ (a : Embedding A Source.toRelStructure) (w : Fin 2 → X),
      (∀ k : Fin 2, w k ∈ copyCarrier a) → Original.rel ord w → Source.rel ord w)
    (i : I) (w : Fin 2 → X)
    (hw : Original.rel ord w) (a : Embedding A Core.toRelStructure)
    (hInside : copyCarrier a ⊆ copyCarrier (f i).toEmbedding)
    (hTuple : ∀ k, (f i).toEmbedding (w k) ∈ copyCarrier a) :
    Core.rel ord ((f i).toEmbedding ∘ w) := by
  have hRange (u : U) : ∃ x : X, a u = (f i).toEmbedding x := by
    obtain ⟨x, hx⟩ := hInside (show a u ∈ copyCarrier a from ⟨u, rfl⟩)
    exact ⟨x, hx.symm⟩
  let aSource := a.factorThroughRange (f i).toEmbedding hRange
  have hTupleSource (k : Fin 2) : w k ∈ copyCarrier aSource := by
    obtain ⟨u, hu⟩ := hTuple k
    exact ⟨u, (f i).toEmbedding.injective ((Classical.choose_spec (hRange u)).symm.trans hu)⟩
  exact ((f i).toEmbedding.map_rel_iff ord w).mpr (hSupports aSource w hTupleSource hw)

/-- Pairwise mixed-forest intersections guarantee that restoring the
orders preserves and reflects the full original target on each lift. -/
def restoredSelectedEmbedding
    (hRetained : ∀ w : Fin 2 → X, Source.rel ord w → Original.rel ord w)
    (hSupported : ∀ (a : Embedding A Source.toRelStructure) (w : Fin 2 → X),
      (∀ k : Fin 2, w k ∈ copyCarrier a) → Original.rel ord w → Source.rel ord w)
    (hIrrefl : ∀ w : Fin 2 → X, Original.rel ord w → w 0 ≠ w 1)
    (hq : 2 ≤ q) (hForest : FiniteMixedForestThrough (RelationalMixedSupportTest A RF) q)
    (hUnordered : ∀ (r : L.Symbol) (w : Fin (L.arity r) → X),
      Source.rel (.inl r) w ↔ Original.rel (.inl r) w)
    (hSelected : Function.Injective (fun i => bSupportPiece A (RF i)))
    (i : I) : StructuralRamsey.Partite.Embedding Original Restored where
  toEmbedding := {
    toFun := (f i).toEmbedding
    injective := (f i).toEmbedding.injective
    map_rel_iff := by
      intro r z
      cases r with
      | inl s =>
          exact ((f i).toEmbedding.map_rel_iff (.inl s) z).trans (hUnordered s z)
      | inr s =>
          cases s
          change (Core.rel ord ((f i).toEmbedding ∘ z) ∨ ∃ (j : I) (w : Fin 2 → X),
            Original.rel ord w ∧ (f j).toEmbedding ∘ w = (f i).toEmbedding ∘ z) ↔
              Original.rel ord z
          constructor
          · rintro (hz | ⟨j, w, hw, heq⟩)
            · exact hRetained z (((f i).toEmbedding.map_rel_iff ord z).mp hz)
            · by_cases hji : j = i
              · subst j
                have hOld : w = z := funext (fun k =>
                  (f i).toEmbedding.injective (congrFun heq k))
                exact hOld ▸ hw
              · have hOverlap := FiniteMixedForestThrough.allowedIntersection_of_ne hForest hq
                  (bSupportPiece A (RF j)) (bSupportPiece A (RF i))
                  (Or.inl ⟨j, rfl⟩) (Or.inl ⟨i, rfl⟩) (fun h => hji (hSelected h))
                have hIn (k : Fin 2) : (f j).toEmbedding (w k) ∈
                    copyCarrier (f j).toEmbedding ∩ copyCarrier (f i).toEmbedding :=
                  ⟨⟨w k, rfl⟩, ⟨z k, (congrFun heq k).symm⟩⟩
                rcases hOverlap with hSingle | ⟨edge, ⟨a, ha, haSub⟩, _, hEdge⟩
                · exact (hIrrefl w hw ((f j).toEmbedding.injective
                    (hSingle (hIn 0) (hIn 1)))).elim
                · have hz := selectedOrder_of_sharedEdge Original Source Core f A
                    hSupported j w hw a haSub (by
                      intro k
                      rw [ha, ← hEdge]
                      exact hIn k)
                  exact hRetained z (((f i).toEmbedding.map_rel_iff ord z).mp
                    (Eq.mp (congrArg (Core.rel ord) heq) hz))
          · intro hz
            exact Or.inr ⟨i, z, hz, rfl⟩ }
  map_part := fun x => ((f i).map_part x).trans (hPart x).symm

/-- Every original core A-edge retains the same induced order when the
selected target orders are restored. -/
theorem restoredOrder_on_coreEdge
    (hSupported : ∀ (a : Embedding A Source.toRelStructure) (w : Fin 2 → X),
      (∀ k : Fin 2, w k ∈ copyCarrier a) → Original.rel ord w → Source.rel ord w)
    (hIrrefl : ∀ w : Fin 2 → X, Original.rel ord w → w 0 ≠ w 1)
    (hq : 2 ≤ q) (hForest : FiniteMixedForestThrough (RelationalMixedSupportTest A RF) q)
    (a : Embedding A Core.toRelStructure)
    (z : Fin 2 → Y) (hz : ∀ k : Fin 2, z k ∈ copyCarrier a) :
    (Restored).rel ord z ↔ Core.rel ord z := by
  constructor
  · change (Core.rel ord z ∨ ∃ (i : I) (w : Fin 2 → X),
      Original.rel ord w ∧ (f i).toEmbedding ∘ w = z) → Core.rel ord z
    rintro (hCore | ⟨i, w, hw, rfl⟩)
    · exact hCore
    · have hStrong := aStrong_of_finiteMixedForestThrough A (f i).toEmbedding
        (RelationalMixedSupportTest A RF) q hq hForest (Or.inl ⟨i, rfl⟩)
        (fun edge => Or.inr ⟨edge, rfl⟩)
      have hInside := hStrong a (by
        intro hs
        exact hIrrefl w hw ((f i).toEmbedding.injective
          (hs ⟨hz 0, w 0, rfl⟩ ⟨hz 1, w 1, rfl⟩)))
      exact selectedOrder_of_sharedEdge Original Source Core f A hSupported i w hw a hInside hz
  · exact Or.inl

/-- An unchanged spanning hyperedge relation pins every possible new
edge to an existing core edge. Its full induced order survives there. -/
theorem supportCopies_restoreSelectedOrder
    (hSupported : ∀ (a : Embedding A Source.toRelStructure) (w : Fin 2 → X),
      (∀ k : Fin 2, w k ∈ copyCarrier a) → Original.rel ord w → Source.rel ord w)
    (hIrrefl : ∀ w : Fin 2 → X, Original.rel ord w → w 0 ≠ w 1)
    (hq : 2 ≤ q) (hForest : FiniteMixedForestThrough (RelationalMixedSupportTest A RF) q)
    (r : L.Symbol) (w : Fin (L.arity r) → U)
    (hw : A.rel (.inl r) w) (hSpan : Function.Surjective w)
    (hCoreSupport : ∀ z : Fin (L.arity r) → Y, Core.rel (.inl r) z →
      ∃ a : Embedding A Core.toRelStructure, ∀ k, z k ∈ copyCarrier a) :
    supportCopies A (Restored).toRelStructure = supportCopies A Core.toRelStructure := by
  apply Set.Subset.antisymm
  · rintro _ ⟨a, rfl⟩
    obtain ⟨c, hc⟩ := hCoreSupport (a ∘ w) ((a.map_rel_iff (.inl r) w).mpr hw)
    have hInside (x : U) : a x ∈ copyCarrier c := by
      obtain ⟨j, rfl⟩ := hSpan x
      exact hc j
    let aCore : Embedding A Core.toRelStructure := {
      toFun := a
      injective := a.injective
      map_rel_iff := by
        intro s z
        cases s with
        | inl s => exact a.map_rel_iff (.inl s) z
        | inr s =>
            cases s
            exact (restoredOrder_on_coreEdge Original Source Core f hPart A hSupported
              hIrrefl hq hForest c (a ∘ z) (fun k => hInside (z k))).symm.trans
                (a.map_rel_iff ord z) }
    exact ⟨aCore, rfl⟩
  · rintro _ ⟨a, rfl⟩
    let aRestored : Embedding A (Restored).toRelStructure := {
      toFun := a
      injective := a.injective
      map_rel_iff := by
        intro s z
        cases s with
        | inl s => exact a.map_rel_iff (.inl s) z
        | inr s =>
            cases s
            exact (restoredOrder_on_coreEdge Original Source Core f hPart A hSupported
              hIrrefl hq hForest a (a ∘ z) (fun k => ⟨z k, rfl⟩)).trans
                (a.map_rel_iff ord z) }
    exact ⟨aRestored, rfl⟩

/-- The restored comparisons are forward in the fine-part order whenever
the old target and the supported witness both satisfy that invariant. -/
theorem restoreSelectedOrder_forwardCompatible [LT U]
    (hOriginal : PartiteOrderCompatible Original) (hCore : PartiteOrderCompatible Core) :
    PartiteOrderCompatible Restored := by
  intro z hz
  change Core.rel ord z ∨ ∃ (i : I) (w : Fin 2 → X),
    Original.rel ord w ∧ (f i).toEmbedding ∘ w = z at hz
  rcases hz with hz | ⟨i, w, hw, rfl⟩
  · exact hCore z hz
  · change Core.part (f i (w 0)) < Core.part (f i (w 1))
    rw [(f i).map_part, (f i).map_part, ← hPart, ← hPart]
    exact hOriginal w hw

end Restoration

end StructuralRamsey.Girth.TrainRecursiveWitness.CoverageFree.Physical
