import Girth.PartiteOrderCompatibility
import Girth.Support
import PartiteConstruction.Iterated.LocalTreeLike
import Mathlib.Tactic

set_option autoImplicit false
set_option Elab.async false

namespace StructuralRamsey.Girth.TrainRecursiveWitness.CoverageFree.Physical

open StructuralRamsey.RelStructure
open StructuralRamsey.Partite (System)

universe u v
variable {L : RelLanguage.{u}} {U X Y : Type v}

/-- Present a fine-coloured hypergraph relationally, with forward
comparisons on physical A-carriers. The ambient orders within parts
remain separate. -/
def supportedCrossPartOrder (A₀ : RelStructure L U) [LinearOrder U]
    (H : System L U X) : System L.withOrder U X where
  toRelStructure := {
    rel := fun r => match r with
      | .inl s => H.rel s
      | .inr _ => fun (z : Fin 2 → X) => H.part (z 0) < H.part (z 1) ∧
          ∃ a : Embedding A₀ H.toRelStructure, ∀ k, z k ∈ copyCarrier a }
  part := H.part
  transversal := by
    intro r z hz i j hij
    cases r with
    | inl s => exact H.transversal s z hz i j hij
    | inr s =>
        cases s
        have hForward : H.part (z (0 : Fin 2)) < H.part (z (1 : Fin 2)) := hz.1
        fin_cases i <;> fin_cases j
        · rfl
        · exact ((ne_of_lt hForward) hij).elim
        · exact ((ne_of_lt hForward) hij.symm).elim
        · rfl

/-- An unordered physical edge lifts to the supported-order presentation
on its prescribed fine coordinates. -/
def supportedCrossPartOrder_edge (A₀ : RelStructure L U) [LinearOrder U]
    (H : System L U X) (a : Embedding A₀ H.toRelStructure)
    (hFine : ∀ u, H.part (a u) = u) :
    Embedding A₀.ordered (supportedCrossPartOrder A₀ H).toRelStructure where
  toFun := a
  injective := a.injective
  map_rel_iff := by
    intro r z
    cases r with
    | inl s => exact a.map_rel_iff s z
    | inr s =>
        cases s
        change (H.part (a (z (0 : Fin 2))) < H.part (a (z (1 : Fin 2))) ∧
          ∃ b : Embedding A₀ H.toRelStructure, ∀ k, a (z k) ∈ copyCarrier b) ↔
            z (0 : Fin 2) < z (1 : Fin 2)
        simp only [hFine]
        exact ⟨And.left, fun h => ⟨h, a, fun k => ⟨z k, rfl⟩⟩⟩

/-- Each carrier is retained in the supported-order presentation. -/
theorem supportCopies_supportedCrossPartOrder (A₀ : RelStructure L U) [LinearOrder U]
    (H : System L U X)
    (hFine : ∀ (a : Embedding A₀ H.toRelStructure) u, H.part (a u) = u) :
    supportCopies A₀.ordered (supportedCrossPartOrder A₀ H).toRelStructure =
      supportCopies A₀ H.toRelStructure := by
  apply Set.Subset.antisymm
  · rintro _ ⟨a, rfl⟩
    let reduct : Embedding A₀ H.toRelStructure := {
      toFun := a
      injective := a.injective
      map_rel_iff := fun s z => a.map_rel_iff (.inl s) z }
    exact ⟨reduct, rfl⟩
  · rintro _ ⟨a, rfl⟩
    exact ⟨supportedCrossPartOrder_edge A₀ H a (hFine a), rfl⟩

/-- A strongly induced hypergraph lift preserves and reflects the
supported cross-part order on its image. -/
noncomputable def supportedCrossPartOrder_lift (A₀ : RelStructure L U) [LinearOrder U]
    (H : System L U X) (K : System L U Y) (f : StructuralRamsey.Partite.Embedding H K)
    (hStrong : AStrong A₀ K.toRelStructure (copyCarrier f.toEmbedding)) :
    StructuralRamsey.Partite.Embedding (supportedCrossPartOrder A₀ H)
      (supportedCrossPartOrder A₀ K) where
  toEmbedding := {
    toFun := f.toEmbedding
    injective := f.toEmbedding.injective
    map_rel_iff := by
      intro r z
      cases r with
      | inl s => exact f.toEmbedding.map_rel_iff s z
      | inr s =>
          cases s
          let w : Fin 2 → X := z
          change (K.part (f.toEmbedding (w 0)) < K.part (f.toEmbedding (w 1)) ∧
            ∃ a : Embedding A₀ K.toRelStructure, ∀ k,
              f.toEmbedding (w k) ∈ copyCarrier a) ↔
            (H.part (w 0) < H.part (w 1) ∧
              ∃ a : Embedding A₀ H.toRelStructure, ∀ k, w k ∈ copyCarrier a)
          simp only [f.map_part]
          constructor
          · rintro ⟨hForward, a, ha⟩
            have hNe : w 0 ≠ w 1 := fun h => ne_of_lt hForward (congrArg H.part h)
            have hInside := hStrong a (by
              intro hSmall
              exact hNe (f.toEmbedding.injective
                (hSmall ⟨ha (0 : Fin 2), w 0, rfl⟩ ⟨ha (1 : Fin 2), w 1, rfl⟩)))
            have hRange (u : U) : ∃ x : X, a u = f.toEmbedding x := by
              obtain ⟨x, hx⟩ := hInside (show a u ∈ copyCarrier a from ⟨u, rfl⟩)
              exact ⟨x, hx.symm⟩
            let b := a.factorThroughRange f.toEmbedding hRange
            refine ⟨hForward, b, fun k => ?_⟩
            obtain ⟨u, hu⟩ := ha k
            exact ⟨u, f.toEmbedding.injective
              ((Classical.choose_spec (hRange u)).symm.trans hu)⟩
          · rintro ⟨hForward, a, ha⟩
            refine ⟨hForward, f.toEmbedding.comp a, fun k => ?_⟩
            obtain ⟨u, hu⟩ := ha k
            exact ⟨u, congrArg f.toEmbedding hu⟩ }
  map_part := f.map_part

theorem supportedCrossPartOrder_forwardCompatible (A₀ : RelStructure L U) [LinearOrder U]
    (H : System L U X) : PartiteOrderCompatible (supportedCrossPartOrder A₀ H) :=
  fun _ hz => hz.1

/-- The supported order equals the original order on a genuine physical
edge if the latter realises the prescribed fine coordinates. The original
order may also compare vertices from distinct edges. -/
theorem originalOrder_bounds_of_supportedCrossPartOrder
    (A₀ : RelStructure L U) [LinearOrder U] (H : System L U X)
    (Original : System L.withOrder U X) (hPart : ∀ x, Original.part x = H.part x)
    (hFine : ∀ (a : Embedding A₀ H.toRelStructure) u, H.part (a u) = u)
    (hReal : ∀ a : Embedding A₀ H.toRelStructure,
      ∃ b : Embedding A₀.ordered Original.toRelStructure, ∀ u, b u = a u)
    (hForward : PartiteOrderCompatible Original) :
    let Source := supportedCrossPartOrder A₀ H
    (∀ w : Fin 2 → X, Source.rel (.inr ()) w → Original.rel (.inr ()) w) ∧
    (∀ (a : Embedding A₀.ordered Source.toRelStructure) (w : Fin 2 → X),
      (∀ k, w k ∈ copyCarrier a) → Original.rel (.inr ()) w → Source.rel (.inr ()) w) ∧
    (∀ w : Fin 2 → X, Original.rel (.inr ()) w → w 0 ≠ w 1) := by
  let Source := supportedCrossPartOrder A₀ H
  refine ⟨?_, ?_, ?_⟩
  · intro w hw
    change H.part (w 0) < H.part (w 1) ∧
      ∃ a : Embedding A₀ H.toRelStructure, ∀ k, w k ∈ copyCarrier a at hw
    obtain ⟨hOrder, a, ha⟩ := hw
    obtain ⟨b, hb⟩ := hReal a
    have hExist (k : Fin 2) : ∃ u : U, a u = w k := ha k
    choose z hz using hExist
    have hAOrder : z 0 < z 1 := by
      simpa only [← hz 0, ← hz 1, hFine] using hOrder
    have hBOrder := (b.map_rel_iff (.inr ()) z).mpr hAOrder
    have hMap : b ∘ z = w := funext (fun i => (hb (z i)).trans (hz i))
    exact hMap ▸ hBOrder
  · intro a w hInside hw
    let aH : Embedding A₀ H.toRelStructure := {
      toFun := a
      injective := a.injective
      map_rel_iff := fun s z => a.map_rel_iff (.inl s) z }
    have hLt : H.part (w 0) < H.part (w 1) := by
      simpa only [hPart] using hForward w hw
    exact ⟨hLt, aH, hInside⟩
  · intro w hw hEq
    exact ne_of_lt (hForward w hw) (congrArg Original.part hEq)

end StructuralRamsey.Girth.TrainRecursiveWitness.CoverageFree.Physical
