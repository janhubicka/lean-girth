import Girth.ActualActivePartitePresentation
import Girth.PartiteOrderCompatibility
import PartiteConstruction.Partite.Operations
import Mathlib.Tactic

set_option autoImplicit false
set_option Elab.async false

namespace StructuralRamsey.Girth.TrainRecursiveWitness.CoverageFree.Physical

open StructuralRamsey.RelStructure
open StructuralRamsey.Partite (System)

universe u v
variable {L : RelLanguage.{u}} {U P X Y I : Type v}

local notation "ord" => (Sum.inr () : L.withOrder.Symbol)

/-- Comparisons in the picture project to comparisons in the fixed base. -/
def ProjectsOrder (D : RelStructure L.withOrder P) (C : System L.withOrder P X) : Prop :=
  ∀ z : Fin 2 → X, C.rel ord z → D.rel ord (C.part ∘ z)

theorem projectsOrder_of_isPartiteOver (D : RelStructure L.withOrder P)
    (C : System L.withOrder P X) (h : C.IsPartiteOver D) : ProjectsOrder D C :=
  fun _ hz => h.map_rel hz

/-- A comparison in the true active subsystem goes forward in the fine
parts because the processed base A-copy reflects comparisons. -/
theorem projectsOrder_activeFine (A₀ : RelStructure L U) [LinearOrder U]
    (D : RelStructure L.withOrder P) (C : System L.withOrder P X)
    (e : Embedding A₀.ordered D) (h : ProjectsOrder D C) :
    PartiteOrderCompatible (actualActiveSubsystemPartite A₀.ordered C e.toFunctionEmbedding) := by
  let α := e.toFunctionEmbedding
  let S := activeCarrier A₀.ordered C α
  let part := activeSourcePart A₀.ordered C α
  intro z hz
  change C.rel ord (Subtype.val ∘ z) at hz
  change part (z 0) < part (z 1)
  apply (e.map_rel_iff ord (part ∘ z)).mp
  have hTuple : C.part ∘ ((Subtype.val : S → X) ∘ z) = e ∘ (part ∘ z) := by
    funext i
    exact (activeSourcePart_spec A₀.ordered C α (z i)).symm
  exact Eq.mp (congrArg (D.rel ord) hTuple) (h _ hz)

/-- Relabelling a forward fine core projects its comparisons into the
base via the actual ordered A-copy. -/
theorem projectsOrder_relabelFine (A₀ : RelStructure L U) [LinearOrder U]
    (D : RelStructure L.withOrder P) (H : System L.withOrder U Y)
    (e : Embedding A₀.ordered D) (h : PartiteOrderCompatible H) :
    ProjectsOrder D (H.relabel e.toFunctionEmbedding) := by
  intro z hz
  change D.rel ord (e ∘ (H.part ∘ z))
  exact (e.map_rel_iff ord (H.part ∘ z)).mpr (h z hz)

/-- The existing attachment order lemma applies to the base relation
itself, without choosing an auxiliary total order on the base. -/
theorem projectsOrder_attachment (D : RelStructure L.withOrder P)
    (C : System L.withOrder P X) (S : Set X) (H : System L.withOrder P Y)
    (f : I → StructuralRamsey.Partite.Embedding (C.induce S) H)
    (hC : ProjectsOrder D C) (hH : ProjectsOrder D H) :
    ProjectsOrder D (StructuralRamsey.Partite.Attachment.attach C S H f) := by
  letI : LT P := ⟨fun x y => D.rel ord ![x, y]⟩
  have hTwo (z : Fin 2 → P) : ![z 0, z 1] = z := by
    funext i
    fin_cases i <;> rfl
  have hConvert (V : Type v) (E : System L.withOrder P V) :
      ProjectsOrder D E ↔ PartiteOrderCompatible E := by
    constructor <;> intro h z hz
    · change D.rel ord ![E.part (z 0), E.part (z 1)]
      exact Eq.mpr (congrArg (D.rel ord) (hTwo (E.part ∘ z))) (h z hz)
    · have hRel := h z hz
      change D.rel ord ![E.part (z 0), E.part (z 1)] at hRel
      exact Eq.mp (congrArg (D.rel ord) (hTwo (E.part ∘ z))) hRel
  exact (hConvert _ _).mpr <| partiteOrderCompatible_attachment C S H f
    ((hConvert X C).mp hC) ((hConvert Y H).mp hH)

end StructuralRamsey.Girth.TrainRecursiveWitness.CoverageFree.Physical
