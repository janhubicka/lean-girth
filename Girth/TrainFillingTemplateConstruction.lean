import Girth.TrainFillingInheritedSystemGirth
import Girth.TrainEndpointGeometry

set_option Elab.async false

/-!
# Construct a filling from copies of one local template

Section 16 says to fill each old edge f by a copy X_f of one uniform
hypergraph X. Here the filling record is CONSTRUCTED from those placements,
not supplied as an input. The complete generated edge family is the range
of the images of all template edges in all old edges.

Two vertices in every template edge, together with old edge linearity,
force a unique old cover. Injectivity of each placement then also recovers
the unique template edge. Thus no global new-edge injectivity, chosen cover,
coverage of the output, or pruning is an assumption. Pointwise template
coverage supplies the filling coverage field.

The two-vertex hypothesis is essential for this unique-cover construction:
singleton template images can coincide in two old edges meeting once. This
file does not dispose of such degenerate edge types by silently assigning
or discarding them. It also does not construct the uniform Ramsey witness X
or its ordered relational placements; it constructs the filling from them.
-/

namespace StructuralRamsey.Girth

universe v

/-- Input for canonical filling: local template data and its placements
on the old edges. No field asserts an output filling or output invariant. -/
structure UniformFillingData (V X : Type v) where
  oldEdges : Set (Set V)
  templateEdges : Set (Set X)
  place : {f : Set V // f ∈ oldEdges} → (X ↪ V)
  range_place : ∀ f, Set.range (place f) = f.1
  old_linear : ∀ f g : {f : Set V // f ∈ oldEdges},
    f ≠ g → (f.1 ∩ g.1).Subsingleton
  template_pair : ∀ a : {a : Set X // a ∈ templateEdges},
    ∃ x y, x ≠ y ∧ x ∈ a.1 ∧ y ∈ a.1
  template_covers : ∀ x : X,
    ∃ a : {a : Set X // a ∈ templateEdges}, x ∈ a.1

namespace UniformFillingData

variable {V X : Type v} (U : UniformFillingData V X)

abbrev OldEdge := {f : Set V // f ∈ U.oldEdges}
abbrev TemplateEdge := {a : Set X // a ∈ U.templateEdges}
abbrev Occurrence := U.OldEdge × U.TemplateEdge

/-- A genuine edge carrier in the copy of the template on the old edge. -/
def imageCarrier (c : U.Occurrence) : Set V := U.place c.1 '' c.2.1

/-- No template edge extends outside the old edge on which it is placed. -/
theorem imageCarrier_subset (c : U.Occurrence) :
    U.imageCarrier c ⊆ c.1.1 := by
  rintro x ⟨y, _hy, rfl⟩
  rw [← U.range_place c.1]
  exact ⟨y, rfl⟩

/-- An image has only one containing old edge, rather than merely one
arbitrarily selected owner. The template's two vertices are used here. -/
theorem unique_old_cover (c : U.Occurrence) (g : U.OldEdge)
    (hSub : U.imageCarrier c ⊆ g.1) : c.1 = g := by
  by_contra hne
  obtain ⟨x, y, hxy, hx, hy⟩ := U.template_pair c.2
  have hxImage : U.place c.1 x ∈ U.imageCarrier c := ⟨x, hx, rfl⟩
  have hyImage : U.place c.1 y ∈ U.imageCarrier c := ⟨y, hy, rfl⟩
  apply hxy
  apply (U.place c.1).injective
  exact U.old_linear c.1 g hne
    ⟨U.imageCarrier_subset c hxImage, hSub hxImage⟩
    ⟨U.imageCarrier_subset c hyImage, hSub hyImage⟩

/-- Equal physical images have the same old edge AND the same local edge.
This proves that the generated family does not collapse different labels. -/
theorem imageCarrier_injective : Function.Injective U.imageCarrier := by
  rintro ⟨f, a⟩ ⟨g, b⟩ h
  have hfg : f = g := U.unique_old_cover (f, a) g (by
    rw [h]
    exact U.imageCarrier_subset (g, b))
  subst g
  have hab : a = b := by
    apply Subtype.ext
    ext x
    constructor
    · intro hx
      have him : U.place f x ∈ U.imageCarrier (f, b) := by
        rw [← h]
        exact ⟨x, hx, rfl⟩
      obtain ⟨y, hy, hyx⟩ := him
      have heq : y = x := (U.place f).injective hyx
      simpa only [heq] using hy
    · intro hx
      have him : U.place f x ∈ U.imageCarrier (f, a) := by
        rw [h]
        exact ⟨x, hx, rfl⟩
      obtain ⟨y, hy, hyx⟩ := him
      have heq : y = x := (U.place f).injective hyx
      simpa only [heq] using hy
  subst b
  rfl

/-- Keep every image edge in every fibre. -/
def generatedEdges : Set (Set V) := Set.range U.imageCarrier

abbrev GeneratedEdge := {e : Set V // e ∈ U.generatedEdges}

def encode (c : U.Occurrence) : U.GeneratedEdge :=
  ⟨U.imageCarrier c, ⟨c, rfl⟩⟩

noncomputable def decode (e : U.GeneratedEdge) : U.Occurrence :=
  Classical.choose e.2

@[simp] theorem imageCarrier_decode (e : U.GeneratedEdge) :
    U.imageCarrier (U.decode e) = e.1 := Classical.choose_spec e.2

@[simp] theorem decode_encode (c : U.Occurrence) : U.decode (U.encode c) = c := by
  apply U.imageCarrier_injective
  exact U.imageCarrier_decode (U.encode c)

@[simp] theorem encode_decode (e : U.GeneratedEdge) : U.encode (U.decode e) = e := by
  apply Subtype.ext
  exact U.imageCarrier_decode e

/-- Actual filling of the old hypergraph by all placed template edges.
The old cover and its full pointwise coverage are constructed. -/
noncomputable def toTrainFilling : TrainFilling V where
  oldEdges := U.oldEdges
  newEdges := U.generatedEdges
  cover e := (U.decode e).1
  contained := by
    intro e
    have h := U.imageCarrier_subset (U.decode e)
    simpa only [U.imageCarrier_decode] using h
  covering := by
    intro f x hx
    have hxRange : x ∈ Set.range (U.place f) := by
      rw [U.range_place f]
      exact hx
    obtain ⟨y, hy⟩ := hxRange
    obtain ⟨a, ha⟩ := U.template_covers y
    refine ⟨U.encode (f, a), ?_, ?_⟩
    · exact congrArg Prod.fst (U.decode_encode (f, a))
    · exact ⟨y, ha, hy⟩

/-- The complete new physical edge set is canonically indexed by pairs
(old edge, local template edge), not a quotient with lost occurrences. -/
noncomputable def edgeEquiv : U.Occurrence ≃ U.toTrainFilling.NewEdge where
  toFun := U.encode
  invFun := U.decode
  left_inv := U.decode_encode
  right_inv := U.encode_decode

@[simp] theorem edgeEquiv_carrier (c : U.Occurrence) :
    (U.edgeEquiv c).1 = U.imageCarrier c := rfl

@[simp] theorem edgeEquiv_cover (c : U.Occurrence) :
    U.toTrainFilling.cover (U.edgeEquiv c) = c.1 := by
  exact congrArg Prod.fst (U.decode_encode c)

/-- Every physical generated edge has exactly its constructed old cover
as a containing old edge. -/
theorem toTrainFilling_cover_unique (e : U.toTrainFilling.NewEdge)
    (g : U.OldEdge) (hSub : e.1 ⊆ g.1) :
    U.toTrainFilling.cover e = g := by
  apply U.unique_old_cover (U.decode e) g
  simpa only [U.imageCarrier_decode] using hSub

/-- Finite local and old edge sets give a finite generated edge set. -/
theorem finite_newEdges [Finite U.OldEdge] [Finite U.TemplateEdge] :
    Finite U.toTrainFilling.NewEdge :=
  Finite.of_surjective U.edgeEquiv U.edgeEquiv.surjective

private theorem image_inter_eq (i : X ↪ V) (a b : Set X) :
    (i '' a) ∩ (i '' b) = i '' (a ∩ b) := by
  ext x
  constructor
  · rintro ⟨⟨y, hy, hyx⟩, ⟨z, hz, hzx⟩⟩
    have hyz : y = z := i.injective (hyx.trans hzx.symm)
    exact ⟨y, ⟨hy, by simpa only [← hyz] using hz⟩, hyx⟩
  · rintro ⟨y, ⟨hy, hz⟩, rfl⟩
    exact ⟨⟨y, hy, rfl⟩, ⟨y, hz, rfl⟩⟩

/-- Intersections within one generated fibre are exact images of local
intersections. This supplies the genuine first-fibre parameter. -/
theorem first_fibre_parameter (localAllowed : Set X) (allowed : Set V)
    (hLocal : ∀ a b : U.TemplateEdge, a ≠ b → a.1 ∩ b.1 ⊆ localAllowed)
    (hPlace : ∀ f : U.OldEdge, U.place f '' localAllowed ⊆ allowed) :
    ∀ e f : U.toTrainFilling.NewEdge, e ≠ f →
      U.toTrainFilling.cover e = U.toTrainFilling.cover f →
        e.1 ∩ f.1 ⊆ allowed := by
  intro e f hne hc
  obtain ⟨⟨a, i⟩, rfl⟩ := U.edgeEquiv.surjective e
  obtain ⟨⟨b, j⟩, rfl⟩ := U.edgeEquiv.surjective f
  simp only [U.edgeEquiv_cover] at hc
  subst b
  have hij : i ≠ j := by
    intro heq
    subst j
    exact hne rfl
  change (U.place a '' i.1) ∩ (U.place a '' j.1) ⊆ allowed
  rw [image_inter_eq]
  rintro x ⟨y, hy, rfl⟩
  exact hPlace a ⟨y, hLocal i j hij hy, rfl⟩

/-- Linearity inside each generated fibre follows from template linearity. -/
theorem fibre_linear
    (hLocal : ∀ a b : U.TemplateEdge, a ≠ b → (a.1 ∩ b.1).Subsingleton) :
    ∀ e f : U.toTrainFilling.NewEdge, e ≠ f →
      U.toTrainFilling.cover e = U.toTrainFilling.cover f →
        (e.1 ∩ f.1).Subsingleton := by
  intro e f hne hc
  obtain ⟨⟨a, i⟩, rfl⟩ := U.edgeEquiv.surjective e
  obtain ⟨⟨b, j⟩, rfl⟩ := U.edgeEquiv.surjective f
  simp only [U.edgeEquiv_cover] at hc
  subst b
  have hij : i ≠ j := by
    intro heq
    subst j
    exact hne rfl
  change ((U.place a '' i.1) ∩ (U.place a '' j.1)).Subsingleton
  rw [image_inter_eq]
  rintro x ⟨y, hy, rfl⟩ z ⟨w, hw, rfl⟩
  exact congrArg (U.place a) (hLocal i j hij hy hw)

/-- The whole constructed filling is linear: equal covers use the local
template, and distinct covers use containment and old edge linearity. -/
theorem generated_linear
    (hLocal : ∀ a b : U.TemplateEdge, a ≠ b → (a.1 ∩ b.1).Subsingleton) :
    ∀ e f : U.toTrainFilling.NewEdge, e ≠ f →
      (e.1 ∩ f.1).Subsingleton :=
  U.toTrainFilling.edgeLinear_of_fibreLinear U.old_linear (U.fibre_linear hLocal)

/-- Construct the filling and its full restored invariants directly from
local template data and the old proper-cut bounds. The old equality cut
is included; neither universal top is an additional girth coordinate. -/
theorem restored_parameters_and_tailSystemGirth
    {I : Type v} {m : ℕ} (T : EdgeTrainLevels U.OldEdge m)
    (copyCarrier : I → Set V) (copyEdges : I → Set U.OldEdge)
    (allowed : Fin (m + 1 + 1) → Set V) (g : Fin m → ℕ)
    (localAllowed : Set X)
    (hLocalParameter : ∀ a b : U.TemplateEdge, a ≠ b →
      a.1 ∩ b.1 ⊆ localAllowed)
    (hPlace : ∀ f : U.OldEdge, U.place f '' localAllowed ⊆
      allowed (0 : Fin (m + 1)).succ)
    (hLocalLinear : ∀ a b : U.TemplateEdge, a ≠ b →
      (a.1 ∩ b.1).Subsingleton)
    (hOldParameters : T.AdjacentParameters (fun e => e.1)
      (fun ν => allowed ν.succ))
    (hOldGirth : ∀ j : Fin m,
      (U.toTrainFilling.oldCutData T copyCarrier copyEdges j.castSucc).FullSystemGirthGT (g j)) :
    (U.toTrainFilling.inheritedTrain T).AdjacentParameters (fun e => e.1) allowed ∧
      ∀ j : Fin m,
        (U.toTrainFilling.inheritedCutData T copyCarrier copyEdges j.castSucc).FullSystemGirthGT (g j) := by
  exact U.toTrainFilling.inheritedTrain_parameters_and_tailSystemGirth
    T copyCarrier copyEdges allowed g
    (U.first_fibre_parameter localAllowed _ hLocalParameter hPlace)
    hOldParameters hOldGirth (U.fibre_linear hLocalLinear)

section RelationalTemplate

open StructuralRamsey.RelStructure
universe u
variable {L : RelLanguage.{u}} {UA : Type v}
variable (A : RelStructure L UA) (R : RelStructure L X) [Nontrivial UA]
variable (N : Set (Set V))
variable (place : {f : Set V // f ∈ N} → (X ↪ V))
variable (hRange : ∀ f, Set.range (place f) = f.1)
variable (hOldLinear : ∀ f g : {f : Set V // f ∈ N},
  f ≠ g → (f.1 ∩ g.1).Subsingleton)
variable (hCovers : ∀ x : X, ∃ a : Embedding A R, x ∈ copyCarrier a)

/-- The actual A-support of a covered relational template supplies the
pair and coverage fields. No separate two-vertex certificate for every
edge is an application premise once A is nontrivial. -/
def ofSupportCopies : UniformFillingData V X where
  oldEdges := N
  templateEdges := supportCopies A R
  place := place
  range_place := hRange
  old_linear := hOldLinear
  template_pair := by
    intro a
    obtain ⟨e, he⟩ := a.2
    obtain ⟨x, y, hxy⟩ := exists_pair_ne UA
    refine ⟨e x, e y, fun h => hxy (e.injective h), ?_, ?_⟩
    · rw [he]
      exact ⟨x, rfl⟩
    · rw [he]
      exact ⟨y, rfl⟩
  template_covers := by
    intro x
    obtain ⟨a, ha⟩ := hCovers x
    exact ⟨⟨copyCarrier a, ⟨a, rfl⟩⟩, ha⟩

/-- Reuse the existing relational-to-physical linearity theorem for the
complete local A-support; no designated-edge restriction is made. -/
theorem ofSupportCopies_generated_linear (hLinear : ALinear A R) :
    let U := ofSupportCopies A R N place hRange hOldLinear hCovers
    ∀ e f : U.toTrainFilling.NewEdge, e ≠ f → (e.1 ∩ f.1).Subsingleton := by
  let U := ofSupportCopies A R N place hRange hOldLinear hCovers
  exact U.generated_linear
    (oldACarrier_edges_inter_subsingleton_of_aLinear A R hLinear)

end RelationalTemplate

end UniformFillingData
end StructuralRamsey.Girth
