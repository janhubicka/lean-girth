import Girth.TrainRecursiveWitnessPass

set_option autoImplicit false
set_option Elab.async false

/-!
# Global allowed-part compatibility for a nonpartite Ramsey base

A general ordered shorter train need not be partite over the vertices
of its coloured edge type. Its Ramsey picture can instead use a larger
base D, with a prescribed B-family in D.

For such a picture the local condition
  b ⁻¹' allowedD ν ⊆ allowedB ν   (for all prescribed b)
is NOT sufficient by itself to show that every vertex in allowedD ν
has an originally permitted coarse predicate: allowedD ν may include
points of D outside all the prescribed base copies.

A natural sufficient hypothesis is coverage of permitted base vertices
by the designated B-family. Together with the local pullback constraints
it gives a global bound, which can then be pulled back through the
actual part map of any larger D-partite picture.

All statements concern actual labelled base points. No designated
copies are identified by carriers, and no ambient vertex is removed.
-/

namespace StructuralRamsey.Girth.TrainRecursiveWitness

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}} {VB W Q Y : Type v}

/-- The original selected-family pullback condition and a genuine
coverage of the allowed base vertices imply that every permitted D-point
is the image of a permitted B-point in a prescribed B-copy. This is
exactly the extra global information needed when forgetting auxiliary
D-parts and returning to the original coarse unary predicates. -/
theorem allowedBase_covered_of_familyPullbacks
    (B : RelStructure L VB) (D : RelStructure L W)
    (family : Set (Embedding B D)) {m : ℕ}
    (allowedB : Fin (m + 1) → Set VB)
    (allowedD : Fin (m + 1) → Set W)
    (hCover : ∀ (ν : Fin (m + 1)) (y : W), y ∈ allowedD ν →
      ∃ b : Embedding B D, b ∈ family ∧
        ∃ x : VB, b x = y)
    (hPull : ∀ b : Embedding B D, b ∈ family →
      ∀ ν : Fin (m + 1), b ⁻¹' allowedD ν ⊆ allowedB ν) :
    ∀ (ν : Fin (m + 1)) (y : W), y ∈ allowedD ν →
      ∃ b : Embedding B D, b ∈ family ∧
        ∃ x : VB, x ∈ allowedB ν ∧ b x = y := by
  intro ν y hy
  obtain ⟨b, hb, x, hxy⟩ := hCover ν y hy
  refine ⟨b, hb, x, ?_, hxy⟩
  apply hPull b hb ν
  change b x ∈ allowedD ν
  rw [hxy]
  exact hy

/-- Every permitted base point has an original allowed COARSE predicate,
provided prescribed base embeddings respect those predicates.
This is the precise transport needed from an auxiliary D-part map to
the original (possibly non-fine-partite) coloured edge structure. -/
theorem allowedBase_coarsePredicate_of_coverage
    (B : RelStructure L VB) (D : RelStructure L W)
    (family : Set (Embedding B D)) {m : ℕ}
    (allowedB : Fin (m + 1) → Set VB)
    (allowedD : Fin (m + 1) → Set W)
    (predB : VB → Q) (predD : W → Q)
    (permitted : Fin (m + 1) → Set Q)
    (hPred : ∀ b : Embedding B D, b ∈ family →
      ∀ x : VB, predD (b x) = predB x)
    (hAllowed : ∀ ν : Fin (m + 1),
      allowedB ν ⊆ predB ⁻¹' permitted ν)
    (hCover : ∀ (ν : Fin (m + 1)) (y : W), y ∈ allowedD ν →
      ∃ b : Embedding B D, b ∈ family ∧
        ∃ x : VB, b x = y)
    (hPull : ∀ b : Embedding B D, b ∈ family →
      ∀ ν : Fin (m + 1), b ⁻¹' allowedD ν ⊆ allowedB ν) :
    ∀ ν : Fin (m + 1), allowedD ν ⊆ predD ⁻¹' permitted ν := by
  intro ν y hy
  obtain ⟨b, hb, x, hx, hxy⟩ :=
    allowedBase_covered_of_familyPullbacks B D family
      allowedB allowedD hCover hPull ν y hy
  change predD y ∈ permitted ν
  rw [← hxy, hPred b hb x]
  exact hAllowed ν hx

/-- If a D-partite picture has part map into D, its allowed-vertex
parameters are contained in the original coarse-predicate parameters
whenever D's permitted part set is globally compatible. There is no
assumption that the target train is A-partite. -/
theorem allowedVertices_coarsePredicate_of_globalBaseBound
    (part : Y → W) (predD : W → Q)
    (allowedD : Set W) (permitted : Set Q)
    (hAllowed : allowedD ⊆ predD ⁻¹' permitted) :
    part ⁻¹' allowedD ⊆ (predD ∘ part) ⁻¹' permitted := by
  intro y hy
  exact hAllowed hy

/-- The canonical choice of allowed D-parts determined only by the
ORIGINAL coarse unary predicates. This is independent of the selected
B-family and controls ALL ambient D-vertices, including those not in
any designated B-image. -/
def canonicalCoarseAllowed
    (predD : W → Q) {m : ℕ}
    (permitted : Fin (m + 1) → Set Q) :
    Fin (m + 1) → Set W :=
  fun ν => predD ⁻¹' permitted ν

/-- For a coarse-predicate-preserving B-embedding, canonical allowed
D-parts restrict to precisely the original coarse permitted B-parts.
No selected-family coverage of D is needed because D's allowed sets
have been CHOSEN globally, rather than specified arbitrarily. -/
theorem canonicalCoarseAllowed_pullback
    (B : RelStructure L VB) (D : RelStructure L W)
    (b : Embedding B D)
    (predB : VB → Q) (predD : W → Q)
    (hPred : ∀ x : VB, predD (b x) = predB x)
    {m : ℕ} (permitted : Fin (m + 1) → Set Q) :
    ∀ ν : Fin (m + 1),
      b ⁻¹' canonicalCoarseAllowed predD permitted ν =
        predB ⁻¹' permitted ν := by
  intro ν
  ext x
  change predD (b x) ∈ permitted ν ↔ predB x ∈ permitted ν
  rw [hPred x]

/-- If original allowed B-parts contain every point with a permitted
coarse predicate, canonical allowed D-parts satisfy the earlier
selected-family pullback hypothesis, without ambient coverage. -/
theorem canonicalCoarseAllowed_familyPullback
    (B : RelStructure L VB) (D : RelStructure L W)
    (family : Set (Embedding B D))
    (predB : VB → Q) (predD : W → Q)
    {m : ℕ}
    (permitted : Fin (m + 1) → Set Q)
    (allowedB : Fin (m + 1) → Set VB)
    (hPred : ∀ b : Embedding B D, b ∈ family →
      ∀ x : VB, predD (b x) = predB x)
    (hAllowed : ∀ ν : Fin (m + 1),
      predB ⁻¹' permitted ν ⊆ allowedB ν) :
    ∀ b : Embedding B D, b ∈ family →
      ∀ ν : Fin (m + 1),
        b ⁻¹' canonicalCoarseAllowed predD permitted ν ⊆
          allowedB ν := by
  intro b hb ν x hx
  have hCoarse : predB x ∈ permitted ν := by
    change predD (b x) ∈ permitted ν at hx
    rw [hPred b hb x] at hx
    exact hx
  exact hAllowed ν hCoarse

/-- The output part map composes with the coarse predicate map.
This is a DEFINITONAL global identity, requiring no selected-family
or base-coverage argument at all, provided the canonical allowedD
sets are used in the constructed witness. -/
theorem canonicalCoarseAllowed_output
    (part : Y → W) (predD : W → Q)
    {m : ℕ} (permitted : Fin (m + 1) → Set Q) :
    ∀ ν : Fin (m + 1),
      part ⁻¹' canonicalCoarseAllowed predD permitted ν =
        (predD ∘ part) ⁻¹' permitted ν := by
  intro ν
  rfl

/-- The actual train parameter predicate also transports directly:
taking canonical coarse allowed sets at the D-level leaves the
adjacent-sibling intersection condition unchanged when the output
picture's part map is composed with the coarse predicate map.

This is the precise train-level boundary needed by the nonpartite
forest-to-order step, not merely an equality of preimage sets. -/
theorem adjacentParameters_of_canonicalCoarseAllowed
    {Edge : Type v} {m : ℕ} (T : EdgeTrainLevels Edge m)
    (edge : Edge → Set Y) (part : Y → W) (predD : W → Q)
    (permitted : Fin (m + 1) → Set Q)
    (hParam : T.AdjacentParameters edge
      (fun ν => part ⁻¹' canonicalCoarseAllowed predD permitted ν)) :
    T.AdjacentParameters edge
      (fun ν => (predD ∘ part) ⁻¹' permitted ν) := by
  change T.AdjacentParameters edge
    (fun ν => part ⁻¹' (predD ⁻¹' permitted ν))
  exact hParam

/-- The output's ACTUAL coarse unary predicate need not be the
coarse predicate of its part: Partite.System stores an arbitrary
part map subject to transversality, not a relational homomorphism.
To pass from the base predicate to the actual output predicate one
must establish this compatibility (or its restriction to contacts).

With that premise, the canonical coarse allowed sets give the
actual original-vertex train parameters, not merely parameters for
the artificial predicate obtained by composing part and predD. -/
theorem adjacentParameters_of_canonicalCoarseAllowed_and_colourCompatibility
    {Edge : Type v} {m : ℕ} (T : EdgeTrainLevels Edge m)
    (edge : Edge → Set Y) (part : Y → W)
    (predD : W → Q) (predOut : Y → Q)
    (permitted : Fin (m + 1) → Set Q)
    (hColour : ∀ y : Y, predOut y = predD (part y))
    (hParam : T.AdjacentParameters edge
      (fun ν => part ⁻¹' canonicalCoarseAllowed predD permitted ν)) :
    T.AdjacentParameters edge
      (fun ν => predOut ⁻¹' permitted ν) := by
  have hEq :
      (fun ν : Fin (m + 1) =>
        (predD ∘ part) ⁻¹' permitted ν) =
      (fun ν : Fin (m + 1) =>
        predOut ⁻¹' permitted ν) := by
    funext ν
    ext y
    change predD (part y) ∈ permitted ν ↔ predOut y ∈ permitted ν
    rw [hColour y]
  rw [← hEq]
  exact adjacentParameters_of_canonicalCoarseAllowed
    T edge part predD permitted hParam

/-- It can suffice to prove colour/part compatibility only on
vertices that actually appear as cut contacts. There is no need to
identify the unary colours of irrelevant isolated output points. -/
theorem usedContact_originalPredicate_of_colourCompatibility
    {m : ℕ} (contact : Fin (m + 1) → Set Y)
    (part : Y → W) (predD : W → Q) (predOut : Y → Q)
    (permitted : Fin (m + 1) → Set Q)
    (hContactCoarse : ∀ ν : Fin (m + 1),
      contact ν ⊆ (predD ∘ part) ⁻¹' permitted ν)
    (hContactColour : ∀ (ν : Fin (m + 1)) (y : Y),
      y ∈ contact ν → predOut y = predD (part y)) :
    ∀ ν : Fin (m + 1),
      contact ν ⊆ predOut ⁻¹' permitted ν := by
  intro ν y hy
  have hPermitted : predD (part y) ∈ permitted ν :=
    hContactCoarse ν hy
  change predOut y ∈ permitted ν
  rw [hContactColour ν y hy]
  exact hPermitted

/-- A weaker sufficient condition than coverage of *every* allowed
D-base point: it is enough that the actually USED contact vertices
of the output have base parts in prescribed B-images.

The parameter information hContact is exactly the form supplied by
an output train's adjacent-parameter restriction at one cut. The extra
coverage input is only on genuine contacts, not on unrelated D-points
which happen to lie in allowedD. This distinction can simplify the
unrestricted forest-to-order transfer when selected-family coverage of
the ENTIRE Ramsey base is unavailable. -/
theorem usedContact_coarsePredicate_of_localPullback
    (B : RelStructure L VB) (D : RelStructure L W)
    (family : Set (Embedding B D)) {m : ℕ}
    (part : Y → W)
    (contact : Fin (m + 1) → Set Y)
    (allowedB : Fin (m + 1) → Set VB)
    (allowedD : Fin (m + 1) → Set W)
    (predB : VB → Q) (predD : W → Q)
    (permitted : Fin (m + 1) → Set Q)
    (hContact : ∀ ν : Fin (m + 1),
      contact ν ⊆ part ⁻¹' allowedD ν)
    (hContactCovered : ∀ (ν : Fin (m + 1)) (y : Y),
      y ∈ contact ν →
        ∃ b : Embedding B D, b ∈ family ∧
          ∃ x : VB, b x = part y)
    (hPull : ∀ b : Embedding B D, b ∈ family →
      ∀ ν : Fin (m + 1), b ⁻¹' allowedD ν ⊆ allowedB ν)
    (hPred : ∀ b : Embedding B D, b ∈ family →
      ∀ x : VB, predD (b x) = predB x)
    (hAllowed : ∀ ν : Fin (m + 1),
      allowedB ν ⊆ predB ⁻¹' permitted ν) :
    ∀ ν : Fin (m + 1),
      contact ν ⊆ (predD ∘ part) ⁻¹' permitted ν := by
  intro ν y hy
  have hPermittedBase : part y ∈ allowedD ν := hContact ν hy
  obtain ⟨b, hb, x, hx⟩ := hContactCovered ν y hy
  have hAllowedSource : x ∈ allowedB ν := by
    apply hPull b hb ν
    change b x ∈ allowedD ν
    rw [hx]
    exact hPermittedBase
  change predD (part y) ∈ permitted ν
  rw [← hx, hPred b hb x]
  exact hAllowed ν hAllowedSource

/-- The local pullback condition ALONE cannot control the ambient base:
a chosen family may miss a permitted D-point. The displayed witness has
an empty allowed B-set but a nonempty allowed D-set disjoint from its
only prescribed B-image. -/
theorem localPullback_does_not_imply_globalCover :
    ∃ (f : Unit → Bool) (allowedB : Set Unit)
        (allowedD : Set Bool),
      (∀ x : Unit, f x ∈ allowedD → x ∈ allowedB) ∧
      (∃ y : Bool, y ∈ allowedD ∧
        ∀ x : Unit, y ≠ f x) := by
  refine ⟨(fun _ : Unit => false), ∅, {true}, ?_, true, ?_, ?_⟩
  · intro x hx
    have hFalse : (false : Bool) ∈ ({true} : Set Bool) := hx
    simp at hFalse
  · simp
  · intro x
    simp

end StructuralRamsey.Girth.TrainRecursiveWitness
