import Girth.ForestActualRecursiveSupport

/-!
# Track 1 — one genuine B embedding for each physical B-copy carrier

Do NOT assume that equality of full B-copy image carriers forces equality
of the original embedding labels. Instead, index the physical selected
family by its actual vertex carriers, and select an original embedding
representing each carrier. This works without rigidity or any
unverified "ordered embedding equality" lemma.

The representative remains an actual embedding in the EHN-selected
family. Strongness, controlled intersections and the selected Ramsey
arrow remain true after normalization; the arrow is invariant because
every A-copy within a representative's carrier factors into any other
B-embedding with that same induced image carrier.

-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v w
variable {L : RelLanguage.{u}} {UA VB V : Type v}

/-- The selected physical B-copy carriers, identified up to equality
of their actual image vertex sets. -/
def Track1PhysicalBCarrier
    {B : RelStructure L VB} {D : RelStructure L V}
    (family : Set (Embedding B D)) :=
  {S : Set V // ∃ b : Embedding B D,
    b ∈ family ∧ copyCarrier b = S}

/-- Choose a genuine selected embedding of B for each actual carrier. -/
noncomputable def track1_physicalRepresentative
    {B : RelStructure L VB} {D : RelStructure L V}
    (family : Set (Embedding B D))
    (q : Track1PhysicalBCarrier family) :
    Embedding B D :=
  Classical.choose q.2

theorem track1_physicalRepresentative_spec
    {B : RelStructure L VB} {D : RelStructure L V}
    (family : Set (Embedding B D))
    (q : Track1PhysicalBCarrier family) :
    track1_physicalRepresentative family q ∈ family ∧
      copyCarrier (track1_physicalRepresentative family q) = q.1 :=
  Classical.choose_spec q.2

/-- Two distinct physical carrier labels remain physically distinct. -/
theorem track1_physicalRepresentative_distinct
    {B : RelStructure L VB} {D : RelStructure L V}
    (family : Set (Embedding B D))
    {i j : Track1PhysicalBCarrier family} (hij : i ≠ j) :
    ¬ SameCopy (track1_physicalRepresentative family i)
        (track1_physicalRepresentative family j) := by
  intro hEq
  apply hij
  apply Subtype.ext
  calc
    i.1 = copyCarrier (track1_physicalRepresentative family i) :=
      (track1_physicalRepresentative_spec family i).2.symm
    _ = copyCarrier (track1_physicalRepresentative family j) := hEq
    _ = j.1 := (track1_physicalRepresentative_spec family j).2

/-- Different physical labels have different COMPLETE B-support
pieces. This holds even if B is not ordered, and includes isolated
source vertices in the piece carrier. -/
theorem track1_physicalRepresentative_supportPieces_injective
    (A : RelStructure L UA)
    {B : RelStructure L VB} {D : RelStructure L V}
    (family : Set (Embedding B D)) :
    Function.Injective (fun q : Track1PhysicalBCarrier family =>
      bSupportPiece A (track1_physicalRepresentative family q)) := by
  intro i j hPiece
  apply Subtype.ext
  calc
    i.1 = copyCarrier (track1_physicalRepresentative family i) :=
      (track1_physicalRepresentative_spec family i).2.symm
    _ = copyCarrier (track1_physicalRepresentative family j) := by
      exact congrArg HypergraphPiece.carrier hPiece
    _ = j.1 := (track1_physicalRepresentative_spec family j).2

/-- The representative family retains every selected B image, up to
the *same carrier*. This suffices for the source's monochromatic arrow. -/
theorem track1_physicalRepresentative_arrow
    (A : RelStructure L UA)
    {B : RelStructure L VB} {D : RelStructure L V}
    (family : Set (Embedding B D))
    {κ : Type w}
    (hArrow : ∀ χ : Embedding A D → κ,
      ∃ b : Embedding B D, b ∈ family ∧
        ∀ a₁ a₂ : Embedding A B,
          χ (b.comp a₁) = χ (b.comp a₂)) :
    ∀ χ : Embedding A D → κ,
      ∃ q : Track1PhysicalBCarrier family,
        ∀ a₁ a₂ : Embedding A B,
          χ ((track1_physicalRepresentative family q).comp a₁) =
            χ ((track1_physicalRepresentative family q).comp a₂) := by
  classical
  intro χ
  obtain ⟨b, hb, hMono⟩ := hArrow χ
  let q : Track1PhysicalBCarrier family :=
    ⟨copyCarrier b, ⟨b, hb, rfl⟩⟩
  let rep := track1_physicalRepresentative family q
  have hSame : copyCarrier rep = copyCarrier b :=
    (track1_physicalRepresentative_spec family q).2
  have hFactor (a : Embedding A B) :
      ∃ a' : Embedding A B, rep.comp a = b.comp a' := by
    have hSub : copyCarrier (rep.comp a) ⊆ copyCarrier b := by
      rw [← hSame]
      rintro z ⟨u, rfl⟩
      exact ⟨a u, rfl⟩
    have hRange : ∀ u : UA, ∃ v : VB,
        (rep.comp a) u = b v := by
      intro u
      obtain ⟨v, hv⟩ := hSub ⟨u, rfl⟩
      exact ⟨v, hv.symm⟩
    let a' : Embedding A B := (rep.comp a).factorThroughRange b hRange
    refine ⟨a', ?_⟩
    apply Embedding.ext
    intro u
    exact Classical.choose_spec (hRange u)
  refine ⟨q, ?_⟩
  intro a₁ a₂
  obtain ⟨b₁, hb₁⟩ := hFactor a₁
  obtain ⟨b₂, hb₂⟩ := hFactor a₂
  change χ (rep.comp a₁) = χ (rep.comp a₂)
  calc
    χ (rep.comp a₁) = χ (b.comp b₁) := congrArg χ hb₁
    _ = χ (b.comp b₂) := hMono b₁ b₂
    _ = χ (rep.comp a₂) := (congrArg χ hb₂).symm

#print axioms StructuralRamsey.Girth.track1_physicalRepresentative_supportPieces_injective
#print axioms StructuralRamsey.Girth.track1_physicalRepresentative_arrow

end StructuralRamsey.Girth
