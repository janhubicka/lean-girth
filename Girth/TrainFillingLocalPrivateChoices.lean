import Girth.TrainFillingPrivateUniform
import Girth.TrainFillingPrivateActualSourceEdgeEquiv

set_option autoImplicit false

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}} {A V P X : Type v}
variable (small : RelStructure L A) (B : RelStructure L V) (R : RelStructure L X)
variable (carrier : P → Set V)
variable (localCopy : ∀ p : P, Embedding (B.induce (carrier p)) R)
variable (hStrong : ∀ p : P, AStrong small R (copyCarrier (localCopy p)))
variable (hCover : ∀ p : P, ∀ x : {v : V // v ∈ carrier p},
  ∃ a : Embedding small (B.induce (carrier p)), x ∈ copyCarrier a)

/-- Each genuine induced first wagon has its own local relational map
into the common template and its own selected local edge family. -/
noncomputable def privateChoiceOfLocalCopies : PrivateWagonInput V P X where
  oldCarrier := carrier
  coordinate := fun p => (localCopy p).toFunctionEmbedding
  templateEdges := supportCopies small R
  selectedEdges := fun p =>
    (UniformPrivateTemplate.ofStrongEmbedding small (B.induce (carrier p)) R
      (localCopy p) (hStrong p) (hCover p)).selectedEdges
  selected_inside := by
    intro p e he
    obtain ⟨a, ha⟩ := he
    rw [ha]
    rintro y ⟨x, _, rfl⟩
    exact ⟨x, rfl⟩
  local_strong := by
    intro p e x y hxy hx hy hxr hyr
    exact (UniformPrivateTemplate.ofStrongEmbedding small (B.induce (carrier p)) R
      (localCopy p) (hStrong p) (hCover p)).strong e x y hxy hx hy hxr hyr
  local_cover := by
    intro p x
    obtain ⟨a, ha⟩ := hCover p x
    refine ⟨⟨copyCarrier ((localCopy p).comp a), ⟨_, rfl⟩⟩, ?_, ?_⟩
    · exact ⟨⟨copyCarrier a, ⟨a, rfl⟩⟩,
        (UniformPrivateTemplate.image_copyCarrier_comp small (B.induce (carrier p)) R
          (localCopy p) a).symm⟩
    · obtain ⟨z, rfl⟩ := ha
      exact ⟨z, rfl⟩

local notation "W" => privateChoiceOfLocalCopies small B R carrier localCopy hStrong hCover

/-- The local support embedding becomes the actual selected physical
edge in the private filling of its own first wagon. -/
noncomputable def privateChoice_localEdge
    (p : P) (a : Embedding small (B.induce (carrier p))) : (W).Edge :=
  (p, ⟨copyCarrier ((localCopy p).comp a), ⟨_, rfl⟩⟩)

theorem privateChoice_localEdge_mem_target
    (p : P) (a : Embedding small (B.induce (carrier p))) :
    privateChoice_localEdge small B R carrier localCopy hStrong hCover p a ∈ (W).targetEdges :=
  ⟨⟨copyCarrier a, ⟨a, rfl⟩⟩,
    (UniformPrivateTemplate.image_copyCarrier_comp small (B.induce (carrier p)) R
      (localCopy p) a).symm⟩

/-- The private filling sends the selected edge to its original vertices,
with no private vertices inserted into that particular edge. -/
theorem privateChoice_localEdge_carrier
    (p : P) (a : Embedding small (B.induce (carrier p))) :
    (W).edgeCarrier (privateChoice_localEdge small B R carrier localCopy hStrong hCover p a) =
      (Sum.inl : V → (W).Vertex) '' copyCarrier ((inclusion B (carrier p)).comp a) := by
  change (W).place p '' copyCarrier ((localCopy p).comp a) =
    (Sum.inl : V → (W).Vertex) '' copyCarrier ((inclusion B (carrier p)).comp a)
  ext y
  constructor
  · rintro ⟨x, ⟨z, rfl⟩, rfl⟩
    refine ⟨(a z).1, ⟨z, rfl⟩, ?_⟩
    exact ((W).place_old p (a z)).symm
  · rintro ⟨_, ⟨z, rfl⟩, rfl⟩
    exact ⟨localCopy p (a z), ⟨z, rfl⟩, (W).place_old p (a z)⟩

/-- Every selected physical edge comes from a genuine relational edge in
its original first wagon. -/
theorem privateChoice_targetEdge_relational
    (e : (W).Edge) (he : e ∈ (W).targetEdges) :
    ∃ a : Embedding small (B.induce (carrier e.1)),
      privateChoice_localEdge small B R carrier localCopy hStrong hCover e.1 a = e := by
  rcases e with ⟨p, e⟩
  obtain ⟨f, hf⟩ := he
  obtain ⟨a, ha⟩ := f.2
  refine ⟨a, Prod.ext rfl (Subtype.ext ?_)⟩
  change copyCarrier ((localCopy p).comp a) = e.1
  change e.1 = (localCopy p).toFunctionEmbedding '' f.1 at hf
  rw [← UniformPrivateTemplate.image_copyCarrier_comp small (B.induce (carrier p)) R
    (localCopy p) a, ← ha]
  exact hf.symm

/-- Conversely the true owner of any original edge supplies its complete
selected physical edge in the private filling. -/
theorem privateChoice_originalEdge_relational
    [Nontrivial A]
    (owner : {e : Set V // e ∈ supportCopies small B} → P)
    (hOwner : ∀ e, e.1 ⊆ carrier (owner e))
    (hLinear : ∀ p q : P, p ≠ q → (carrier p ∩ carrier q).Subsingleton)
    (a : Embedding small B) :
    ∃ e : (W).Edge, e.1 = owner ⟨copyCarrier a, ⟨a, rfl⟩⟩ ∧ e ∈ (W).targetEdges ∧
      (W).edgeCarrier e = (Sum.inl : V → (W).Vertex) '' copyCarrier a := by
  obtain ⟨⟨p, f⟩, hf⟩ :=
    firstWagonEdgeToOriginal_surjective small B carrier owner hOwner
      ⟨copyCarrier a, ⟨a, rfl⟩⟩
  obtain ⟨b, hb⟩ := f.2
  have hCopy : copyCarrier ((inclusion B (carrier p)).comp b) = copyCarrier a := by
    have hImage : Subtype.val '' f.1 = copyCarrier a := congrArg Subtype.val hf
    rw [← UniformPrivateTemplate.image_copyCarrier_comp small (B.induce (carrier p)) B
      (inclusion B (carrier p)) b]
    change Subtype.val '' copyCarrier b = copyCarrier a
    rw [← hb]
    exact hImage
  have hp : owner ⟨copyCarrier a, ⟨a, rfl⟩⟩ = p := hf ▸
    firstWagonEdgeToOriginal_owner small B carrier owner hOwner hLinear ⟨p, f⟩
  refine ⟨privateChoice_localEdge small B R carrier localCopy hStrong hCover p b,
    hp.symm, privateChoice_localEdge_mem_target small B R carrier localCopy hStrong hCover p b, ?_⟩
  rw [privateChoice_localEdge_carrier, hCopy]

end StructuralRamsey.Girth
