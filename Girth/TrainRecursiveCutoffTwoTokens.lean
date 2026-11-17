import Girth.TrainRecursiveSelectedLiftCoverage

set_option autoImplicit false
set_option Elab.async false

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v

variable {L : RelLanguage.{u}} {U V W I : Type v}
variable {A : RelStructure L U} {B : RelStructure L V} {D : RelStructure L W}

/-- The choice is unique at vertices in forbidden parts. At any other vertex
the chosen edge is irrelevant to the lift. -/
noncomputable def cutoffTwoOwner
    (hVertex : ∀ x : V, ∃ a : Embedding A B, x ∈ copyCarrier a) :
    V → Embedding A B :=
  fun x => Classical.choose (hVertex x)

theorem cutoffTwoOwner_eq_of_forbidden
    (part : V → U) (allowed : Set U)
    (hVertex : ∀ x : V, ∃ a : Embedding A B, x ∈ copyCarrier a)
    (hRigid : ∀ a b : Embedding A B, SameCopy a b → a = b)
    (hContacts : ∀ a b : Embedding A B, ¬ SameCopy a b →
      ∀ x ∈ copyCarrier a ∩ copyCarrier b, part x ∈ allowed)
    (a : Embedding A B) (u : U) (hForbidden : part (a u) ∉ allowed) :
    cutoffTwoOwner hVertex (a u) = a := by
  apply hRigid
  by_contra hne
  exact hForbidden (hContacts _ _ hne _ ⟨Classical.choose_spec (hVertex (a u)), ⟨u, rfl⟩⟩)

/-- Keep the original point and its fine part. Outside the allowed parts,
also record the unique original A-edge containing the point in the target. -/
structure CutoffTwoLiftData
    (A : RelStructure L U) (B : RelStructure L V) (D : RelStructure L W)
    (I : Type v) where
  original : I → Embedding B D
  part : V → U
  allowed : Set U
  owner : V → Embedding A B

namespace CutoffTwoLiftData

variable (C : CutoffTwoLiftData A B D I)

noncomputable def point (i : I) (x : V) : W × U × Option (Set W) := by
  classical
  exact (C.original i x, C.part x,
    if C.part x ∈ C.allowed then none else
      some (copyCarrier ((C.original i).comp (C.owner x))))

/-- Keep only points that occur in the actual selected lifts. -/
abbrev Vertex : Type v :=
  Set.range (fun p : I × V => C.point p.1 p.2)

noncomputable def lift (i : I) : V ↪ C.Vertex where
  toFun x := ⟨C.point i x, ⟨(i, x), rfl⟩⟩
  inj' := by
    intro x y hxy
    exact (C.original i).injective (congrArg (fun z : C.Vertex => z.1.1) hxy)

def project (z : C.Vertex) : W := z.1.1
def vertexPart (z : C.Vertex) : U := z.1.2.1

@[simp] theorem project_lift (i : I) (x : V) :
    C.project (C.lift i x) = C.original i x := rfl

@[simp] theorem vertexPart_lift (i : I) (x : V) :
    C.vertexPart (C.lift i x) = C.part x := rfl

theorem lift_covers (z : C.Vertex) : ∃ i : I, z ∈ Set.range (C.lift i) := by
  obtain ⟨⟨i, x⟩, hx⟩ := z.2
  exact ⟨i, x, Subtype.ext hx⟩

/-- The copy selected over an original edge is independent of the selected
target that contained the edge. This preserves the original Ramsey arrow. -/
theorem lift_compatible
    (hPart : ∀ (a : Embedding A B) (u : U), C.part (a u) = u)
    (hOwner : ∀ (a : Embedding A B) (u : U), u ∉ C.allowed → C.owner (a u) = a)
    (i j : I) (a b : Embedding A B)
    (hab : (C.original i).comp a = (C.original j).comp b) :
    (C.lift i : V → C.Vertex) ∘ a = (C.lift j : V → C.Vertex) ∘ b := by
  classical
  funext u
  apply Subtype.ext
  change C.point i (a u) = C.point j (b u)
  have hOld : C.original i (a u) = C.original j (b u) :=
    congrArg (fun f : Embedding A D => f u) hab
  by_cases hu : u ∈ C.allowed
  · simp [point, hPart a u, hPart b u, hu, hOld]
  · simp [point, hPart a u, hPart b u, hu, hOwner a u hu, hOwner b u hu, hOld, hab]

/-- If two tagged edge lifts meet at a forbidden point, the owner coordinate
forces their old physical edges to coincide. -/
theorem original_sameCopy_of_forbidden_contact
    (hPart : ∀ (a : Embedding A B) (u : U), C.part (a u) = u)
    (hOwner : ∀ (a : Embedding A B) (u : U), u ∉ C.allowed → C.owner (a u) = a)
    (i j : I) (a b : Embedding A B) (u v : U) (hu : u ∉ C.allowed)
    (hContact : C.lift i (a u) = C.lift j (b v)) :
    SameCopy ((C.original i).comp a) ((C.original j).comp b) := by
  classical
  have huv : u = v := by
    simpa only [vertexPart_lift, hPart] using congrArg C.vertexPart hContact
  subst v
  have hTag := congrArg (fun z : C.Vertex => z.1.2.2) hContact
  change (C.point i (a u)).2.2 = (C.point j (b u)).2.2 at hTag
  simpa [point, hPart, hu, hOwner, SameCopy] using hTag

end CutoffTwoLiftData

end StructuralRamsey.Girth
