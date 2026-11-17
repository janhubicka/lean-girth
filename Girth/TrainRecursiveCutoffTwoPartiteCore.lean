import Girth.TrainRecursiveCutoffTwoTokens
import PartiteConstruction.Partite.Induced

set_option autoImplicit false
set_option Elab.async false

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v

variable {L : RelLanguage.{u}} {U V W I : Type v}
variable {A : RelStructure L U} {D : RelStructure L W}

namespace CutoffTwoLiftData

variable (Target : StructuralRamsey.Partite.System L U V)
variable (C : CutoffTwoLiftData A Target.toRelStructure D I)

noncomputable def system (hPart : C.part = Target.part) :
    StructuralRamsey.Partite.System L U C.Vertex where
  toRelStructure := selectedRelationalLiftUnion Target.toRelStructure C.lift
  part := C.vertexPart
  transversal := by
    intro R t ht k l hkl
    obtain ⟨i, s, hs, rfl⟩ := ht
    change C.vertexPart (C.lift i (s k)) = C.vertexPart (C.lift i (s l)) at hkl
    rw [C.vertexPart_lift, C.vertexPart_lift, hPart] at hkl
    exact congrArg (C.lift i) (Target.transversal R s hs k l hkl)

noncomputable def partiteLift (hPart : C.part = Target.part) (i : I) :
    StructuralRamsey.Partite.Embedding Target (C.system Target hPart) where
  toEmbedding := selectedRelationalLiftUnionEmbedding C.original C.lift
    C.project C.project_lift i
  map_part := fun x => (C.vertexPart_lift i x).trans (congrFun hPart x)

/-- The selected lifted union has a homomorphism-embedding to the fine
part base. Each irreducible is covered by a lifted A-copy, and on that copy
the part map is the identity in the original target coordinates. -/
theorem system_isPartiteOver
    (hPart : C.part = Target.part) (hTarget : Target.IsPartiteOver A)
    (hA : A.Irreducible)
    (hRigid : ∀ a : Embedding A A, a = Embedding.id A)
    (hOwner : ∀ (a : Embedding A Target.toRelStructure) (u : U),
      u ∉ C.allowed → C.owner (a u) = a)
    (hStrong : ∀ i, AStrong A D (copyCarrier (C.original i)))
    (hCoverage : NonsingletonIrreduciblesExtendTo A D)
    (hTargetVertex : ∀ x : V,
      ∃ a : Embedding A Target.toRelStructure, x ∈ copyCarrier a)
    (hNonempty : Nonempty I)
    (hTargetEdge : Nonempty (Embedding A Target.toRelStructure)) :
    (C.system Target hPart).IsPartiteOver A := by
  have hPartOnA (a : Embedding A Target.toRelStructure) (u : U) :
      C.part (a u) = u := by
    obtain ⟨b, hb⟩ := hTarget.after_irreducible_embedding hA a
    rw [hRigid b] at hb
    exact (congrFun hPart (a u)).trans (hb u).symm
  constructor
  · intro R t ht
    obtain ⟨i, s, hs, rfl⟩ := ht
    have hEq :
        ((C.system Target hPart).part ∘ ((C.lift i : V → C.Vertex) ∘ s)) =
          Target.part ∘ s := by
      funext k
      exact (C.partiteLift Target hPart i).map_part (s k)
    rw [hEq]
    exact hTarget.map_rel hs
  · intro S hS
    obtain ⟨i, a, hCover⟩ := selectedRelationalLiftUnion_all_irreducibles_covered
      C.original C.lift C.project C.project_lift hStrong hCoverage
      (C.lift_compatible hPartOnA hOwner) C.lift_covers hTargetVertex
      hNonempty hTargetEdge S hS
    let E := (C.system Target hPart).toRelStructure
    let f := (C.partiteLift Target hPart i).toEmbedding.comp a
    have hFactor (x : S) : (inclusion E S) x ∈ copyCarrier f := hCover x.2
    have hFactor' (x : S) : ∃ u : U, inclusion E S x = f u := by
      obtain ⟨u, hu⟩ := hFactor x
      exact ⟨u, hu.symm⟩
    let e := (inclusion E S).factorThroughRange f hFactor'
    refine ⟨e, fun x => ?_⟩
    have hSpec : x.1 = f (e x) := Classical.choose_spec (hFactor' x)
    change e x = C.vertexPart x.1
    rw [hSpec]
    exact (hPartOnA a (e x)).symm

end CutoffTwoLiftData

end StructuralRamsey.Girth
