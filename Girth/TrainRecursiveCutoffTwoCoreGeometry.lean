import Girth.TrainRecursiveCutoffTwoPartiteCore

set_option autoImplicit false
set_option Elab.async false

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v w

variable {L : RelLanguage.{u}} {U V W I : Type v}
variable {A : RelStructure L U} {D : RelStructure L W}

private theorem rigid_embeddings_eq_of_sameCopy
    {R : RelStructure L W} (hRigid : ∀ a : Embedding A A, a = Embedding.id A)
    (a b : Embedding A R) (h : SameCopy a b) : a = b := by
  classical
  have hFactor (u : U) : ∃ v : U, a u = b v := by
    have hmem : a u ∈ copyCarrier b := h ▸ ⟨u, rfl⟩
    obtain ⟨v, hv⟩ := hmem
    exact ⟨v, hv.symm⟩
  let c := a.factorThroughRange b hFactor
  apply Embedding.ext
  intro u
  have hSpec : a u = b (c u) := Classical.choose_spec (hFactor u)
  simpa only [hRigid c, RelStructure.Embedding.id_apply] using hSpec

namespace CutoffTwoLiftData

variable (Target : StructuralRamsey.Partite.System L U V)
variable (C : CutoffTwoLiftData A Target.toRelStructure D I)
variable (hPart : C.part = Target.part)

noncomputable abbrev liftedEmbedding (i : I) :
    Embedding Target.toRelStructure (C.system Target hPart).toRelStructure :=
  (C.partiteLift Target hPart i).toEmbedding

variable (hPartOnA : ∀ (a : Embedding A Target.toRelStructure) (u : U), C.part (a u) = u)
variable (hOwner : ∀ (a : Embedding A Target.toRelStructure) (u : U),
  u ∉ C.allowed → C.owner (a u) = a)

include hPartOnA hOwner in
/-- Every physical edge of the lifted core is a literal selected lift
of an original A-embedding, including edges that cross tuple witnesses. -/
theorem all_core_edges_lifted [Finite U]
    (hA : A.Irreducible)
    (hRigid : ∀ a : Embedding A A, a = Embedding.id A)
    (hStrong : ∀ i, AStrong A D (copyCarrier (C.original i)))
    (hCoverage : NonsingletonIrreduciblesExtendTo A D)
    (hTargetVertex : ∀ x : V, ∃ a : Embedding A Target.toRelStructure, x ∈ copyCarrier a)
    (hNonempty : Nonempty I)
    (hTargetEdge : Nonempty (Embedding A Target.toRelStructure))
    (e : Embedding A (C.system Target hPart).toRelStructure) :
    ∃ (i : I) (a : Embedding A Target.toRelStructure), e = (C.liftedEmbedding Target hPart i).comp a := by
  obtain ⟨i, a, hCover⟩ := selectedRelationalLiftUnion_all_irreducibles_covered
    C.original C.lift C.project C.project_lift hStrong hCoverage
    (C.lift_compatible hPartOnA hOwner) C.lift_covers hTargetVertex
    hNonempty hTargetEdge (copyCarrier e) (hA.range_embedding e)
  refine ⟨i, a, rigid_embeddings_eq_of_sameCopy hRigid e ((C.liftedEmbedding Target hPart i).comp a) ?_⟩
  apply sameCopy_of_range_subset
  intro u
  obtain ⟨v, hv⟩ := hCover ⟨u, rfl⟩
  exact ⟨v, hv.symm⟩

private theorem project_mem_original {i : I}
    {a : Embedding A Target.toRelStructure} {z : C.Vertex}
    (hz : z ∈ copyCarrier ((C.liftedEmbedding Target hPart i).comp a)) :
    C.project z ∈ copyCarrier ((C.original i).comp a) := by
  obtain ⟨u, rfl⟩ := hz
  exact ⟨u, rfl⟩

private theorem project_injOn_edge (i : I) (a : Embedding A Target.toRelStructure) :
    Set.InjOn C.project (copyCarrier ((C.liftedEmbedding Target hPart i).comp a)) := by
  rintro _ ⟨u, rfl⟩ _ ⟨v, rfl⟩ huv
  exact congrArg ((C.liftedEmbedding Target hPart i).comp a)
    (((C.original i).comp a).injective huv)

include hPartOnA hOwner in
private theorem lift_edge_eq_of_original_edge_eq (i j : I)
    (a b : Embedding A Target.toRelStructure)
    (h : (C.original i).comp a = (C.original j).comp b) :
    (C.liftedEmbedding Target hPart i).comp a = (C.liftedEmbedding Target hPart j).comp b := by
  apply Embedding.ext
  intro u
  exact congrFun (C.lift_compatible hPartOnA hOwner i j a b h) u

variable
  (hLifted : ∀ e : Embedding A (C.system Target hPart).toRelStructure,
    ∃ (i : I) (a : Embedding A Target.toRelStructure), e = (C.liftedEmbedding Target hPart i).comp a)

include hPartOnA hOwner hLifted in
/-- The original witness is A-linear. Injectivity on lifted edges and
compatibility of repeated edge lifts transport that property. -/
theorem core_aLinear
    (hRigid : ∀ a : Embedding A A, a = Embedding.id A)
    (hLinear : ALinear A D) :
    ALinear A (C.system Target hPart).toRelStructure := by
  intro e f hNe
  obtain ⟨i, a, rfl⟩ := hLifted e
  obtain ⟨j, b, rfl⟩ := hLifted f
  have hOldNe : ¬ SameCopy ((C.original i).comp a) ((C.original j).comp b) := by
    intro hSame
    have hOldEq := rigid_embeddings_eq_of_sameCopy hRigid _ _ hSame
    exact hNe (congrArg copyCarrier
      (C.lift_edge_eq_of_original_edge_eq Target hPart hPartOnA hOwner i j a b hOldEq))
  have hSmall := hLinear _ _ hOldNe
  intro x hx y hy
  apply C.project_injOn_edge Target hPart i a hx.1 hy.1
  exact hSmall
    ⟨C.project_mem_original Target hPart hx.1, C.project_mem_original Target hPart hx.2⟩
    ⟨C.project_mem_original Target hPart hy.1, C.project_mem_original Target hPart hy.2⟩

include hPartOnA hOwner hLifted in
/-- Each selected target lift remains A-strong. Intersecting an edge in two
points puts its whole original inside that selected target. Compatibility
then identifies its edge lift inside that very target. -/
theorem selected_core_aStrong
    (hStrong : ∀ i, AStrong A D (copyCarrier (C.original i))) (i : I) :
    AStrong A (C.system Target hPart).toRelStructure (copyCarrier (C.liftedEmbedding Target hPart i)) := by
  classical
  intro e hInter
  obtain ⟨j, a, rfl⟩ := hLifted e
  have hOldInter :
      ¬ (copyCarrier ((C.original j).comp a) ∩ copyCarrier (C.original i)).Subsingleton := by
    intro hSmall
    apply hInter
    intro x hx y hy
    have hOld (z : C.Vertex) (hz : z ∈ copyCarrier (C.liftedEmbedding Target hPart i)) :
        C.project z ∈ copyCarrier (C.original i) := by
      obtain ⟨v, rfl⟩ := hz
      exact ⟨v, rfl⟩
    apply C.project_injOn_edge Target hPart j a hx.1 hy.1
    exact hSmall
      ⟨C.project_mem_original Target hPart hx.1, hOld x hx.2⟩
      ⟨C.project_mem_original Target hPart hy.1, hOld y hy.2⟩
  have hFactor (u : U) : ∃ v : V, ((C.original j).comp a) u = C.original i v := by
    obtain ⟨v, hv⟩ := hStrong i ((C.original j).comp a) hOldInter ⟨u, rfl⟩
    exact ⟨v, hv.symm⟩
  let b := ((C.original j).comp a).factorThroughRange (C.original i) hFactor
  have hEq : (C.original j).comp a = (C.original i).comp b := by
    apply Embedding.ext
    intro u
    exact Classical.choose_spec (hFactor u)
  rw [C.lift_edge_eq_of_original_edge_eq Target hPart hPartOnA hOwner j i a b hEq]
  rintro _ ⟨u, rfl⟩
  exact ⟨b u, rfl⟩

include hPartOnA hOwner hLifted in
/-- Distinct lifted edges meet only over permitted parts. Outside those
parts, the owner coordinate would force them to be the same edge. -/
theorem core_contacts_allowed
    (hRigid : ∀ a : Embedding A A, a = Embedding.id A)
    (e f : Embedding A (C.system Target hPart).toRelStructure) (hNe : ¬ SameCopy e f)
    {z : C.Vertex} (hz : z ∈ copyCarrier e ∩ copyCarrier f) :
    C.vertexPart z ∈ C.allowed := by
  obtain ⟨i, a, rfl⟩ := hLifted e
  obtain ⟨j, b, rfl⟩ := hLifted f
  obtain ⟨u, hu⟩ := hz.1
  obtain ⟨v, hv⟩ := hz.2
  by_contra hBad
  have huBad : u ∉ C.allowed := by
    intro h
    apply hBad
    rw [← hu]
    change C.vertexPart (C.lift i (a u)) ∈ C.allowed
    rw [C.vertexPart_lift, hPartOnA]
    exact h
  have hOld := C.original_sameCopy_of_forbidden_contact hPartOnA hOwner i j a b u v huBad
    (hu.trans hv.symm)
  exact hNe (congrArg copyCarrier
    (C.lift_edge_eq_of_original_edge_eq Target hPart hPartOnA hOwner i j a b
      (rigid_embeddings_eq_of_sameCopy hRigid _ _ hOld)))

include hPartOnA hOwner in
/-- Extend any colouring of the core to the old witness. Compatibility
makes the colour well-defined on every old A-embedding in a selected lift. -/
theorem core_selected_arrow (κ : Type w) [Nonempty κ]
    (hOldArrow : ∀ χ : Embedding A D → κ,
      ∃ i : I, ∀ a b : Embedding A Target.toRelStructure,
        χ ((C.original i).comp a) = χ ((C.original i).comp b)) :
    ∀ χ : Embedding A (C.system Target hPart).toRelStructure → κ,
      ∃ i : I, ∀ a b : Embedding A Target.toRelStructure,
        χ ((C.liftedEmbedding Target hPart i).comp a) = χ ((C.liftedEmbedding Target hPart i).comp b) := by
  classical
  intro χ
  let oldColour (e : Embedding A D) : κ :=
    if h : ∃ p : I × Embedding A Target.toRelStructure, (C.original p.1).comp p.2 = e then
      χ ((C.liftedEmbedding Target hPart (Classical.choose h).1).comp (Classical.choose h).2)
    else Classical.choice inferInstance
  have hColour (i : I) (a : Embedding A Target.toRelStructure) :
      oldColour ((C.original i).comp a) = χ ((C.liftedEmbedding Target hPart i).comp a) := by
    let h : ∃ p : I × Embedding A Target.toRelStructure,
        (C.original p.1).comp p.2 = (C.original i).comp a := ⟨(i, a), rfl⟩
    unfold oldColour
    rw [dite_eq_left h]
    exact congrArg χ (C.lift_edge_eq_of_original_edge_eq Target hPart hPartOnA hOwner
      (Classical.choose h).1 i (Classical.choose h).2 a (Classical.choose_spec h))
  obtain ⟨i, hi⟩ := hOldArrow oldColour
  exact ⟨i, fun a b => (hColour i a).symm.trans ((hi a b).trans (hColour i b))⟩

end CutoffTwoLiftData

end StructuralRamsey.Girth
