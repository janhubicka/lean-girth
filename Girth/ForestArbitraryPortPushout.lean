import Girth.ForestImage
import Mathlib.Tactic

/-!
# Canonical injective gluing over an arbitrary isomorphism of separators

Two B-copy carriers need not realize their shared A-edge by the same
internal coordinate positions. The appropriate elementary pushout
takes distinct old/new vertex universes and an arbitrary specified
bijection between their chosen port subsets.

The physical vertex set is Old ⊕ (New \ NewPort). Every old vertex
survives, and a new vertex is mapped to its corresponding old port
vertex if it lies in NewPort, or gets a fresh right tag otherwise.

Both sides embed injectively, and their cross-copy equalities are
EXACTLY the prescribed port identifications. This is the geometric
building block for reconstructing a general supported forest by
leaf gluings. It does not construct the global successor Ramsey
reservoir or decide when a proposed port is allowed by A-support.
-/

namespace StructuralRamsey.Girth

universe v

/-- Data for gluing a new B-piece to an old picture along one
specified pair of port subsets, using an arbitrary vertex bijection.
No matching of entire B-coordinate systems is assumed. -/
structure PortGluing (Old New : Type v) where
  oldPort : Set Old
  newPort : Set New
  identify : newPort ≃ oldPort

namespace PortGluing

variable {Old New : Type v}

/-- Keep all old vertices. Only new non-port vertices need private tags. -/
abbrev Vertex (G : PortGluing Old New) : Type v :=
  Old ⊕ {y : New // y ∉ G.newPort}

/-- The entire old picture embeds in the new glued picture. -/
def oldEmbedding (G : PortGluing Old New) :
    Old ↪ G.Vertex where
  toFun := Sum.inl
  inj' := by
    intro x y h
    exact Sum.inl.inj h

/-- The new B-piece embeds by identifying exactly its designated
new port with the old port and keeping all other vertices private. -/
noncomputable def newEmbedding (G : PortGluing Old New) :
    New ↪ G.Vertex := by
  classical
  refine
    { toFun := fun y =>
        if h : y ∈ G.newPort then
          Sum.inl (G.identify ⟨y, h⟩).1
        else
          Sum.inr ⟨y, h⟩
      inj' := ?_ }
  intro x y hxy
  by_cases hx : x ∈ G.newPort
  · by_cases hy : y ∈ G.newPort
    · have heq :
          (G.identify ⟨x, hx⟩).1 =
            (G.identify ⟨y, hy⟩).1 := by
        simpa [hx, hy] using hxy
      have hp :
          G.identify ⟨x, hx⟩ = G.identify ⟨y, hy⟩ :=
        Subtype.ext heq
      exact congrArg Subtype.val (G.identify.injective hp)
    · have hFalse : False := by
        simpa [hx, hy] using hxy
      exact hFalse.elim
  · by_cases hy : y ∈ G.newPort
    · have hFalse : False := by
        simpa [hx, hy] using hxy
      exact hFalse.elim
    · have hp :
          (⟨x, hx⟩ : {z : New // z ∉ G.newPort}) =
            (⟨y, hy⟩ : {z : New // z ∉ G.newPort}) := by
        simpa [hx, hy] using hxy
      exact congrArg Subtype.val hp

/-- Equality across the two embedded pictures is EXACTLY the
prescribed identification of one new-port vertex with its old mate. -/
theorem oldEmbedding_eq_newEmbedding_iff
    (G : PortGluing Old New) (x : Old) (y : New) :
    G.oldEmbedding x = G.newEmbedding y ↔
      ∃ h : y ∈ G.newPort, x = (G.identify ⟨y, h⟩).1 := by
  classical
  constructor
  · intro h
    by_cases hy : y ∈ G.newPort
    · refine ⟨hy, ?_⟩
      have heq :
          Sum.inl x = Sum.inl (G.identify ⟨y, hy⟩).1 := by
        simpa [oldEmbedding, newEmbedding, hy] using h
      exact Sum.inl.inj heq
    · have hFalse : False := by
        simpa [oldEmbedding, newEmbedding, hy] using h
      exact hFalse.elim
  · rintro ⟨hy, hEq⟩
    change Sum.inl x =
      (if h : y ∈ G.newPort then
        Sum.inl (G.identify ⟨y, h⟩).1
       else Sum.inr ⟨y, h⟩)
    rw [dif_pos hy, hEq]

/-- The two embeddings coincide at corresponding chosen port
vertices, with no additional quotient identifications. -/
theorem agree_on_port
    (G : PortGluing Old New) {y : New}
    (hy : y ∈ G.newPort) :
    G.oldEmbedding (G.identify ⟨y, hy⟩).1 =
      G.newEmbedding y :=
  (G.oldEmbedding_eq_newEmbedding_iff _ _).mpr ⟨hy, rfl⟩

/-- Every physical overlap between an old and a new subset lies
inside the OLD port. In particular an unintended extra intersection
can never arise during this gluing. -/
theorem old_new_image_inter_subset_port
    (G : PortGluing Old New) (A : Set Old) (B : Set New) :
    G.oldEmbedding '' A ∩ G.newEmbedding '' B ⊆
      G.oldEmbedding '' G.oldPort := by
  rintro z ⟨⟨x, _, hx⟩, ⟨y, _, hy⟩⟩
  have hCross : G.oldEmbedding x = G.newEmbedding y :=
    hx.trans hy.symm
  obtain ⟨hyPort, hEq⟩ :=
    (G.oldEmbedding_eq_newEmbedding_iff x y).mp hCross
  have hxPort : x ∈ G.oldPort := by
    rw [hEq]
    exact (G.identify ⟨y, hyPort⟩).2
  exact ⟨x, hxPort, hx⟩

/-- Every old port vertex occurs in the new side as the image of
the corresponding new port vertex. -/
theorem oldPort_image_subset_newPort_image
    (G : PortGluing Old New) :
    G.oldEmbedding '' G.oldPort ⊆
      G.newEmbedding '' G.newPort := by
  rintro z ⟨x, hx, hxz⟩
  let y : G.newPort := G.identify.symm ⟨x, hx⟩
  refine ⟨y.1, y.2, ?_⟩
  calc
    G.newEmbedding y.1 =
        G.oldEmbedding (G.identify y).1 :=
      (G.agree_on_port y.2).symm
    _ = G.oldEmbedding x := by
      change G.oldEmbedding (G.identify (G.identify.symm ⟨x, hx⟩)).1 =
        G.oldEmbedding x
      rw [G.identify.apply_symm_apply]
    _ = z := hxz

/-- The physical common vertices of the two ENTIRE pictures are
exactly the prescribed old port image. -/
theorem old_new_full_images_inter
    (G : PortGluing Old New) :
    G.oldEmbedding '' (Set.univ : Set Old) ∩
      G.newEmbedding '' (Set.univ : Set New) =
        G.oldEmbedding '' G.oldPort := by
  apply Set.Subset.antisymm
  · exact G.old_new_image_inter_subset_port _ _
  · intro z hz
    have hzOld : z ∈ G.oldEmbedding '' (Set.univ : Set Old) := by
      obtain ⟨x, _, hxz⟩ := hz
      exact ⟨x, Set.mem_univ x, hxz⟩
    have hzNew : z ∈ G.newEmbedding '' (Set.univ : Set New) := by
      have hIn : z ∈ G.newEmbedding '' G.newPort :=
        G.oldPort_image_subset_newPort_image hz
      obtain ⟨y, _, hyz⟩ := hIn
      exact ⟨y, Set.mem_univ y, hyz⟩
    exact ⟨hzOld, hzNew⟩

end PortGluing

end StructuralRamsey.Girth
