import Girth.TrainFinePartiteOrderProjection

set_option autoImplicit false
set_option Elab.async false

namespace StructuralRamsey.Partite

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}} {U P X Y I : Type v}

/-- A relation-preserving projection is preserved by the free picture
attachment. Each tuple comes from the core or one attached copy. -/
theorem Attachment.isHomomorphism_of_partProjections
    (C : System L P X) (S : Set X) (K : System L P Y)
    (f : I → Embedding (C.induce S) K) (D : RelStructure L P)
    (hOld : C.toRelStructure.IsHomomorphism D C.part)
    (hCore : K.toRelStructure.IsHomomorphism D K.part) :
    (attach C S K f).toRelStructure.IsHomomorphism D (attach C S K f).part := by
  intro r z hz
  rcases hz with ⟨w, hw, rfl⟩ | ⟨i, w, hw, rfl⟩
  · exact hCore r w hw
  · have hPart : (attach C S K f).part ∘
        (RelStructure.Attachment.copyMap C.toRelStructure S K.toRelStructure
          (fun i => (f i).toEmbedding) i ∘ w) = C.part ∘ w := by
      funext j
      exact part_copyMap C S K f i (w j)
    rw [hPart]
    exact hOld r w hw

/-- Relabelling from the fine parts of the active edge gives a
homomorphism into the old base. -/
theorem System.isHomomorphism_relabel_of_partProjection
    (K : System L U Y) (A : RelStructure L U) (D : RelStructure L P)
    (e : RelStructure.Embedding A D)
    (hFine : K.toRelStructure.IsHomomorphism A K.part) :
    (K.relabel e.toFunctionEmbedding).toRelStructure.IsHomomorphism D
      (K.relabel e.toFunctionEmbedding).part := by
  intro r z hz
  exact (e.map_rel_iff r (K.part ∘ z)).mpr (hFine r z hz)

/-- For a fine-coloured edge reduct, each tuple covered by an actual
edge projects to a relation of the edge type. -/
theorem System.isHomomorphism_of_edgeCovered
    (K : System L U Y) (A : RelStructure L U)
    (hFine : ∀ (a : RelStructure.Embedding A K.toRelStructure) u, K.part (a u) = u)
    (hCovered : ∀ r z, K.rel r z →
      ∃ a : RelStructure.Embedding A K.toRelStructure, Set.range z ⊆ Set.range a) :
    K.toRelStructure.IsHomomorphism A K.part := by
  classical
  intro r z hz
  obtain ⟨a, ha⟩ := hCovered r z hz
  have hLift (j : Fin (L.arity r)) : ∃ u : U, a u = z j := ha ⟨j, rfl⟩
  choose y hy using hLift
  have hTuple : a ∘ y = z := funext hy
  have hParts : K.part ∘ z = y := by
    funext j
    change K.part (z j) = y j
    rw [← hy j, hFine]
  rw [hParts]
  exact (a.map_rel_iff r y).mp (hTuple.symm ▸ hz)

end StructuralRamsey.Partite

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}} {U Y : Type v}

/-- Restrict a picture projection to the true active support and read
the coordinates in the processed copy of the edge type. -/
theorem activeFine_isHomomorphism_of_partProjection
    {P : Type v} (A : RelStructure L U) (D : RelStructure L P)
    (C : StructuralRamsey.Partite.System L P Y) (e : RelStructure.Embedding A D)
    (hProject : C.toRelStructure.IsHomomorphism D C.part) :
    let H := actualActiveSubsystemPartite A C e.toFunctionEmbedding
    H.toRelStructure.IsHomomorphism A H.part := by
  let H := actualActiveSubsystemPartite A C e.toFunctionEmbedding
  change H.toRelStructure.IsHomomorphism A H.part
  intro r z hz
  apply (e.map_rel_iff r (H.part ∘ z)).mp
  have hParts : e ∘ (H.part ∘ z) = C.part ∘ (Subtype.val ∘ z) := by
    funext j
    exact activeSourcePart_spec A C e.toFunctionEmbedding (z j)
  rw [hParts]
  exact hProject r (Subtype.val ∘ z) hz

/-- Combine the hypergraph relation projection with the independent
forward comparison invariant on the fine parts. -/
theorem partProjection_of_reduct_and_order
    (A : RelStructure L U) [LinearOrder U]
    (K : StructuralRamsey.Partite.System L.withOrder U Y)
    (hReduct : ∀ (r : L.Symbol) (z : Fin (L.arity r) → Y),
      K.rel (.inl r) z → A.rel r (K.part ∘ z))
    (hOrder : PartiteOrderCompatible K) :
    K.toRelStructure.IsHomomorphism A.ordered K.part := by
  intro r z hz
  cases r with
  | inl r => exact hReduct r z hz
  | inr r =>
      cases r
      exact hOrder z hz

end StructuralRamsey.Girth
