import Girth.ContactActualStrip
import Girth.ContactAllLevelPreservation
import Girth.ContactPictureIncrement

/-! Actual picture step from embeddings of an active strip.
The lifted standards are strongly induced without requiring the
core to have the pairwise mixed-forest property at cutoff one.
This is important for the first forest-increment step. -/

namespace StructuralRamsey.Girth
universe v
variable {V E I U F J X B W G K : Type v}

namespace ContactTrainStrip
variable {m : ℕ} {L : ContactHypergraphData V E I} {S : ContactTrainData E m}
    {D : ContactHypergraphData U F J} {T : ContactTrainData F m}
    (A : ContactTrainStrip D L T S)

/-- Only the ordinary strong inducedness of the designated core
copies is needed here. The bridge part of G1 is unnecessary. -/
theorem standardStrong_of_core (hs : A.StripStrong)
    (hstrong : ∀ i e, (D.edgeCarrier e ∩ D.copyCarrier i).Nontrivial →
      e ∈ D.copyEdges i) :
    A.bottomPicture.toPictureData.StandardStrong := by
  let P := A.bottomPicture.toPictureData
  have hc := A.bottomPicture.core_strong (A.stripStrong_bottom hs)
  intro i f hn
  obtain ⟨x,hx,y,hy,hxy⟩ := hn
  have coreCase : f ∈ Set.range P.core.edge → f ∈ Set.range (P.std i).edge := by
    rintro ⟨e,rfl⟩
    obtain ⟨a,rfl⟩ := P.core.edge_vertex_range hx.1
    obtain ⟨b,rfl⟩ := P.core.edge_vertex_range hy.1
    have hab : a ≠ b := fun he => hxy (congrArg P.core.vertex he)
    exact (P.std_core_edge i e).mpr (hstrong i e
      ⟨a,⟨P.core.edge_vertex_reflect e a hx.1,(P.std_core_vertex i a).mp hx.2⟩,
       b,⟨P.core.edge_vertex_reflect e b hy.1,(P.std_core_vertex i b).mp hy.2⟩,hab⟩)
  rcases P.edge_cover f with h | ⟨j,e,rfl⟩
  · exact coreCase h
  · by_cases hij : i = j
    · subst j
      exact ⟨e,rfl⟩
    · apply coreCase
      exact hc _ ⟨x,⟨hx.1,P.shared_vertex i j hij x hx.2
        ((P.std j).edge_vertex_range hx.1)⟩,
        y,⟨hy.1,P.shared_vertex i j hij y hy.2
        ((P.std j).edge_vertex_range hy.1)⟩,hxy⟩

/-- The actual standard train embedding, in all cuts at once. -/
noncomputable def standardEmbedding (hs : A.StripStrong)
    (hstrong : ∀ i e, (D.edgeCarrier e ∩ D.copyCarrier i).Nontrivial →
      e ∈ D.copyEdges i) (i : J) :
    ContactTrainEmbedding L S A.outputHypergraph A.outputTrain where
  vertex := A.stdV i
  edge := A.stdE i
  carrier_eq := fun e => A.output_carrier_std i (Sum.inr e)
  rel_iff := fun μ e f => A.outputTrain_std_rel μ i e f
  strong := by
    intro e he
    have hh : (A.bottomPicture.output.edgeCarrier e ∩ Set.range (A.stdV i)).Nontrivial := by
      rw [A.bottomPicture_output_eq]
      exact he
    exact A.standardStrong_of_core hs hstrong i e hh

/-- The actual core train embedding. -/
noncomputable def coreEmbedding (hs : A.StripStrong) :
    ContactTrainEmbedding D T A.outputHypergraph A.outputTrain where
  vertex := A.coreV
  edge := A.coreE
  carrier_eq := A.output_carrier_core_edge
  rel_iff := A.outputTrain_core_rel
  strong := by
    intro e he
    have hh : (A.bottomPicture.output.edgeCarrier e ∩ Set.range A.coreV).Nontrivial := by
      rw [A.bottomPicture_output_eq]
      exact he
    exact A.bottomPicture.core_strong (A.stripStrong_bottom hs) e hh

/-- Lift every old designated target embedding into each standard.
The selected labels are exactly the product used by the actual
tagged picture, with its existing copy-carrier and copy-edge maps. -/
noncomputable def liftedFamily {H : ContactHypergraphData W G K}
    {R : ContactTrainData G m} (N : ContactDesignatedEmbeddings H R L S)
    (hs : A.StripStrong)
    (hstrong : ∀ i e, (D.edgeCarrier e ∩ D.copyCarrier i).Nontrivial →
      e ∈ D.copyEdges i) :
    ContactDesignatedEmbeddings H R A.outputHypergraph A.outputTrain where
  emb := fun p => (N.emb p.2).comp (A.standardEmbedding hs hstrong p.1)
  vertex_eq := by
    rintro ⟨i,j⟩
    change A.stdV i '' L.copyCarrier j =
      Set.range ((N.emb j).vertex.trans (A.stdV i))
    rw [N.vertex_eq]
    ext x
    constructor
    · rintro ⟨y,⟨z,rfl⟩,he⟩
      exact ⟨z,he⟩
    · rintro ⟨z,he⟩
      exact ⟨(N.emb j).vertex z,⟨z,rfl⟩,he⟩
  edge_eq := by
    rintro ⟨i,j⟩
    change A.stdE i '' L.copyEdges j =
      Set.range ((N.emb j).edge.trans (A.stdE i))
    rw [N.edge_eq]
    ext x
    constructor
    · rintro ⟨y,⟨z,rfl⟩,he⟩
      exact ⟨z,he⟩
    · rintro ⟨z,he⟩
      exact ⟨(N.emb j).edge z,⟨z,rfl⟩,he⟩

end ContactTrainStrip

namespace ContactDesignatedEmbeddings
variable {m : ℕ} {L : ContactHypergraphData V E I} {S : ContactTrainData E m}
    {base : B → Set X} {P : ContactBaseProjection L base} {b : B}
    {D : ContactHypergraphData U F J} {T : ContactTrainData F m}
    (M : ContactDesignatedEmbeddings (P.stripHypergraph b) (P.stripTrain S b) D T)

theorem copy_strong (i : J) (e : F)
    (h : (D.edgeCarrier e ∩ D.copyCarrier i).Nontrivial) :
    e ∈ D.copyEdges i := by
  rw [M.vertex_eq] at h
  rw [M.edge_eq]
  exact (M.emb i).strong e h

theorem copy_edge_subset (i : J) (e : F) (he : e ∈ D.copyEdges i) :
    D.edgeCarrier e ⊆ D.copyCarrier i := by
  rw [M.edge_eq] at he
  obtain ⟨f,rfl⟩ := he
  rw [M.vertex_eq]
  exact (M.emb i).vertex_range_of_edge f

theorem copy_covered (i : J) (u : U) (hu : u ∈ D.copyCarrier i) :
    ∃ e, e ∈ D.copyEdges i ∧ u ∈ D.edgeCarrier e := by
  rw [M.vertex_eq] at hu
  obtain ⟨x,rfl⟩ := hu
  obtain ⟨f,hf⟩ := P.strip_covered b x
  exact ⟨(M.emb i).edge f,by rw [M.edge_eq]; exact ⟨f,rfl⟩,
    ((M.emb i).mem_edge_image f x).mpr hf⟩

/-- The one-step colouring assertion uses the exact shared edge
map of a chosen core copy. No colouring theorem about the output
picture is an extra hypothesis. -/
theorem strip_step_arrow {Color : Type v}
    (hne : Nonempty (P.StripEdge b)) (h : M.Arrow Color)
    (χ : (M.stripGluing hne).Edge → Color) :
    ∃ i : J, ∃ c : Color, ∀ e : P.StripEdge b,
      χ ((M.stripGluing hne).stdE i e.val) = c := by
  let A := M.stripGluing hne
  obtain ⟨i,c,hi⟩ := h (fun f => χ (A.coreE f))
  refine ⟨i,c,?_⟩
  intro e
  have hg : A.edgeGlue i e.val = some ((M.emb i).edge e) :=
    (M.edgePartial_iff i e.val _).mpr ⟨e.property,rfl⟩
  have he := A.shared_edge_eq i e.val ((M.emb i).edge e) hg
  change χ (A.stdE i e.val) = c
  rw [he]
  exact hi e

end ContactDesignatedEmbeddings
end StructuralRamsey.Girth
