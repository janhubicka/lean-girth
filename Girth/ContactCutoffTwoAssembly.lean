import Girth.ContactCutoffTwoInput

/-! Finish cutoff two from a Ramsey witness for the actual
constructed shorter train. The selected ambient family is obtained
by filling and then applying the concrete copy-restriction data.
The vector-colour proof uses exactly the resulting copy labels. -/

namespace StructuralRamsey.Girth
universe v
variable {V E I X F J C U G K : Type v}

namespace ContactCutoffTwoInput
variable {m : ℕ} {D : ContactHypergraphData V E I}
    {T : ContactTrainData E (m+1)} {L : ContactHypergraphData X F J}
    (A : ContactCutoffTwoInput D T L C)
    {H : ContactHypergraphData U G K} {S : ContactTrainData G m}
    (N : ContactDesignatedEmbeddings A.source A.sourceTrain H S)
    (B : ContactFilling H L)
    (hplace : ∀ j e x, B.place ((N.emb j).edge e) x =
      (N.emb j).vertex (A.fill.place e x))

noncomputable def filledFamily :
    ContactDesignatedEmbeddings A.filled A.filledTrain B.output (B.fillTrain S) :=
  N.fill A.fill B hplace

noncomputable def resultHypergraph : ContactHypergraphData U (G × F) (K × C) :=
  A.selection.selected (A.filledFamily N B hplace)

/-- The actual chosen family consists of embeddings of the
original train, not merely strongly induced vertex sets. -/
noncomputable def resultFamily :
    ContactDesignatedEmbeddings D T (A.resultHypergraph N B hplace) (B.fillTrain S) where
  emb := fun p =>
    let M := (A.original p.2).comp ((A.filledFamily N B hplace).emb p.1)
    { vertex := M.vertex
      edge := M.edge
      carrier_eq := M.carrier_eq
      rel_iff := M.rel_iff
      strong := M.strong }
  vertex_eq := by
    rintro ⟨j,c⟩
    change (N.emb j).vertex '' Set.range (A.original c).vertex =
      Set.range ((A.original c).vertex.trans (N.emb j).vertex)
    ext x
    constructor
    · rintro ⟨y,⟨z,rfl⟩,he⟩
      exact ⟨z,he⟩
    · rintro ⟨z,he⟩
      exact ⟨(A.original c).vertex z,⟨z,rfl⟩,he⟩
  edge_eq := by
    rintro ⟨j,c⟩
    let M := (A.filledFamily N B hplace).emb j
    change M.edge '' Set.range (A.original c).edge =
      Set.range ((A.original c).edge.trans M.edge)
    ext x
    constructor
    · rintro ⟨y,⟨z,rfl⟩,he⟩
      exact ⟨z,he⟩
    · rintro ⟨z,he⟩
      exact ⟨(A.original c).edge z,⟨z,rfl⟩,he⟩

/-- The inherited positive bounds follow first by substitution
on the shorter witness, then by the actual selected-copy
restriction on each positive proper cut. -/
theorem result_positiveBounds (q : Fin (m+1) → ℕ)
    (hN : H.SystemBounds S q)
    (hNonempty : ∀ e, (H.edgeCarrier e).Nonempty)
    (hL : ∀ e f : F, e ≠ f → (L.edgeCarrier e ∩ L.edgeCarrier f).Subsingleton) :
    (A.resultHypergraph N B hplace).PositiveBounds (B.fillTrain S) (Fin.cases 0 q) :=
  A.selection.preserves_positiveBounds (A.filledFamily N B hplace) (Fin.cases 0 q)
    (B.preserves_positiveBounds S q hNonempty hL hN)

/-- The selected hypergraph is literally the filled ambient
hypergraph on vertices and edges; changing designated labels
does not affect the parameters. -/
theorem result_first_parameter (allowed : Set U)
    (hL : ∀ e (a b : F), a ≠ b →
      B.place e '' (L.edgeCarrier a ∩ L.edgeCarrier b) ⊆ allowed) :
    (A.resultHypergraph N B hplace).Parameter (B.fillTrain S)
      0 (Fin.succ (0 : Fin (m+1))) allowed :=
  B.first_parameter S allowed hL

theorem result_inherited_parameter (μ ν : Fin (m+1)) (allowed : Set U)
    (h : H.Parameter S μ ν allowed) :
    (A.resultHypergraph N B hplace).Parameter (B.fillTrain S) μ.succ ν.succ allowed :=
  B.inherited_parameter S μ ν allowed h

/-- The word-base and the shorter-train Ramsey arrow yield the
desired arrow for the constructed chosen family. The witnesses
are exactly the pair (shorter copy, template line). -/
theorem result_arrow {Color : Type v}
    (hN : N.Arrow (F → Color))
    (hline : ∀ ρ : F → Color, ∃ c : C, ∃ a : Color,
      ∀ e : E, ρ ((A.line c).edge e) = a) :
    (A.resultFamily N B hplace).Arrow Color := by
  intro χ
  obtain ⟨j,ρ,hj⟩ := hN (fun e f => χ (e,f))
  obtain ⟨c,a,ha⟩ := hline ρ
  refine ⟨(j,c),a,?_⟩
  intro e
  change χ ((N.emb j).edge (c,T.parent (0 : Fin (m+1)).succ e),
      (A.line c).edge e) = a
  exact (congrFun (hj (c,T.parent (0 : Fin (m+1)).succ e)) ((A.line c).edge e)).trans (ha e)

theorem result_linear
    (hN : ∀ e f : G, e ≠ f → (H.edgeCarrier e ∩ H.edgeCarrier f).Subsingleton)
    (hL : ∀ e f : F, e ≠ f → (L.edgeCarrier e ∩ L.edgeCarrier f).Subsingleton) :
    ∀ e f : G × F, e ≠ f →
      ((A.resultHypergraph N B hplace).edgeCarrier e ∩
        (A.resultHypergraph N B hplace).edgeCarrier f).Subsingleton :=
  B.output_linear hN hL

/-- The cutoff-two conclusion at the actual constructed output.
All hypotheses concern the shorter input witness and the
word-base template. In particular neither the selected arrow
nor the positive system-girth bounds are assumed. -/
theorem cutoffTwo_of_shorter {Color : Type v}
    (q : Fin (m+1) → ℕ)
    (hN : H.SystemBounds S q)
    (hNonempty : ∀ e, (H.edgeCarrier e).Nonempty)
    (hLinear : ∀ e f : F, e ≠ f → (L.edgeCarrier e ∩ L.edgeCarrier f).Subsingleton)
    (hArrow : N.Arrow (F → Color))
    (hline : ∀ ρ : F → Color, ∃ c : C, ∃ a : Color,
      ∀ e : E, ρ ((A.line c).edge e) = a) :
    (A.resultHypergraph N B hplace).PositiveBounds (B.fillTrain S) (Fin.cases 0 q) ∧
      (A.resultFamily N B hplace).Arrow Color :=
  ⟨A.result_positiveBounds N B hplace q hN hNonempty hLinear,
    A.result_arrow N B hplace hArrow hline⟩

end ContactCutoffTwoInput
end StructuralRamsey.Girth
