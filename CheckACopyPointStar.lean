import Girth.ACopyPointStar

open StructuralRamsey.Girth StructuralRamsey.Girth.ACopyPointStar

namespace ACopyPointStarRegression

/-- Two injective two-point charts with a cross-coordinate common point. -/
def chart (e : Bool) : Bool ↪ ℕ where
  toFun a := match e, a with
    | false, false => 0
    | false, true => 1
    | true, false => 1
    | true, true => 2
  inj' := by
    cases e <;> intro a b h <;> cases a <;> cases b <;> simp_all

def chain : CoherentOverlap Bool Bool := CoherentOverlap.ofCharts chart

def edge : CoherentOverlap Unit Bool where
  Rel _ _ a b := a = b
  diagonal _ _ _ := Iff.rfl
  reverse h := h.symm
  compose h₁ h₂ := h₁.trans h₂

/-- Source false shares the core's first edge; source true shares its second.
Each source also has a second edge reaching a private point. -/
def data : Data Bool Bool (fun _ => Bool) (fun _ => Unit) Bool where
  core := chain
  source _ := chain
  shared _ := edge
  toCore i := {
    node := ⟨fun _ => i, fun _ _ _ => Subsingleton.elim _ _⟩
    rel_iff := fun _ _ a b => chain.diagonal i a b }
  toSource _ := {
    node := ⟨fun _ => false, fun _ _ _ => Subsingleton.elim _ _⟩
    rel_iff := fun _ _ a b => chain.diagonal false a b }

/-- A nonshared source-node occurrence reaches another source through two
shared representatives and the core's cross-coordinate overlap. -/
theorem transitive_cross_coordinate :
    data.sourcePoint false true false = data.sourcePoint true false false := by
  apply (data.distinct_sourcePoint_eq_iff false true (by decide) true false false false).mpr
  exact ⟨(), (), true, false, rfl, rfl, rfl⟩

/-- The preceding equality lies in the actual generated relation. -/
theorem transitive_generated :
    data.Generated (.inr ⟨false, (true, false)⟩) (.inr ⟨true, (false, false)⟩) :=
  Quot.eqvGen_exact transitive_cross_coordinate

theorem no_core_fold : data.corePoint false false ≠ data.corePoint true true := by
  intro h
  have hrel := (data.corePoint_eq_iff false true false true).mp h
  change (0 : ℕ) = 2 at hrel
  omega

theorem no_source_fold : data.sourcePoint false false false ≠
    data.sourcePoint false true true := by
  intro h
  have hrel := (data.sourcePoint_eq_iff false false true false true).mp h
  change (0 : ℕ) = 2 at hrel
  omega

/-- Its local point 2 is outside the whole shared point class, not merely
outside the literal shared node label. -/
theorem private_off_core (i : Bool) :
    data.sourcePoint i true true ∉ data.coreImage := by
  rw [data.sourcePoint_mem_coreImage_iff]
  rintro ⟨q, c, hc⟩
  cases c
  · change (0 : ℕ) = 2 at hc
    omega
  · change (1 : ℕ) = 2 at hc
    omega

theorem private_sources_separate : data.sourcePoint false true true ≠
    data.sourcePoint true true true := by
  intro h
  obtain ⟨e, a, he, _⟩ :=
    (data.distinct_sourcePoint_eq_iff_core false true (by decide) true true true true).mp h
  exact private_off_core false ⟨e, a, he.symm⟩

/-- Distinct raw node labels can represent the same shared physical edge. -/
theorem shared_raw_nodes_distinct :
    (Sum.inl false : Data.Node (CoreNode := Bool) (SourceNode := fun _ : Bool => Bool)) ≠
      .inr ⟨false, false⟩ := by
  intro h
  cases h

theorem shared_raw_carriers_equal :
    data.output.carrier (.inl false) = data.output.carrier (.inr ⟨false, false⟩) := by
  change Set.range (data.output.nodePoint (.inl false)) =
    Set.range (data.output.nodePoint (.inr ⟨false, false⟩))
  congr 1
  funext a
  apply data.output.nodePoint_eq_iff.mpr
  exact (data.sharedPoint_eq false () a).symm

/-- Even linear source diagrams do not make the unquotiented raw-node output
linear: its distinct shared labels overlap in both coordinates. -/
theorem raw_output_not_linear : ¬ data.output.Linear := by
  intro h
  exact shared_raw_nodes_distinct
    (data.output.carrier_injective_of_linear h shared_raw_carriers_equal)

theorem source_diagrams_linear (i : Bool) : (data.source i).Linear := by
  intro e f hef a ha b hb
  obtain ⟨c, hc⟩ := ha
  obtain ⟨d, hd⟩ := hb
  cases e <;> cases f <;> cases a <;> cases b <;> cases c <;> cases d <;>
    simp_all [data, chain, CoherentOverlap.ofCharts, chart]

end ACopyPointStarRegression

namespace ACopyPointStarFullDomainRegression

/-- The missing edge xy and the two declared shared edges xu and vy. -/
inductive Edge
  | xy | xu | vy
  deriving DecidableEq

def chart (e : Edge) : Bool ↪ Bool × Bool where
  toFun a := (match e with
    | .xy => false
    | .xu => a
    | .vy => !a, a)
  inj' := by
    intro a b h
    exact congrArg (fun p : Bool × Bool => p.2) h

def diagram : CoherentOverlap Edge Bool := CoherentOverlap.ofCharts chart

def sharedNode : Bool ↪ Edge where
  toFun b := if b then .vy else .xu
  inj' := by
    intro a b h
    cases a <;> cases b <;> simp_all

def sharedDiagram : CoherentOverlap Bool Bool :=
  CoherentOverlap.ofCharts (fun q => chart (sharedNode q))

def data : Data Edge Unit (fun _ => Edge) (fun _ => Bool) Bool where
  core := diagram
  source _ := diagram
  shared _ := sharedDiagram
  toCore _ := ⟨sharedNode, fun _ _ _ _ => Iff.rfl⟩
  toSource _ := ⟨sharedNode, fun _ _ _ _ => Iff.rfl⟩

theorem diagrams_linear : diagram.Linear := by
  intro e f hef a ha b hb
  obtain ⟨c, hc⟩ := ha
  obtain ⟨d, hd⟩ := hb
  cases e <;> cases f <;> cases a <;> cases b <;> cases c <;> cases d <;>
    simp_all [diagram, CoherentOverlap.ofCharts, chart]
  all_goals cases hc
  all_goals cases hd

/-- Both endpoints of xy glue, although xy is not a declared shared node. -/
theorem missing_edge_coordinates_glue (a : Bool) :
    data.sourcePoint () .xy a = data.corePoint .xy a := by
  apply (data.sourcePoint_eq_corePoint_iff () .xy .xy a a).mpr
  cases a
  · exact ⟨false, false, rfl, rfl⟩
  · exact ⟨true, true, rfl, rfl⟩

theorem missing_edge_carriers_equal :
    data.output.carrier (.inl .xy) = data.output.carrier (.inr ⟨(), .xy⟩) := by
  change Set.range (data.output.nodePoint (.inl .xy)) =
    Set.range (data.output.nodePoint (.inr ⟨(), .xy⟩))
  congr 1
  funext a
  apply data.output.nodePoint_eq_iff.mpr
  exact (missing_edge_coordinates_glue a).symm

def nodeEq : Setoid Edge where
  r := Eq
  iseqv := ⟨fun _ => rfl, fun h => h.symm, fun h₁ h₂ => h₁.trans h₂⟩

def coreNode (i : Unit) : Bool → Edge := fun q => (data.toCore i).node q
def sourceNode (i : Unit) : Bool → Edge := fun q => (data.toSource i).node q

/-- The literal shared-node pushout still distinguishes the unshared xy
labels. Equal point carriers do not justify identifying these labels. -/
theorem missing_edge_nodes_separate :
    ¬ ACopyExactStar.SourceStar.Generated nodeEq (fun _ : Unit => nodeEq)
      coreNode sourceNode (.inr ⟨(), .xy⟩) (.inl .xy) := by
  intro h
  have compatible : ∀ i s t,
      nodeEq (coreNode i s) (coreNode i t) ↔
        nodeEq (sourceNode i s) (sourceNode i t) := fun _ _ _ => Iff.rfl
  obtain ⟨q, hq, _⟩ :=
    (ACopyExactStar.SourceStar.generated_source_core_iff nodeEq
      (fun _ : Unit => nodeEq) coreNode sourceNode compatible () .xy .xy).mp h
  cases q <;> cases hq

end ACopyPointStarFullDomainRegression

#print axioms StructuralRamsey.Girth.ACopyPointStar.Data.coreOccurrence_injective
#print axioms StructuralRamsey.Girth.ACopyPointStar.Data.sourceOccurrence_injective
#print axioms StructuralRamsey.Girth.ACopyPointStar.Data.occurrence_compatible
#print axioms StructuralRamsey.Girth.ACopyPointStar.Data.coreMap_injective
#print axioms StructuralRamsey.Girth.ACopyPointStar.Data.sourceMap_injective
#print axioms StructuralRamsey.Girth.ACopyPointStar.Data.corePoint_eq_iff
#print axioms StructuralRamsey.Girth.ACopyPointStar.Data.sourcePoint_eq_iff
#print axioms StructuralRamsey.Girth.ACopyPointStar.Data.sourcePoint_eq_corePoint_iff
#print axioms StructuralRamsey.Girth.ACopyPointStar.Data.sharedPoint_eq
#print axioms StructuralRamsey.Girth.ACopyPointStar.Data.distinct_sourcePoint_eq_iff_core
#print axioms StructuralRamsey.Girth.ACopyPointStar.Data.distinct_sourcePoint_eq_iff
#print axioms StructuralRamsey.Girth.ACopyPointStar.Data.coreImage_eq_range_coreMap
#print axioms StructuralRamsey.Girth.ACopyPointStar.Data.sourceImage_eq_range_sourceMap
#print axioms StructuralRamsey.Girth.ACopyPointStar.Data.sourcePoint_mem_coreImage_iff
#print axioms StructuralRamsey.Girth.ACopyPointStar.Data.sourceImage_inter_coreImage
#print axioms StructuralRamsey.Girth.ACopyPointStar.Data.distinct_sourceImage_inter
#print axioms StructuralRamsey.Girth.ACopyPointStar.Data.point_covered
#print axioms StructuralRamsey.Girth.ACopyPointStar.Data.nodePoint_injective
#print axioms StructuralRamsey.Girth.ACopyPointStar.Data.output
#print axioms StructuralRamsey.Girth.ACopyPointStar.Data.output_rel_core_iff
#print axioms StructuralRamsey.Girth.ACopyPointStar.Data.output_rel_source_iff
#print axioms StructuralRamsey.Girth.ACopyPointStar.Data.nodePoint_covered
#print axioms StructuralRamsey.Girth.ACopyPointStar.Data.outputPointEquiv
#print axioms StructuralRamsey.Girth.ACopyPointStar.Data.outputPointEquiv_nodePoint
#print axioms ACopyPointStarRegression.transitive_cross_coordinate
#print axioms ACopyPointStarRegression.transitive_generated
#print axioms ACopyPointStarRegression.no_core_fold
#print axioms ACopyPointStarRegression.no_source_fold
#print axioms ACopyPointStarRegression.private_off_core
#print axioms ACopyPointStarRegression.private_sources_separate
#print axioms ACopyPointStarRegression.shared_raw_nodes_distinct
#print axioms ACopyPointStarRegression.shared_raw_carriers_equal
#print axioms ACopyPointStarRegression.raw_output_not_linear
#print axioms ACopyPointStarRegression.source_diagrams_linear
#print axioms ACopyPointStarFullDomainRegression.diagrams_linear
#print axioms ACopyPointStarFullDomainRegression.missing_edge_coordinates_glue
#print axioms ACopyPointStarFullDomainRegression.missing_edge_carriers_equal
#print axioms ACopyPointStarFullDomainRegression.missing_edge_nodes_separate
